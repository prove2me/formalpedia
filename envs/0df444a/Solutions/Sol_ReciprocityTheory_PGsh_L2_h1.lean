-- Prove2me | solution 1 for ReciprocityTheory.PGsh.L2.h1
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T16:23:23.366998+00:00
-- url     : https://prove2.me/submissions/1bfcded0-3737-4f2a-9616-275389b45898

import Definitions.Def_ReciprocityTheory_DualLattices_DualHopfOrderStatement
import Definitions.Def_ReciprocityTheory_DualLattices_MemDualLatMapFourier
import Definitions.Def_ReciprocityTheory_DualLattices_ImportsAlt
import Theorems.Thm_P2M_ReciprocityTheory_PGsh_L2_fourier__surjective_1bda25901bf1
import Theorems.Thm_ReciprocityTheory_PGsh_L2_antipode_fourier
import Theorems.Thm_ReciprocityTheory_PGsh_L2_comul_fourier
import Theorems.Thm_ReciprocityTheory_PGsh_L2_conv_mem_dualLat
import Theorems.Thm_ReciprocityTheory_PGsh_L2_dualLat_dualLat_spanCols
import Theorems.Thm_ReciprocityTheory_PGsh_L2_dualLat_spanCols
import Theorems.Thm_ReciprocityTheory_PGsh_L2_fourier_conv
import Theorems.Thm_ReciprocityTheory_PGsh_L2_fourier_single
import Theorems.Thm_ReciprocityTheory_PGsh_L2_map_fourier_spanCols
import Theorems.Thm_ReciprocityTheory_PGsh_L2_mem_dualLat_map_fourier
import Theorems.Thm_ReciprocityTheory_PGsh_L2_single_mem_dualLat
import Theorems.Thm_ReciprocityTheory_PGsh_L2_tableM_isUnit
import Theorems.Thm_ReciprocityTheory_PGsh_L2_valuation_det_eq_of_span_eq
import Theorems.Thm_ReciprocityTheory_PGsh_L2_valuation_fourier_le_one
import Theorems.Thm_ReciprocityTheory_PGsh_charTable


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open ReciprocityTheory ReciprocityTheory.PGsh ReciprocityTheory.PGsh.L2
namespace ReciprocityTheory.PGsh.L2
theorem _root_.solution (C R : Type) [Field C] [CommRing R] [Algebra R C] :
    DualHopfOrderStatement (C := C) (R := R) := by
  intro v hv N H _ _ _ _ _ _ e he hcard AA
  obtain ⟨B, hB, hAA⟩ := AA.lat
  have σ : H ≃ N := Fintype.equivOfCardEq hcard
  obtain ⟨M, hMdef⟩ : ∃ M : Matrix H H C,
      M = ((tableM e σ)ᵀ * (B⁻¹)ᵀ).submatrix σ σ := ⟨_, rfl⟩
  have hdual : dualLat AA.carrier = Submodule.span R (Set.range fun j x => (B⁻¹)ᵀ x j) := by
    rw [hAA]; exact dualLat_spanCols B hB
  have hmap : (dualLat AA.carrier).map (fourier (R := R) fun h a => e h a) =
      Submodule.span R (Set.range fun k h => M h k) := by
    rw [hdual, hMdef]; exact map_fourier_spanCols e σ _
  have hBB : B.det * B⁻¹.det = 1 := by
    rw [← Matrix.det_mul, Matrix.mul_nonsing_inv B hB, Matrix.det_one]
  have hBinv : IsUnit B⁻¹.det := ⟨⟨B⁻¹.det, B.det, by rw [mul_comm]; exact hBB, hBB⟩, rfl⟩
  have hdetM : M.det = (tableM e σ).det * B⁻¹.det := by
    rw [hMdef, Matrix.det_submatrix_equiv_self, Matrix.det_mul, Matrix.det_transpose,
      Matrix.det_transpose]
  have hMunit : IsUnit M.det := by
    rw [hdetM]; exact (tableM_isUnit e σ).mul hBinv
  have hdd : dualLat (dualLat AA.carrier) = AA.carrier := by
    rw [hAA]; exact dualLat_dualLat_spanCols B hB
  refine ⟨{ carrier := (dualLat AA.carrier).map (fourier (R := R) fun h a => e h a)
            lat := ⟨M, hMunit, hmap⟩
            le_int := by
              rintro w ⟨u, hu, rfl⟩ h
              exact hv.exists_of_le_one (valuation_fourier_le_one v hv (fun h => e h) AA hu h)
            one_mem := Submodule.mem_map.mpr ⟨(Pi.single 0 1 : N → C),
              single_mem_dualLat AA,
              funext fun h => fourier_single (R := R) (fun h => e h) h⟩
            mul_mem := by
              rintro f g ⟨u, hu, rfl⟩ ⟨w, hw, rfl⟩
              exact Submodule.mem_map.mpr ⟨conv u w,
                conv_mem_dualLat AA hu hw,
                funext fun h => fourier_conv (R := R) (fun h => e h) u w h⟩
            comul := by
              rintro f ⟨u, hu, rfl⟩
              exact comul_fourier e he AA B hB hAA u hu
            antipode := by
              rintro f ⟨u, hu, rfl⟩
              exact antipode_fourier e he AA u hu }, rfl, ?_, ?_⟩
  · ext f
    rw [Submodule.mem_map]
    constructor
    · rintro ⟨w, hw, rfl⟩
      have solution := (mem_dualLat_map_fourier e (dualLat AA.carrier) w).mp hw
      rwa [hdd] at solution
    · intro hf
      obtain ⟨w, hw⟩ := fourier'_surjective (R := R) e σ f
      refine ⟨w, (mem_dualLat_map_fourier e (dualLat AA.carrier) w).mpr ?_, hw⟩
      rw [hw, hdd]; exact hf
  · intro c c' hc hc'
    obtain ⟨B₀, hB₀, rfl⟩ := hc
    obtain ⟨B₁, hB₁, rfl⟩ := hc'
    have e0 : v B₀.det = v B.det :=
      valuation_det_eq_of_span_eq v hv B₀ B (hB₀.symm.trans hAA)
    have e1 : v B₁.det = v M.det :=
      valuation_det_eq_of_span_eq v hv B₁ M (hB₁.symm.trans hmap)
    have key : v B.det * v M.det = v (tableM e σ).det := by
      rw [← map_mul, hdetM, mul_left_comm, hBB, mul_one]
    have h2 : (tableM e σ).det ^ 2 = (Fintype.card N : C) ^ Fintype.card N ∨
        (tableM e σ).det ^ 2 = -(Fintype.card N : C) ^ Fintype.card N :=
      ReciprocityTheory.PGsh.charTable C N (σ.symm.trans e)
    rw [e0, e1, key]
    calc v (tableM e σ).det ^ 2 = v ((tableM e σ).det ^ 2) :=
          (map_pow v _ 2).symm
      _ = v (Fintype.card N : C) ^ Fintype.card N := by
        rcases h2 with h | h <;> rw [h] <;> simp [Valuation.map_neg, map_pow]
end ReciprocityTheory.PGsh.L2
