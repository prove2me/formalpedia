-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.LCG.determinant_index_formula
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T11:10:48.777772+00:00
-- url     : https://prove2.me/submissions/d0846379-b7bc-4bfe-a482-ab63f8392d43

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeCountingBound_IndexDefs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeCountingBound_IndexDet
import Theorems.Thm_PI_UnitaryGroupMassFormula_LCG_DetIdxW_vm_apply
import Theorems.Thm_PI_UnitaryGroupMassFormula_LCG_DetIdxW_idx_int
import Theorems.Thm_PI_UnitaryGroupMassFormula_LCG_DetIdxW_natAbs_norm_real
import Theorems.Thm_PI_UnitaryGroupMassFormula_LCG_DetIdxW_vecMul_inj
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
noncomputable section
open NumberField Matrix
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.LCG
open DetIdxW
namespace PI.UnitaryGroupMassFormula.LCG
theorem _root_.solution : DetIdx := by
  intro K _ _ k N Q D hOQ hOQ0 hDO hDO0 hDQ
  classical
  by_cases hN : N.det = 0
  · rw [hN, Algebra.norm_zero, Rat.cast_zero, abs_zero]
    positivity
  set O := (oLat K k).toAddSubgroup with hOdef

  obtain ⟨⟨d, hd⟩, hdT⟩ := IsLocalization.exist_integer_multiples_of_finset (nonZeroDivisors (𝓞 K))
    (Finset.univ.image fun p : Fin k × Fin k => N p.1 p.2)
  have hd0 : d ≠ 0 := nonZeroDivisors.ne_zero hd
  set dK := algebraMap (𝓞 K) K d with hdKdef
  have hdK : dK ≠ 0 := by
    rw [hdKdef, Ne, ← map_zero (algebraMap (𝓞 K) K)]
    exact fun h => hd0 (IsFractionRing.injective (𝓞 K) K h)
  have hG : ∀ i j, ∃ x : 𝓞 K, algebraMap (𝓞 K) K x = dK * N i j := by
    intro i j
    obtain ⟨x, hx⟩ := hdT (N i j) (Finset.mem_image.2 ⟨(i, j), Finset.mem_univ _, rfl⟩)
    exact ⟨x, by rw [hx, Algebra.smul_def]⟩
  choose G hGe using hG
  let Gm : Matrix (Fin k) (Fin k) (𝓞 K) := Matrix.of G
  have hGmap : Gm.map (algebraMap (𝓞 K) K) = dK • N := by
    ext i j
    simp [Gm, hGe]
  have hdetG : algebraMap (𝓞 K) K Gm.det = dK ^ k * N.det := by
    rw [RingHom.map_det, RingHom.mapMatrix_apply, hGmap, Matrix.det_smul, Fintype.card_fin]
  have hGdet0 : Gm.det ≠ 0 := by
    intro h
    have h2 := hdetG
    rw [h, map_zero] at h2
    exact (mul_ne_zero (pow_ne_zero _ hdK) hN) h2.symm
  let Dm : Matrix (Fin k) (Fin k) (𝓞 K) := d • (1 : Matrix (Fin k) (Fin k) (𝓞 K))
  have hDmap : Dm.map (algebraMap (𝓞 K) K) = dK • (1 : Matrix (Fin k) (Fin k) K) := by
    ext i j
    by_cases h : i = j <;> simp [Dm, h, hdKdef]
  have hDdet : Dm.det = d ^ k := by simp [Dm]
  have hDdet0 : Dm.det ≠ 0 := by rw [hDdet]; exact pow_ne_zero _ hd0
  set T := vm (Gm.map (algebraMap (𝓞 K) K)) with hTdef
  set S := vm (Dm.map (algebraMap (𝓞 K) K)) with hSdef
  have hT : ∀ s, T s = dK • (s ᵥ* N) := by
    intro s; rw [hTdef, vm_apply, hGmap, Matrix.vecMul_smul]
  have hS : ∀ s, S s = dK • s := by
    intro s; rw [hSdef, vm_apply, hDmap, Matrix.vecMul_smul, Matrix.vecMul_one]
  have hTinj : Function.Injective T := by
    intro s s' h
    rw [hT, hT] at h
    exact vecMul_inj N hN (smul_right_injective _ hdK h)
  have hSinj : Function.Injective S := by
    intro s s' h
    rw [hS, hS] at h
    exact smul_right_injective _ hdK h
  set X := O.map T with hX
  set Y := Q.map T with hY
  set Z := D.map S with hZ
  set dO := O.map S with hdO
  have hXO : X.relIndex O = (Algebra.norm ℤ Gm.det).natAbs := idx_int Gm hGdet0
  have hdOO : dO.relIndex O = (Algebra.norm ℤ Dm.det).natAbs := idx_int Dm hDdet0
  have hXY : X.relIndex Y = O.relIndex Q := AddSubgroup.relIndex_map_map_of_injective _ _ hTinj
  have hZdO : Z.relIndex dO = D.relIndex O := AddSubgroup.relIndex_map_map_of_injective _ _ hSinj
  have hZle_dO : Z ≤ dO := AddSubgroup.map_mono hDO
  have hdO_le : dO ≤ O := by
    rintro _ ⟨s, hs, rfl⟩
    rw [hS]
    have := (oLat K k).smul_mem d hs
    rwa [← algebraMap_smul K d s] at this
  have hZO_le : Z ≤ O := hZle_dO.trans hdO_le
  have hZY : Z ≤ Y := by
    rintro _ ⟨r, hr, rfl⟩
    obtain ⟨s, hs, hsr⟩ := hDQ r hr
    exact ⟨s, hs, by rw [hT, hS, hsr]⟩
  have hZO : Z.relIndex O = D.relIndex O * (Algebra.norm ℤ Dm.det).natAbs := by
    rw [← AddSubgroup.relIndex_mul_relIndex (hHK := hZle_dO) (hKL := hdO_le), hZdO, hdOO]
  have hXY0 : X.relIndex Y ≠ 0 := hXY ▸ hOQ0
  have hXZ0 : X.relIndex Z ≠ 0 := mt (AddSubgroup.relIndex_eq_zero_of_le_right (hKL := hZY)) hXY0
  have hZO0 : Z.relIndex O ≠ 0 := by
    rw [hZO]
    exact mul_ne_zero hDO0 (Int.natAbs_ne_zero.mpr (Algebra.norm_ne_zero_iff.mpr hDdet0))
  have hmul : (X ⊓ Z).relIndex O = X.relIndex Z * Z.relIndex O := by
    rw [← AddSubgroup.relIndex_mul_relIndex (hHK := (inf_le_right : X ⊓ Z ≤ Z)) (hKL := hZO_le),
      AddSubgroup.inf_relIndex_right]
  have h1 : X.relIndex O ≤ (X ⊓ Z).relIndex O :=
    AddSubgroup.relIndex_le_of_le_left (hHK := (inf_le_left : X ⊓ Z ≤ X)) (hHL := by rw [hmul]; exact mul_ne_zero hXZ0 hZO0)
  have h2 : X.relIndex Z ≤ X.relIndex Y := AddSubgroup.relIndex_le_of_le_right (hKL := hZY) (hHL := hXY0)
  have key : X.relIndex O ≤ X.relIndex Y * Z.relIndex O := by
    rw [hmul] at h1
    exact h1.trans (Nat.mul_le_mul_right _ h2)
  rw [hXO, hXY, hZO] at key
  have keyR : ((Algebra.norm ℤ Gm.det).natAbs : ℝ) ≤
      (O.relIndex Q : ℝ) * ((D.relIndex O : ℝ) * ((Algebra.norm ℤ Dm.det).natAbs : ℝ)) := by
    exact_mod_cast key
  rw [natAbs_norm_real, natAbs_norm_real, hdetG, hDdet, map_pow, map_mul, map_pow] at keyR
  simp only [Rat.cast_mul, Rat.cast_pow, abs_mul, abs_pow] at keyR
  have ha : 0 < |((Algebra.norm ℚ dK : ℚ) : ℝ)| ^ k := by
    apply pow_pos
    rw [abs_pos, Rat.cast_ne_zero]
    exact Algebra.norm_ne_zero_iff.mpr hdK
  have : |((Algebra.norm ℚ dK : ℚ) : ℝ)| ^ k * |((Algebra.norm ℚ N.det : ℚ) : ℝ)| ≤
      |((Algebra.norm ℚ dK : ℚ) : ℝ)| ^ k * ((O.relIndex Q : ℝ) * (D.relIndex O : ℝ)) := by
    calc _ ≤ _ := keyR
      _ = _ := by ring
  exact le_of_mul_le_mul_left this ha
end PI.UnitaryGroupMassFormula.LCG
