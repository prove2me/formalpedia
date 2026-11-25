-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_FlagMultiHomog_ker_map_le_span_bd4e93bd4fc2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T04:06:00.850144+00:00
-- url     : https://prove2.me/submissions/3327339e-9e5a-40cc-a405-9dbd65ae5ba1

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StFlagMultiHomog
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_IsVerticalDivOfIsVerticalDivisorAlt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_PCurveComplexPoint
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PFlagMultiHomog

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter.FlagMultiHomog
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter.FlagMultiHomog
theorem _root_.solution {F E : Type} [Field F] [Field E] (τ : F →+* E) {t N1 n : ℕ}
    (M : Matrix (Fin t) (Fin N1) F) (B : Matrix (Fin n) (Fin N1) F) (hB : LinearIndependent F B)
    (hK : Submodule.span F (Set.range B) = LinearMap.ker M.mulVecLin) :
    LinearMap.ker (M.map τ).mulVecLin ≤ Submodule.span E (Set.range (B.map τ)) := by
  let _ : Algebra F E := τ.toAlgebra
  have : FaithfulSMul F E := (faithfulSMul_iff_algebraMap_injective F E).2 τ.injective
  have hBE : LinearIndependent E (B.map τ) :=
    (linearIndependent_algebraMap_comp_iff (R := F) (S := E) (v := B)).2 hB
  obtain ⟨κ, a, ha, hsp, hli⟩ := exists_linearIndependent' F M.col
  have : Finite κ := Finite.of_injective a ha
  have : Fintype κ := Fintype.ofFinite κ
  have hliE : LinearIndependent E ((M.map τ).col ∘ a) :=
    (linearIndependent_algebraMap_comp_iff (R := F) (S := E) (v := M.col ∘ a)).2 hli
  have hr : Module.finrank F (LinearMap.range M.mulVecLin) ≤
      Module.finrank E (LinearMap.range (M.map τ).mulVecLin) := by
    rw [Matrix.range_mulVecLin, Matrix.range_mulVecLin, ← hsp, finrank_span_eq_card hli,
      ← finrank_span_eq_card hliE]
    exact Submodule.finrank_mono (Submodule.span_mono (Set.range_comp_subset_range _ _))
  have h1 := LinearMap.finrank_range_add_finrank_ker M.mulVecLin
  have h2 := LinearMap.finrank_range_add_finrank_ker (M.map τ).mulVecLin
  rw [← hK, finrank_span_eq_card hB, Module.finrank_fin_fun] at h1
  rw [Module.finrank_fin_fun] at h2
  have hle : Submodule.span E (Set.range (B.map τ)) ≤ LinearMap.ker (M.map τ).mulVecLin := by
    rw [Submodule.span_le]
    rintro _ ⟨a, rfl⟩
    have h0 : B a ∈ LinearMap.ker M.mulVecLin := hK ▸ Submodule.subset_span ⟨a, rfl⟩
    rw [LinearMap.mem_ker, Matrix.mulVecLin_apply] at h0
    rw [SetLike.mem_coe, LinearMap.mem_ker, Matrix.mulVecLin_apply]
    funext i
    show Matrix.mulVec (M.map τ) (τ ∘ B a) i = 0
    rw [← RingHom.map_mulVec, h0, Pi.zero_apply, map_zero]
  refine (Submodule.eq_of_le_of_finrank_le hle ?_).ge
  rw [finrank_span_eq_card hBE]
  simp only [Fintype.card_fin] at h1 ⊢
  omega
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter.FlagMultiHomog
