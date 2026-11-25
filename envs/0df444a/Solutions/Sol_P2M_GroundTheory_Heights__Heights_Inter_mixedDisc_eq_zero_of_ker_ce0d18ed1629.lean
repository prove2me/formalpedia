-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_mixedDisc_eq_zero_of_ker_ce0d18ed1629
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T05:20:46.053258+00:00
-- url     : https://prove2.me/submissions/da9fb2ee-ec3e-4fbb-866c-d2f0df75bf10

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_IsSemipositiveOn
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PFIntZeroMixed
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_mixedDisc_eq_zero_of_cols_6dbf82d8b420
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_mixedDisc_mul_right_35066f68a6cf

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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open Matrix Module ReciprocityTheory.ChartRestriction.G.Geo
variable {D : ℕ}
namespace GroundTheory.Heights₂.Heights.Inter
theorem _root_.solution (A : Fin D → Matrix (Fin D) (Fin D) ℂ) (V : Submodule ℂ (Fin D → ℂ))
    (S : Finset (Fin D)) (hdim : D < Module.finrank ℂ V + S.card) (hA : ∀ k ∈ S, ∀ x ∈ V, A k *ᵥ x = 0) :
    mixedDisc A = 0 := by
  classical
  obtain ⟨U, hU⟩ := Submodule.exists_isCompl V
  set b0 := ((Module.finBasis ℂ V).prod (Module.finBasis ℂ U)).map (Submodule.prodEquivOfIsCompl V U hU) with hb0
  have hcardι : Fintype.card (Fin (Module.finrank ℂ V) ⊕ Fin (Module.finrank ℂ U)) = D := by
    rw [← Module.finrank_eq_card_basis b0, Module.finrank_fin_fun]
  set e := Fintype.equivFinOfCardEq hcardι
  set b := b0.reindex e
  have hbV : ∀ i, b (e (Sum.inl i)) ∈ V := by
    intro i
    simp [b, hb0, Basis.reindex_apply, Basis.map_apply, Basis.prod_apply]
  set P : Matrix (Fin D) (Fin D) ℂ := (Pi.basisFun ℂ (Fin D)).toMatrix b
  have hP : IsUnit P.det := by
    rw [← Basis.det_apply]
    exact (Pi.basisFun ℂ (Fin D)).isUnit_det b
  set C := Finset.univ.image fun i => e (Sum.inl i)
  have hC : C.card = Module.finrank ℂ V := by
    rw [Finset.card_image_of_injective (f := fun i => e (Sum.inl i)) _
      (fun x y h => Sum.inl_injective (e.injective h)), Finset.card_univ, Fintype.card_fin]
  have hcol : ∀ k ∈ S, ∀ j ∈ C, ∀ i, (A k * P) i j = 0 := by
    intro k hk j hj i
    obtain ⟨l, -, rfl⟩ := Finset.mem_image.mp hj
    have h := congrFun (hA k hk _ (hbV l)) i
    simpa [P, Matrix.mul_apply, Matrix.mulVec, dotProduct, Basis.toMatrix_apply] using h
  have h := mixedDisc_eq_zero_of_cols (fun k => A k * P) S C (by rw [hC]; exact hdim) hcol
  rw [mixedDisc_mul_right] at h
  exact (mul_eq_zero.mp h).resolve_right hP.ne_zero
end GroundTheory.Heights₂.Heights.Inter
