-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_mixedDisc_eq_zero_of_cols_6dbf82d8b420
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T04:36:41.937891+00:00
-- url     : https://prove2.me/submissions/60741e45-1839-43a9-abac-fbd7a151c624

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_IsSemipositiveOn
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PFIntZeroMixed
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_sum_neg_one_pow_superset_eq_zero_c9217614b6a4

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
theorem _root_.solution (B : Fin D → Matrix (Fin D) (Fin D) ℂ) (S C : Finset (Fin D))
    (hcard : D < C.card + S.card) (hB : ∀ k ∈ S, ∀ j ∈ C, ∀ i, B k i j = 0) : mixedDisc B = 0 := by
  classical
  unfold mixedDisc
  refine mul_eq_zero_of_right _ ?_
  have hdet : ∀ T : Finset (Fin D), (∑ k ∈ T, B k).det = ∑ σ : Equiv.Perm (Fin D), ∑ f : Fin D → Fin D,
      (if ∀ i, f i ∈ T then (Equiv.Perm.sign σ : ℂ) * ∏ i, B (f i) (σ i) i else 0) := by
    intro T
    rw [Matrix.det_apply]
    refine Finset.sum_congr rfl fun σ _ => ?_
    simp only [Matrix.sum_apply]
    rw [Finset.prod_univ_sum, Units.smul_def, zsmul_eq_mul, Finset.mul_sum]
    have hpi : Fintype.piFinset (fun _ : Fin D => T) = Finset.univ.filter (fun f : Fin D → Fin D => ∀ i, f i ∈ T) := by
      ext f; simp [Fintype.mem_piFinset]
    rw [hpi, Finset.sum_filter]
  simp_rw [hdet, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun σ _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun f _ => ?_
  by_cases hf : Function.Surjective f
  · have hbij : Function.Bijective f := ⟨Finite.injective_iff_surjective.mpr hf, hf⟩
    have hpre : (S.preimage f hbij.1.injOn).card = S.card := by
      rw [Finset.card_preimage]
      congr 1
      exact Finset.filter_true_of_mem fun x _ => hf x
    obtain ⟨i, hi⟩ := Finset.inter_nonempty_of_card_lt_card_add_card (Finset.subset_univ C)
      (Finset.subset_univ (S.preimage f hbij.1.injOn)) (by rw [hpre, Finset.card_univ, Fintype.card_fin]; exact hcard)
    rw [Finset.mem_inter, Finset.mem_preimage] at hi
    have h0 : ∏ i, B (f i) (σ i) i = 0 := Finset.prod_eq_zero (Finset.mem_univ i) (hB _ hi.2 _ hi.1 _)
    refine Finset.sum_eq_zero fun T _ => ?_
    simp [h0]
  · obtain ⟨a, ha⟩ := not_forall.mp hf
    push Not at ha
    have := sum_neg_one_pow_superset_eq_zero (fun T => ∀ i, f i ∈ T) a
      (fun T => ⟨fun h i => (Finset.mem_insert.mp (h i)).resolve_left (ha i), fun h i => Finset.mem_insert_of_mem (h i)⟩)
      ((Equiv.Perm.sign σ : ℂ) * ∏ i, B (f i) (σ i) i)
    exact this
end GroundTheory.Heights₂.Heights.Inter
