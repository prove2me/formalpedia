-- Prove2me | solution 1 for ReciprocityTheory.ReducedBases.T2.gs_TB
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T15:48:49.213608+00:00
-- url     : https://prove2.me/submissions/5c206f04-84b8-41e8-a88c-098d00f72071

import Definitions.Def_ReciprocityTheory_ReducedBases_GsInnerBOfLt
import Definitions.Def_ReciprocityTheory_ReducedBases_LatDefs
import Definitions.Def_ReciprocityTheory_ReducedBases_TBInjective
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
namespace ReciprocityTheory.ReducedBases.T2
open Finset InnerProductSpace Matrix
variable {d : ℕ}
private lemma sub_gs_mem_span_Iio {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (f : Fin d → E) (j : Fin d) :
    f j - gs f j ∈ Submodule.span ℝ (f '' Set.Iio j) := by
  rw [← span_gramSchmidt_Iio ℝ f j]
  rw [sub_eq_iff_eq_add'.2 (gramSchmidt_def'' ℝ f j)]
  exact Submodule.sum_mem _ fun i hi =>
    Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, by simpa using hi, rfl⟩)
private lemma norm_gs_sq_le_norm_sq {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (f : Fin d → E) (j : Fin d) (w : E) (hw : w ∈ Submodule.span ℝ (f '' Set.Iio j)) :
    ‖gs f j‖ ≤ ‖f j - w‖ := by
  have hz : f j - gs f j - w ∈ Submodule.span ℝ (f '' Set.Iio j) :=
    Submodule.sub_mem _ (sub_gs_mem_span_Iio f j) hw
  rw [← span_gramSchmidt_Iio ℝ f j] at hz
  have hle : Submodule.span ℝ (gramSchmidt ℝ f '' Set.Iio j) ≤ (ℝ ∙ gs f j)ᗮ := by
    rw [Submodule.span_le]
    rintro _ ⟨i, hi, rfl⟩
    rw [SetLike.mem_coe, Submodule.mem_orthogonal_singleton_iff_inner_right]
    exact gramSchmidt_orthogonal ℝ f (ne_of_gt (Set.mem_Iio.1 hi))
  have horth : ⟪gs f j, f j - gs f j - w⟫_ℝ = 0 :=
    Submodule.mem_orthogonal_singleton_iff_inner_right.1 (hle hz)
  have hsplit : f j - w = gs f j + (f j - gs f j - w) := by abel
  have h2 : ‖f j - w‖ ^ 2 = ‖gs f j‖ ^ 2 + ‖f j - gs f j - w‖ ^ 2 := by
    rw [hsplit, norm_add_sq_real, horth]; ring
  nlinarith [norm_nonneg (gs f j), norm_nonneg (f j - w), sq_nonneg ‖f j - gs f j - w‖]
end ReciprocityTheory.ReducedBases.T2
end
end

set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ReducedBases ReciprocityTheory.ReducedBases.T2
open Finset InnerProductSpace Matrix
variable {d : ℕ}
namespace ReciprocityTheory.ReducedBases.T2
theorem _root_.solution (B : Matrix (Fin d) (Fin d) ℝ) {K : ℝ} (hK : ∀ v, ‖v‖ ≤ K * ‖TB B v‖)
    (U : Fin d → EuclideanSpace ℝ (Fin d)) (j : Fin d) :
    ‖gs U j‖ ≤ K * ‖gs (fun i => TB B (U i)) j‖ := by
  have hp := sub_gs_mem_span_Iio (fun i => TB B (U i)) j
  have himg : (fun i => TB B (U i)) '' Set.Iio j = (TB B) '' (U '' Set.Iio j) := by
    rw [Set.image_image]
  rw [himg, Submodule.span_image] at hp
  obtain ⟨w, hw, hTw⟩ := Submodule.mem_map.1 hp
  have hgs : gs (fun i => TB B (U i)) j = TB B (U j - w) := by
    rw [map_sub, hTw]; abel
  calc ‖gs U j‖ ≤ ‖U j - w‖ := norm_gs_sq_le_norm_sq U j w hw
    _ ≤ K * ‖TB B (U j - w)‖ := hK _
    _ = K * ‖gs (fun i => TB B (U i)) j‖ := by rw [hgs]
end ReciprocityTheory.ReducedBases.T2
