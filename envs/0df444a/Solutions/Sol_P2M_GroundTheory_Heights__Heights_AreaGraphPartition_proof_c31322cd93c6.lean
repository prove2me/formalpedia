-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_AreaGraphPartition_proof_c31322cd93c6
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:32:50.763016+00:00
-- url     : https://prove2.me/submissions/15ec7ad8-df5f-4d39-866a-f2cbc702e8bf

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StAreaGraphPartition
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PAreaGraphPartition

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open scoped ENNReal NNReal
open Set Metric
noncomputable section
namespace GroundTheory.Heights₂.Heights
namespace AreaGraphPartition
theorem _root_.solution : AreaGraphPartition.Statement := by
  intro k m U F hU hF r hr

  have hcont : ContinuousOn (fderiv ℝ F) U := hF.continuousOn_fderiv_of_isOpen hU le_rfl
  have hdiff : ∀ x ∈ U, DifferentiableAt ℝ F x := fun x hx =>
    (hF.differentiableOn one_ne_zero x hx).differentiableAt (hU.mem_nhds hx)

  have hball : ∀ x : U, ∃ ε > 0, ball (x : EuclideanSpace ℝ (Fin k)) ε ⊆ U ∧
      ∀ y ∈ ball (x : EuclideanSpace ℝ (Fin k)) ε, ‖fderiv ℝ F y - fderiv ℝ F x‖ ≤ r (fderiv ℝ F x) := by
    intro x
    have hpos : (0 : ℝ) < r (fderiv ℝ F x) := NNReal.coe_pos.2 (pos_iff_ne_zero.2 (hr _))
    have hca : ContinuousAt (fderiv ℝ F) x := hcont.continuousAt (hU.mem_nhds x.2)
    obtain ⟨δ, δpos, hδ⟩ := Metric.continuousAt_iff.1 hca _ hpos
    obtain ⟨η, ηpos, hη⟩ := Metric.isOpen_iff.1 hU x x.2
    refine ⟨min δ η, lt_min δpos ηpos, (ball_subset_ball (min_le_right _ _)).trans hη, ?_⟩
    intro y hy
    have := hδ (lt_of_lt_of_le (mem_ball.1 hy) (min_le_left _ _))
    rw [dist_eq_norm] at this
    exact this.le
  choose ε εpos hεU hεD using hball

  obtain ⟨T, hTc, hTU⟩ := TopologicalSpace.isOpen_iUnion_countable
    (fun x : U => ball (x : EuclideanSpace ℝ (Fin k)) (ε x)) (fun _ => isOpen_ball)
  have hcover : (⋃ x : U, ball (x : EuclideanSpace ℝ (Fin k)) (ε x)) = U := by
    apply Subset.antisymm
    · exact iUnion_subset fun x => hεU x
    · intro x hx
      exact mem_iUnion.2 ⟨⟨x, hx⟩, mem_ball_self (εpos _)⟩
  rcases U.eq_empty_or_nonempty with hUe | hUne
  ·
    refine ⟨fun _ => ∅, fun _ => 0, fun _ _ _ => disjoint_empty _, fun _ => MeasurableSet.empty,
      fun _ => empty_subset _, by simp [hUe], fun _ => fun x hx => absurd hx (notMem_empty x),
      fun _ x hx => absurd hx (notMem_empty x)⟩
  have hTne : T.Nonempty := by
    by_contra h
    rw [not_nonempty_iff_eq_empty] at h
    obtain ⟨x, hx⟩ := hUne
    have : x ∈ ⋃ i ∈ T, ball ((i : U) : EuclideanSpace ℝ (Fin k)) (ε i) := by rw [hTU, hcover]; exact hx
    simp [h] at this
  obtain ⟨c, hc⟩ := hTc.exists_eq_range hTne
  set B : ℕ → Set (EuclideanSpace ℝ (Fin k)) := fun n => ball ((c n : U) : EuclideanSpace ℝ (Fin k)) (ε (c n)) with hB
  have hBU : ⋃ n, B n = U := by
    rw [← hcover, ← hTU, hc, biUnion_range]
  refine ⟨disjointed B, fun n => fderiv ℝ F (c n), disjoint_disjointed B,
    MeasurableSet.disjointed (fun n => measurableSet_ball), fun n => (disjointed_subset B n).trans
    (hεU (c n)), by rw [iUnion_disjointed, hBU], ?_, ?_⟩
  · intro n x hx y hy
    have hx' := disjointed_subset B n hx
    have hy' := disjointed_subset B n hy
    exact (convex_ball _ _).norm_image_sub_le_of_norm_fderiv_le'
      (fun z hz => hdiff z (hεU (c n) hz)) (fun z hz => hεD (c n) z hz) hy' hx'
  · intro n x hx
    rw [← NNReal.coe_le_coe, coe_nnnorm]
    exact hεD (c n) x (disjointed_subset B n hx)
end AreaGraphPartition
end GroundTheory.Heights₂.Heights
