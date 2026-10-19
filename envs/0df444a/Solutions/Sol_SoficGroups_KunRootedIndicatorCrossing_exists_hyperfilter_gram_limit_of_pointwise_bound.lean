-- Prove2me | solution 1 for SoficGroups.KunRootedIndicatorCrossing.exists_hyperfilter_gram_limit_of_pointwise_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:56.693907+00:00
-- url     : https://prove2.me/submissions/214ab684-c157-4a57-93c8-493bba7a20d2

import Mathlib
import Definitions.Def_NonSoficGroup

set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.KunRootedIndicatorCrossing
universe u
open Filter
open scoped BigOperators ComplexOrder InnerProductSpace Topology
namespace SoficGroups.KunRootedIndicatorCrossing
theorem _root_.solution
    {I : Type*} {H : ℕ → Type*}
    [∀ n, SeminormedAddCommGroup (H n)]
    [∀ n, InnerProductSpace ℂ (H n)]
    (v : ∀ n, I → H n) (B : I → ℝ)
    (hbound : ∀ n i, ‖v n i‖ ≤ B i) :
    ∃ K : Matrix I I ℂ,
      ∀ i j, Tendsto (fun n => ⟪v n i, v n j⟫_ℂ)
        (Filter.hyperfilter ℕ) (𝓝 (K i j)) := by
  have hinnerbound (n : ℕ) (i j : I) :
      ‖⟪v n i, v n j⟫_ℂ‖ ≤ B i * B j := by
    calc
      ‖⟪v n i, v n j⟫_ℂ‖ ≤ ‖v n i‖ * ‖v n j‖ :=
        norm_inner_le_norm _ _
      _ ≤ B i * B j :=
        mul_le_mul (hbound n i) (hbound n j)
          (norm_nonneg _) ((norm_nonneg _).trans (hbound n i))
  let b : ℕ → (q : I × I) →
      Metric.closedBall (0 : ℂ) (B q.1 * B q.2) :=
    fun n q =>
      ⟨⟪v n q.1, v n q.2⟫_ℂ,
        by simpa [Metric.mem_closedBall, dist_zero_right]
          using hinnerbound n q.1 q.2⟩
  let u := Ultrafilter.map b (Filter.hyperfilter ℕ)
  let L : (q : I × I) →
      Metric.closedBall (0 : ℂ) (B q.1 * B q.2) := u.lim
  let K : Matrix I I ℂ := fun i j => (L (i, j) : ℂ)
  refine ⟨K, ?_⟩
  have hu : Tendsto b (Filter.hyperfilter ℕ) (𝓝 L) := by
    change Filter.map b (↑(Filter.hyperfilter ℕ) : Filter ℕ) ≤
      𝓝 u.lim
    simpa only [u, Ultrafilter.coe_map] using u.le_nhds_lim
  intro i j
  have heval :
      Tendsto
        (fun f : (q : I × I) →
          Metric.closedBall (0 : ℂ) (B q.1 * B q.2) => f (i, j))
        (𝓝 L) (𝓝 (L (i, j))) :=
    (continuous_apply (i, j)).tendsto L
  have hval :
      Tendsto
        (fun z : Metric.closedBall (0 : ℂ) (B i * B j) => (z : ℂ))
        (𝓝 (L (i, j))) (𝓝 (L (i, j) : ℂ)) :=
    continuous_subtype_val.tendsto (L (i, j))
  have hcomp := hval.comp (heval.comp hu)
  change Tendsto (fun n => ⟪v n i, v n j⟫_ℂ)
    (Filter.hyperfilter ℕ) (𝓝 (L (i, j) : ℂ)) at hcomp
  exact hcomp
end SoficGroups.KunRootedIndicatorCrossing
