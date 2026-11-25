-- Prove2me | solution 1 for SVD.isClosed_isApproximable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T03:18:47.256801+00:00
-- url     : https://prove2.me/submissions/519baaf9-a8cf-4bcd-bb70-63fc1ef56617

module
public import Definitions.Def_SNumbers_Approximation
public import Mathlib.Analysis.Normed.Operator.Compact.Basic
public import Definitions.Def_AddOns_Approximable
public import Theorems.Thm_SNumbers_approximationNumber_add_le
public import Theorems.Thm_SNumbers_approximationNumber_nonneg


set_option autoImplicit true
@[expose] public section
public section
universe u
open scoped Cardinal
open Filter Topology
open SVD
variable {𝕜 : Type u} [NontriviallyNormedField 𝕜]
variable {W X Y Z : Type u}
variable [NormedAddCommGroup W] [NormedSpace 𝕜 W]
variable [NormedAddCommGroup X] [NormedSpace 𝕜 X]
variable [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
variable [NormedAddCommGroup Z] [NormedSpace 𝕜 Z]
namespace SVD
theorem _root_.solution :
    IsClosed { S : X →L[𝕜] Y | IsApproximable S } := by
  rw [← closure_subset_iff_isClosed]
  intro S hS_in_closure
  rw [Metric.mem_closure_iff] at hS_in_closure
  show IsApproximable S
  unfold IsApproximable
  rw [Metric.tendsto_atTop]
  intro ε hε
  -- Step 1: pick approximable `T` with `‖S - T‖ < ε/2`.
  obtain ⟨T, hT_approx, hT_dist⟩ := hS_in_closure (ε / 2) (by linarith)
  have h_dist_norm : ‖S - T‖ < ε / 2 := by
    rw [dist_eq_norm] at hT_dist; exact hT_dist
  -- Step 2: pick `N` such that `aₙ(T) < ε/2` for all `n ≥ N`.
  have hT_approx' : Tendsto (SNumbers.approximationNumber T) atTop (𝓝 0) :=
    hT_approx
  rw [Metric.tendsto_atTop] at hT_approx'
  obtain ⟨N, hN⟩ := hT_approx' (ε / 2) (by linarith)
  refine ⟨N, fun n hn => ?_⟩
  -- Step 3: combine via (S2): `aₙ(S) ≤ aₙ(T) + ‖S - T‖`.
  have h_eq : S = T + (S - T) := by abel
  have h_bd : SNumbers.approximationNumber S n ≤
                SNumbers.approximationNumber T n + ‖S - T‖ := by
    nth_rewrite 1 [h_eq]
    exact SNumbers.approximationNumber_add_le _ _ n
  have h_aT : SNumbers.approximationNumber T n < ε / 2 := by
    have h := hN n hn
    rwa [Real.dist_0_eq_abs,
         abs_of_nonneg (SNumbers.approximationNumber_nonneg _ _)] at h
  rw [Real.dist_0_eq_abs,
      abs_of_nonneg (SNumbers.approximationNumber_nonneg _ _)]
  linarith
end SVD
