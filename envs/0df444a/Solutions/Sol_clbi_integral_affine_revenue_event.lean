-- Prove2me | solution 1 for clbi_integral_affine_revenue_event
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-08T09:49:08.008606+00:00
-- url     : https://prove2.me/submissions/4af67f01-a068-49b7-b97b-1a76ac0a1ff7

import Mathlib
import Definitions.Def_NestedSeatAlloc_IntPolicy_Model
import Theorems.Thm_NestedSeatAlloc_IntPolicy_revenue_succ_eq_atom_tail_pointwise
import Theorems.Thm_NestedSeatAlloc_IntPolicy_integral_expRevenue_mul_next_event_indicator
import Theorems.Thm_revenue_joint_measurable
import Theorems.Thm_revenue_abs_bound
import Theorems.Thm_clbi_integrable_revenue_event
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory ProbabilityTheory NestedSeatAlloc.IntPolicy
theorem solution
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : ℕ → Ω → ℝ) (f q : ℕ → ℝ) (hM : IsSeatModel P X f)
    (k : ℕ) (t c : ℝ) (ht : 0 ≤ t) (hq : ∀ i, 0 ≤ q i)
    (E : Set ℝ) (hE : MeasurableSet E)
    [DecidablePred (fun ω => X (k + 1) ω ∈ E)] :
    ∫ ω, (c + revenue f q (fun i => X i ω) k t) *
        (if X (k + 1) ω ∈ E then (1 : ℝ) else 0) ∂P =
      (c + expRevenue P X f q k t) * P.real (X (k + 1) ⁻¹' E) := by
  classical
  let I : Ω → ℝ := fun ω => if X (k + 1) ω ∈ E then 1 else 0
  have hI : Integrable (fun ω => c * I ω) P := by
    letI : IsProbabilityMeasure P := hM.isProb
    have hMeas : Measurable I := by
      have hEq : I = (X (k + 1) ⁻¹' E).indicator (fun _ => (1 : ℝ)) := by
        funext ω
        by_cases hω : X (k + 1) ω ∈ E <;> simp [I, Set.indicator_apply, hω]
      rw [hEq]
      exact measurable_const.indicator (hM.meas (k + 1) hE)
    have hdom : ∀ᵐ ω ∂P, ‖c * I ω‖ ≤ |c| := by
      filter_upwards [] with ω
      by_cases hω : X (k + 1) ω ∈ E <;>
        simp [I, hω, Real.norm_eq_abs]
    exact (integrable_const |c|).mono'
      (measurable_const.mul hMeas).aestronglyMeasurable hdom
  have hRev : Integrable (fun ω =>
      revenue f q (fun i => X i ω) k t * I ω) P :=
    clbi_integrable_revenue_event P X f q hM k t ht hq E hE
  have hSplit : (fun ω => (c + revenue f q (fun i => X i ω) k t) * I ω) =
      (fun ω => c * I ω + revenue f q (fun i => X i ω) k t * I ω) := by
    funext ω
    ring
  have hAff : ∫ ω, c * I ω ∂P = c * P.real (X (k + 1) ⁻¹' E) := by
    have hPre : MeasurableSet (X (k + 1) ⁻¹' E) := hM.meas (k + 1) hE
    have hIeq : (fun ω => c * I ω) =
        (X (k + 1) ⁻¹' E).indicator (fun _ => c) := by
      funext ω
      by_cases hω : X (k + 1) ω ∈ E <;>
        simp [I, Set.indicator_apply, hω]
    calc
      ∫ ω, c * I ω ∂P = P.real (X (k + 1) ⁻¹' E) • c := by
        rw [hIeq]
        simpa using (integral_indicator_const (μ := P) (e := c) hPre)
      _ = c * P.real (X (k + 1) ⁻¹' E) := by simp [smul_eq_mul, mul_comm]
  have hFactor :
      ∫ ω, revenue f q (fun i => X i ω) k t * I ω ∂P =
        expRevenue P X f q k t * P.real (X (k + 1) ⁻¹' E) := by
    simpa [I] using
      (integral_expRevenue_mul_next_event_indicator P X f q hM
        k t ht hq E hE)
  calc
    _ = ∫ ω, c * I ω + revenue f q (fun i => X i ω) k t * I ω ∂P := by
      apply integral_congr_ae
      filter_upwards [] with ω
      exact congrFun hSplit ω
    _ = (∫ ω, c * I ω ∂P) +
        ∫ ω, revenue f q (fun i => X i ω) k t * I ω ∂P := integral_add hI hRev
    _ = c * P.real (X (k + 1) ⁻¹' E) +
        expRevenue P X f q k t * P.real (X (k + 1) ⁻¹' E) := by
      rw [hAff, hFactor]
    _ = _ := by ring
