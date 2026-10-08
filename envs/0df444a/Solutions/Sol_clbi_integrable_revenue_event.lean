-- Prove2me | solution 1 for clbi_integrable_revenue_event
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-08T09:03:49.26054+00:00
-- url     : https://prove2.me/submissions/3127f83e-ef95-4553-b23a-69831c2f9a5b

import Mathlib
import Definitions.Def_NestedSeatAlloc_IntPolicy_Model
import Theorems.Thm_NestedSeatAlloc_IntPolicy_revenue_succ_eq_atom_tail_pointwise
import Theorems.Thm_NestedSeatAlloc_IntPolicy_integral_expRevenue_mul_next_event_indicator
import Theorems.Thm_revenue_joint_measurable
import Theorems.Thm_revenue_abs_bound

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory NestedSeatAlloc.IntPolicy

theorem solution
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : ℕ → Ω → ℝ) (f q : ℕ → ℝ) (hM : IsSeatModel P X f)
    (k : ℕ) (t : ℝ) (ht : 0 ≤ t) (hq : ∀ i, 0 ≤ q i)
    (E : Set ℝ) (hE : MeasurableSet E)
    [DecidablePred (fun ω => X (k + 1) ω ∈ E)] :
    Integrable (fun ω => revenue f q (fun i => X i ω) k t *
      (if X (k + 1) ω ∈ E then (1 : ℝ) else 0)) P := by
  classical
  letI : IsProbabilityMeasure P := hM.isProb
  have hX : Measurable (fun ω i => X i ω) :=
    measurable_pi_iff.mpr (fun i => hM.meas i)
  have hRev : Measurable (fun ω => revenue f q (fun i => X i ω) k t) :=
    (revenue_joint_measurable f q k).comp
      (Measurable.prodMk hX measurable_const)
  let I : Ω → ℝ := fun ω => if X (k + 1) ω ∈ E then 1 else 0
  have hI : Measurable I := by
    have hEq : I = (X (k + 1) ⁻¹' E).indicator (fun _ => (1 : ℝ)) := by
      funext ω
      by_cases hω : X (k + 1) ω ∈ E <;> simp [I, Set.indicator_apply, hω]
    rw [hEq]
    exact measurable_const.indicator (hM.meas (k + 1) hE)
  have hProd : Measurable (fun ω =>
      revenue f q (fun i => X i ω) k t * I ω) := hRev.mul hI
  let S : Finset ℕ := Finset.Icc 1 k
  let M : ℝ := ∑ j ∈ S, |f j|
  have hM0 : 0 ≤ M := by
    simp only [M]
    exact Finset.sum_nonneg fun j hj => abs_nonneg (f j)
  have hFare : ∀ j, 1 ≤ j → j ≤ k → |f j| ≤ M := by
    intro j hj hk
    apply Finset.single_le_sum (fun i hi => abs_nonneg (f i))
    simp [S, Finset.mem_Icc, hj, hk]
  let C : ℝ := (k : ℝ) * M * t
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hBound : ∀ ω, |revenue f q (fun i => X i ω) k t * I ω| ≤ C := by
    intro ω
    have hb := revenue_abs_bound f q (fun i => X i ω) M hM0
      (fun j _ => hq j) (fun i => hM.nonneg i ω) k t ht hFare
    by_cases hω : X (k + 1) ω ∈ E
    · simpa [I, C, hω] using hb
    · simp [I, C, hω]
      positivity
  have hdom : ∀ᵐ ω ∂P,
      ‖revenue f q (fun i => X i ω) k t * I ω‖ ≤ C := by
    filter_upwards [] with ω
    simpa [Real.norm_eq_abs, abs_of_nonneg hC] using hBound ω
  exact (integrable_const C).mono' hProd.aestronglyMeasurable hdom
