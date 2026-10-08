-- Prove2me | solution 1 for clbi_integrable_sum_range
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-08T08:32:16.190413+00:00
-- url     : https://prove2.me/submissions/aaf768ae-e542-46ad-9533-b52fb51ade02

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

theorem solution {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (F : ℕ → Ω → ℝ) :
    ∀ n, (∀ i ≤ n, Integrable (F i) P) →
      Integrable (fun ω => ∑ i ∈ Finset.range (n + 1), F i ω) P := by
  intro n hF
  have hfin : ∀ s : Finset ℕ,
      (∀ i ∈ s, Integrable (F i) P) →
        Integrable (fun ω => ∑ i ∈ s, F i ω) P := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
        intro _
        simp
    | @insert a s ha ih =>
        intro hs
        have hsum : (fun ω => ∑ i ∈ insert a s, F i ω) =
            (fun ω => F a ω + ∑ i ∈ s, F i ω) := by
          funext ω
          rw [Finset.sum_insert ha]
        rw [hsum]
        apply Integrable.add
        · exact hs a (Finset.mem_insert_self a s)
        · apply ih
          intro i hi
          exact hs i (Finset.mem_insert_of_mem hi)
  apply hfin
  intro i hi
  exact hF i (by have hi' := Finset.mem_range.mp hi; omega)
