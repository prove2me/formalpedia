-- Prove2me | solution 1 for clbi_integral_sum_range
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-08T09:19:36.78776+00:00
-- url     : https://prove2.me/submissions/aa30dc82-9deb-4646-8e52-b27f0b79834a

import Mathlib
import Definitions.Def_NestedSeatAlloc_IntPolicy_Model
import Theorems.Thm_NestedSeatAlloc_IntPolicy_revenue_succ_eq_atom_tail_pointwise
import Theorems.Thm_NestedSeatAlloc_IntPolicy_integral_expRevenue_mul_next_event_indicator
import Theorems.Thm_revenue_joint_measurable
import Theorems.Thm_revenue_abs_bound
import Theorems.Thm_clbi_integrable_sum_range
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory ProbabilityTheory NestedSeatAlloc.IntPolicy
theorem solution {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (F : ℕ → Ω → ℝ) :
    ∀ n, (∀ i ≤ n, Integrable (F i) P) →
      ∫ ω, (∑ i ∈ Finset.range (n + 1), F i ω) ∂P =
        ∑ i ∈ Finset.range (n + 1), ∫ ω, F i ω ∂P := by
  intro n
  induction n with
  | zero =>
      intro hF
      simp
  | succ n ih =>
      intro hF
      have hsum (G : ℕ → ℝ) :
          (∑ i ∈ Finset.range ((n + 1) + 1), G i) =
            (∑ i ∈ Finset.range (n + 1), G i) + G (n + 1) := by
        simpa using Finset.sum_range_succ G (n + 1)
      have hpoint (ω : Ω) :
          (∑ i ∈ Finset.range ((n + 1) + 1), F i ω) =
            (∑ i ∈ Finset.range (n + 1), F i ω) + F (n + 1) ω := by
        exact hsum (fun i => F i ω)
      have hfun :
          (fun ω => ∑ i ∈ Finset.range ((n + 1) + 1), F i ω) =
            (fun ω => (∑ i ∈ Finset.range (n + 1), F i ω) + F (n + 1) ω) :=
        funext hpoint
      calc
        ∫ ω, (∑ i ∈ Finset.range ((n + 1) + 1), F i ω) ∂P =
            ∫ ω, ((∑ i ∈ Finset.range (n + 1), F i ω) + F (n + 1) ω) ∂P :=
          congrArg (fun g : Ω → ℝ => ∫ ω, g ω ∂P) hfun
        _ = (∫ ω, (∑ i ∈ Finset.range (n + 1), F i ω) ∂P) +
            ∫ ω, F (n + 1) ω ∂P :=
          integral_add
            (clbi_integrable_sum_range P F n (fun i hi => hF i (by omega)))
            (hF (n + 1) (by omega))
        _ = (∑ i ∈ Finset.range (n + 1), ∫ ω, F i ω ∂P) +
            ∫ ω, F (n + 1) ω ∂P := congrArg (fun z => z + ∫ ω, F (n + 1) ω ∂P)
              (ih (fun i hi => hF i (by omega)))
        _ = ∑ i ∈ Finset.range ((n + 1) + 1), ∫ ω, F i ω ∂P :=
          (hsum (fun i => ∫ ω, F i ω ∂P)).symm
