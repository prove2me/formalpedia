-- Prove2me | solution 1 for StabilityDichotomies.Solvability.greatest_solution_true_outside_scopes
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T05:05:26.358668+00:00
-- url     : https://prove2.me/submissions/4ac5923d-6422-4849-aaf4-3e70084fdb82

import Definitions.Def_StabilityDichotomies_Solvability_Model
noncomputable section
open scoped Classical BigOperators
open StabilityDichotomies.Solvability

theorem solution {Γ : Language} {V : Type} [Fintype V]
    (I : Instance Γ V) (xmax : V → Bool) (hmax : Solution I xmax)
    (hgreatest : ∀ x, Solution I x → x ≤ xmax)
    (v : V) (hv : ∀ c ∈ I.constraints, ∀ i, c.scope i ≠ v) : xmax v = true := by
  have hu : Solution I (Function.update xmax v true) := by
    intro c hc
    have heq : (fun i => (Function.update xmax v true) (c.scope i)) =
        (fun i => xmax (c.scope i)) := by
      funext i
      simp [Function.update, hv c hc i]
    simpa [Constraint.Satisfied, heq] using hmax c hc
  apply Bool.eq_true_of_true_le
  simpa using hgreatest (Function.update xmax v true) hu v
