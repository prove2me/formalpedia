-- Prove2me | solution 1 for StabilityDichotomies.Solvability.least_solution_false_outside_scopes
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T05:05:11.44875+00:00
-- url     : https://prove2.me/submissions/f73cca08-0232-423f-bd04-0ff1a723ef6a

import Definitions.Def_StabilityDichotomies_Solvability_Model
noncomputable section
open scoped Classical BigOperators
open StabilityDichotomies.Solvability

theorem solution {Γ : Language} {V : Type} [Fintype V]
    (I : Instance Γ V) (xmin : V → Bool) (hmin : Solution I xmin)
    (hleast : ∀ x, Solution I x → xmin ≤ x)
    (v : V) (hv : ∀ c ∈ I.constraints, ∀ i, c.scope i ≠ v) : xmin v = false := by
  have hu : Solution I (Function.update xmin v false) := by
    intro c hc
    have heq : (fun i => (Function.update xmin v false) (c.scope i)) =
        (fun i => xmin (c.scope i)) := by
      funext i
      simp [Function.update, hv c hc i]
    simpa [Constraint.Satisfied, heq] using hmin c hc
  apply Bool.eq_false_of_le_false
  simpa using hleast (Function.update xmin v false) hu v

