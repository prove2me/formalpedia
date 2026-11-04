-- Prove2me | solution 1 for QuantumMaxCutEnergy.domination_of_integral
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T06:55:48.011083+00:00
-- url     : https://prove2.me/submissions/ed49a54a-0926-4734-9c04-f83a270dd54a

import Definitions.Def_QuantumMaxCutEnergyEstimationModel
import Definitions.Def_QuantumMaxCutEdgeLoads
import Definitions.Def_QuantumMaxCutEdgeInternalSum
import Theorems.Thm_QuantumMaxCutEnergy_integral_support_is_matching
import Mathlib

set_option autoImplicit false
open scoped BigOperators

open QuantumMaxCutEnergy

/-- **Integrality gives domination.** If an edge weight has values in `{0,1}` and vertex loads at most `1`, then
some integral matching carries at least its total weighted mass. This is the last link of the exactness
argument: it turns the rigidity statement (a vertex of the polytope is integral) into the domination bound. -/
theorem solution {n : ℕ} (w x : Edge n → ℝ)
    (hx : ∀ e, 0 ≤ x e) (hload : ∀ v, loadAt x v ≤ 1)
    (hint : ∀ e, x e = 0 ∨ x e = 1) :
    ∃ M : Finset (Edge n),
      (∀ e ∈ M, ∀ e' ∈ M, e ≠ e' →
        e.val.1 ≠ e'.val.1 ∧ e.val.1 ≠ e'.val.2 ∧ e.val.2 ≠ e'.val.1 ∧ e.val.2 ≠ e'.val.2) ∧
      ∑ e, w e * x e ≤ ∑ e ∈ M, w e := by
  classical
  refine ⟨Finset.univ.filter (fun e : Edge n => x e = 1),
    integral_support_is_matching x hx hload hint, ?_⟩
  have hterm : ∀ e : Edge n, w e * x e = if x e = 1 then w e else 0 := by
    intro e
    rcases hint e with h | h <;> simp [h]
  rw [Finset.sum_congr rfl (fun e (_ : e ∈ Finset.univ) => hterm e), Finset.sum_filter]

#print axioms solution
