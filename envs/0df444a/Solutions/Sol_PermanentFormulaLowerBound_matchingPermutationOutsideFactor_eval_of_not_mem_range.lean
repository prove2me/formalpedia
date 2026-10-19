-- Prove2me | solution 1 for PermanentFormulaLowerBound.matchingPermutationOutsideFactor_eval_of_not_mem_range
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:12.090475+00:00
-- url     : https://prove2.me/submissions/97b85aea-0898-4a29-8007-8db9274e15b4

import Mathlib
import Definitions.Def_Permanent

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentFormulaLowerBound
universe u v w
open scoped BigOperators Kronecker Matrix IntermediateField.algebraAdjoinAdjoin
namespace PermanentFormulaLowerBound
theorem _root_.solution
    {n : ℕ} {Y : Type u} (d : Y ↪ Fin n × Fin n)
    (σ : Equiv.Perm (Fin n)) (i j : Fin n)
    (hij : σ i = j) (houtside : (i, j) ∉ Set.range d)
    (ξ : matchingOutside d → ℂ) :
    MvPolynomial.eval ξ (matchingPermutationOutsideFactor d σ i) =
      ξ ⟨(i, j), houtside⟩ := by
  classical
  let z : matchingOutside d := ⟨(i, j), houtside⟩
  have hsplit : (matchingVariableEquiv d).symm (i, j) = .inr z := by
    apply (matchingVariableEquiv d).injective
    simp [z]
  unfold matchingPermutationOutsideFactor
  rw [hij, hsplit]
  simp [z]
end PermanentFormulaLowerBound
