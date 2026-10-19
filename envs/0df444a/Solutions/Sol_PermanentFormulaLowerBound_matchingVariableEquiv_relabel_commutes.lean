-- Prove2me | solution 1 for PermanentFormulaLowerBound.matchingVariableEquiv_relabel_commutes
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:13.787743+00:00
-- url     : https://prove2.me/submissions/2dfd4321-6091-4182-b64b-7de4ca1fe367

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
    {n : ℕ} {Y : Type u}
    (d₀ d : Y ↪ Fin n × Fin n)
    (e : Equiv.Perm (Fin n × Fin n))
    (he : ∀ y : Y, e (d₀ y) = d y) :
    (matchingVariableEquiv d₀).symm.trans
      (Equiv.sumCongr (Equiv.refl Y)
        (matchingOutsideRelabelEquiv d₀ d e he)) =
      e.trans (matchingVariableEquiv d).symm := by
  apply Equiv.ext
  intro x
  apply (matchingVariableEquiv d).injective
  simp only [Equiv.trans_apply, Equiv.apply_symm_apply]
  change matchingVariableEquiv d
    ((Equiv.sumCongr (Equiv.refl Y)
      (matchingOutsideRelabelEquiv d₀ d e he))
        ((matchingVariableEquiv d₀).symm x)) = e x
  generalize hz : (matchingVariableEquiv d₀).symm x = z
  have hx : matchingVariableEquiv d₀ z = x := by
    rw [← hz, Equiv.apply_symm_apply]
  cases z with
  | inl y =>
      simpa [← hx] using (he y).symm
  | inr w =>
      simp [← hx, matchingOutsideRelabelEquiv_apply_val]
end PermanentFormulaLowerBound
