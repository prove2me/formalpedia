-- Prove2me | solution 1 for PermanentFormulaLowerBound.matchingCanonicalComplexPoints_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:13.787743+00:00
-- url     : https://prove2.me/submissions/299c06fd-ebbb-4d23-b498-e71502758743

import Mathlib
import Definitions.Def_Permanent

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentFormulaLowerBound
universe u v w
open scoped BigOperators Kronecker Matrix IntermediateField.algebraAdjoinAdjoin
namespace PermanentFormulaLowerBound
theorem _root_.solution (m : ℕ) :
    Function.Injective (matchingCanonicalComplexPoints m) := by
  intro a b h
  change (a.1 : ℂ) = (b.1 : ℂ) at h
  apply Fin.ext
  exact_mod_cast h
end PermanentFormulaLowerBound
