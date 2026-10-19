-- Prove2me | solution 1 for PermanentFormulaLowerBound.RationalFormula.splitFractionHom_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:11.481307+00:00
-- url     : https://prove2.me/submissions/2f647660-9ad7-4759-9108-d6cff0b625f2

import Mathlib
import Definitions.Def_Permanent

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentFormulaLowerBound
universe u v w
open scoped BigOperators Kronecker Matrix IntermediateField.algebraAdjoinAdjoin
open PermanentFormulaLowerBound.RationalFormula
noncomputable section
variable {Y Z F : Type*}
namespace PermanentFormulaLowerBound.RationalFormula
theorem _root_.solution [Field F] :
    Function.Injective (splitFractionHom (Y := Y) (Z := Z) (F := F)) :=
  RingHom.injective (splitFractionHom (Y := Y) (Z := Z) (F := F))
end PermanentFormulaLowerBound.RationalFormula
