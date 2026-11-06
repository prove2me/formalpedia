-- Prove2me | solution 1 for QEC.Coding.ChainComplexData.pureZLogicalQuotientEquivMiddleHomology_mk
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T09:14:57.80983+00:00
-- url     : https://prove2.me/submissions/1675e5c6-b739-4b29-8e9b-d3ef72a133c6

import Definitions.Def_QEC_Semantics_Core_Definitions
import Definitions.Def_QEC_Coding_Core_Definitions

set_option autoImplicit false
open QEC
open QEC.Coding
universe u v w x
open QEC.Coding.ChainComplexData
variable {F : Type u} {ι : Type v} {C0 C2 : Type (max u v)} [Field F] [Fintype F]
    [Fintype ι] [AddCommGroup C0] [Module F C0] [AddCommGroup C2] [Module F C2]
namespace QEC.Coding.ChainComplexData
theorem _root_.solution {κ lambda : Type v}
    [Fintype κ] [Fintype lambda]
    (K : ChainComplexData F (Word F κ) (Word F ι) (Word F lambda))
    (x : K.firstCoboundaryCheckCode.dual.carrier) :
    K.pureZLogicalQuotientEquivMiddleHomology (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk (K.firstCoboundaryDualEquivMiddleCycleCode x) := by
  rfl
end QEC.Coding.ChainComplexData
