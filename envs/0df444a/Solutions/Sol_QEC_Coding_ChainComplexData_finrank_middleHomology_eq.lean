-- Prove2me | solution 1 for QEC.Coding.ChainComplexData.finrank_middleHomology_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T12:14:30.757643+00:00
-- url     : https://prove2.me/submissions/1cb9ddf7-fb16-4c34-a7fc-6466f4c03a85

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
theorem _root_.solution
    (K : ChainComplexData F C0 (Word F ι) C2) :
    Module.finrank F K.middleHomology =
      Dimension K.middleCycleCode - Dimension K.middleBoundaryCode := by
  have h := Submodule.finrank_quotient_add_finrank K.middleBoundaryInCycles
  rw [finrank_middleBoundaryInCycles_eq,
    ← Dimension_eq_finrank_carrier K.middleCycleCode] at h
  rw [← h]
  exact (Nat.add_sub_cancel_right _ _).symm
end QEC.Coding.ChainComplexData
