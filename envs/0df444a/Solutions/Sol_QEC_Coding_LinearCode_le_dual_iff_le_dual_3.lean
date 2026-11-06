-- Prove2me | solution 3 for QEC.Coding.LinearCode.le_dual_iff_le_dual
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T20:07:15.489514+00:00
-- url     : https://prove2.me/submissions/f110a7f9-094d-4578-b8d1-5042df34750c

import Definitions.Def_QEC_Semantics_Core_Definitions
import Definitions.Def_QEC_Coding_Core_Definitions

set_option autoImplicit false
open QEC
open QEC.Coding
universe u v w x
open QEC.Coding.LinearCode
variable {F : Type u} {ι : Type v} [Field F] [Fintype F] [Fintype ι]
namespace QEC.Coding.LinearCode
theorem _root_.solution (C D : LinearCode F ι) :
    D.carrier ≤ C.dual.carrier ↔ C.carrier ≤ D.dual.carrier := by
  constructor
  · exact le_dual_of_le_dual C D
  · exact le_dual_of_le_dual D C
end QEC.Coding.LinearCode
