-- Prove2me | solution 2 for QEC.Coding.LinearCode.le_dual_iff_le_dual
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-05T19:20:30.97211+00:00
-- url     : https://prove2.me/submissions/9cb95a87-f633-4cc2-accb-e67a6d7221b5

import Definitions.Def_QEC_Semantics_Core_Definitions
import Definitions.Def_QEC_Coding_Core_Definitions
set_option autoImplicit false
open QEC
open QEC.Coding
universe u v w x
open QEC.Coding.LinearCode
variable {F : Type u} {ι : Type v} [Field F] [Fintype F] [Fintype ι]

theorem solution (C D : LinearCode F ι) :
    D.carrier ≤ C.dual.carrier ↔ C.carrier ≤ D.dual.carrier := by
  constructor
  · exact fun h => QEC.Coding.LinearCode.le_dual_of_le_dual C D h
  · exact fun h => QEC.Coding.LinearCode.le_dual_of_le_dual D C h
