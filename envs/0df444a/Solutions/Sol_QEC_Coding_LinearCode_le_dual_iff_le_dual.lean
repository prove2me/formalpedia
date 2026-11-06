-- Prove2me | solution 1 for QEC.Coding.LinearCode.le_dual_iff_le_dual
-- status  : ACCEPTED   (prove)
-- author  : @dphz
-- created : 2026-11-05T18:40:27.5872+00:00
-- url     : https://prove2.me/submissions/c942517a-ff43-4e91-b477-4055b108e48e

-- ID: 9b8dd6de-1a3e-4902-a87a-11c0dbbaaafd | NAME: QEC.Coding.LinearCode.le_dual_iff_le_dual | 未本地编译验证
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
