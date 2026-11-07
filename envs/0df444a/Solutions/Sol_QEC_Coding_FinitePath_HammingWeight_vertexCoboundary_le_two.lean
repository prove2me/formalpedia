-- Prove2me | solution 1 for QEC.Coding.FinitePath.HammingWeight_vertexCoboundary_le_two
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T09:06:45.102254+00:00
-- url     : https://prove2.me/submissions/d44eb095-f38d-42c0-a422-2536077171cf

import Definitions.Def_QEC_Coding_ChainComplex_Cohomology
import Definitions.Def_QEC_Coding_ChainComplex_FinitePath
import Theorems.Thm_QEC_Coding_FinitePath_HammingWeight_optionalSingle_le_one
import Theorems.Thm_QEC_Coding_HammingWeight_add_le


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FinitePath
universe u
variable {F : Type u} [Field F] [Fintype F] [DecidableEq F]
omit [Fintype F]
namespace QEC.Coding.FinitePath
theorem _root_.solution {n : Nat} (i : Fin (n + 1)) :
    HammingWeight (vertexCoboundary (F := F) i) ≤ 2 := by
  unfold vertexCoboundary
  exact (HammingWeight_add_le _ _).trans
    (Nat.add_le_add
      (HammingWeight_optionalSingle_le_one (F := F) _)
      (HammingWeight_optionalSingle_le_one (F := F) _))
end QEC.Coding.FinitePath
