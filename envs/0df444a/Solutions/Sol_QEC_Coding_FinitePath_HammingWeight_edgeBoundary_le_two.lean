-- Prove2me | solution 1 for QEC.Coding.FinitePath.HammingWeight_edgeBoundary_le_two
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T09:06:56.847659+00:00
-- url     : https://prove2.me/submissions/f1851251-27a6-4c9c-ba38-6dcbc9b6ae2d

import Definitions.Def_QEC_Coding_ChainComplex_Cohomology
import Definitions.Def_QEC_Coding_ChainComplex_FinitePath
import Theorems.Thm_QEC_Coding_FinitePath_HammingWeight_single_le_one
import Theorems.Thm_QEC_Coding_HammingWeight_add_le


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FinitePath
universe u
variable {F : Type u} [Field F] [Fintype F] [DecidableEq F]
omit [Fintype F]
namespace QEC.Coding.FinitePath
theorem _root_.solution {n : Nat} (j : Fin n) :
    HammingWeight (edgeBoundary (F := F) j) ≤ 2 := by
  unfold edgeBoundary
  exact (HammingWeight_add_le _ _).trans
    (Nat.add_le_add
      (HammingWeight_single_le_one (F := F) _)
      (HammingWeight_single_le_one (F := F) _))
end QEC.Coding.FinitePath
