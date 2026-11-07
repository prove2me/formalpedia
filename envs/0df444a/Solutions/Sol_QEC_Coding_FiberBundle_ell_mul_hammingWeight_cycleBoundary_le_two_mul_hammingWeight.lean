-- Prove2me | solution 1 for QEC.Coding.FiberBundle.ell_mul_hammingWeight_cycleBoundary_le_two_mul_hammingWeight
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T07:11:48.54371+00:00
-- url     : https://prove2.me/submissions/434d3af7-3bf5-4bb8-b4a3-c451b5ab9359

import Definitions.Def_QEC_Coding_FiberBundle_CohomologyRepresentatives
import Definitions.Def_QEC_Coding_FiberBundle_TwistGraph
import Definitions.Def_QEC_Coding_FiberBundle_HomologyRepresentatives
import Theorems.Thm_QEC_Coding_FiberBundle_hammingWeight_eq_ell_mul_coarseFiberWord
import Theorems.Thm_QEC_Coding_FiberBundle_hammingWeight_cycleFiberChainBoundary_le_two_mul
import Theorems.Thm_QEC_Coding_FiberBundle_hammingWeight_cycleBoundary_eq_coarseBoundaryWord
import Theorems.Thm_QEC_Coding_FiberBundle_coarseBoundaryWord_eq_cycleFiberChainBoundary_coarseFiberWord

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle
universe u
namespace QEC.Coding.FiberBundle
theorem _root_.solution
    (ell : Nat) [NeZero ell] [NeZero (ell - 1)]
    (v : Word (ZMod 2) (ZMod (ell * ell)))
    (hBoundarySupport :
      ∀ j, cycleFiberChainBoundary (ell * ell) v j ≠ 0 →
        fiberResidue ell j = 0) :
    ell * HammingWeight (cycleFiberChainBoundary (ell * ell) v) ≤
      2 * HammingWeight v := by
  have hFine :=
    hammingWeight_eq_ell_mul_coarseFiberWord
      ell v hBoundarySupport
  have hBoundary :=
    hammingWeight_cycleBoundary_eq_coarseBoundaryWord
      ell v hBoundarySupport
  have hCoarseBoundary :=
    coarseBoundaryWord_eq_cycleFiberChainBoundary_coarseFiberWord
      ell v hBoundarySupport
  calc
    ell * HammingWeight (cycleFiberChainBoundary (ell * ell) v) =
        ell * HammingWeight
          (cycleFiberChainBoundary ell (coarseFiberWord ell v)) := by
            rw [hBoundary, hCoarseBoundary]
    _ ≤ ell * (2 * HammingWeight (coarseFiberWord ell v)) :=
      Nat.mul_le_mul_left ell
        (hammingWeight_cycleFiberChainBoundary_le_two_mul
          ell (coarseFiberWord ell v))
    _ = 2 * HammingWeight v := by
      rw [hFine]
      ac_rfl
end QEC.Coding.FiberBundle
