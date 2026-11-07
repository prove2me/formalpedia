-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.conj_mem_lpsQuaternionShell_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T21:33:44.644204+00:00
-- url     : https://prove2.me/submissions/41552f88-f254-44ea-944b-57383a92000b

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuaternion
import Mathlib.Data.Finset.Interval
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuaternionShell
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsResiduePrimeAt_q
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsResiduePrimeAt_q



set_option autoImplicit false
open scoped MatrixGroups
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
variable {p : ℕ}
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    {p : ℕ} (hp : 0 < p) (t : LPSQuaternion) :
    t.conj ∈ lpsQuaternionShell p ↔ t ∈ lpsQuaternionShell p := by
  rw [mem_lpsQuaternionShell_iff hp, mem_lpsQuaternionShell_iff hp]
  simp [LPSQuaternion.IsNormalizedAt]
end QEC.Coding.TannerLiftedProduct
