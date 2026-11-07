-- Prove2me | solution 1 for QEC.Coding.PuncturedReedMuller.shortenedReedMullerCode_dual_eq_punctured
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T15:14:23.096707+00:00
-- url     : https://prove2.me/submissions/9c1ddb57-bf57-435a-a45e-348dff83824a

import Definitions.Def_QEC_Coding_ReedMuller_Base
import Definitions.Def_QEC_Coding_ReedMuller_Punctured
import Theorems.Thm_QEC_Coding_PuncturedReedMuller_shortenedReedMullerCode_dual_eq_punctured_of_lt_of_le

set_option autoImplicit false
noncomputable section
open QEC
open QEC.Coding
open QEC.Coding.PuncturedReedMuller
open ReedMuller
namespace QEC.Coding.PuncturedReedMuller
theorem _root_.solution
    {w r m : Nat} (h : Admissible w r m) :
    (shortenedReedMullerCode (m - r - 1) m w).dual.carrier =
      (puncturedReedMullerCode r m w).carrier := by
  have hrm : r < m := by
    have := h.2.2
    omega
  have hcomplement : w ≤ m - r - 1 := by
    have := h.2
    omega
  exact shortenedReedMullerCode_dual_eq_punctured_of_lt_of_le hrm hcomplement
end QEC.Coding.PuncturedReedMuller
