-- Prove2me | solution 1 for QEC.Coding.PuncturedReedMuller.shortenedReedMullerCode_dualContainment
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T15:14:18.769478+00:00
-- url     : https://prove2.me/submissions/cb186402-bc8d-4e96-bb98-5de398164737

import Definitions.Def_QEC_Coding_ReedMuller_Base
import Definitions.Def_QEC_Coding_ReedMuller_Punctured
import Theorems.Thm_QEC_Coding_PuncturedReedMuller_wordPairing_restrictKept_eq_of_restrictLow_eq_zero
import Theorems.Thm_QEC_Coding_ReedMuller_reedMullerCode_le_dual_of_add_lt


set_option autoImplicit false
noncomputable section
open QEC
open QEC.Coding
open QEC.Coding.PuncturedReedMuller
open ReedMuller
namespace QEC.Coding.PuncturedReedMuller
theorem _root_.solution
    {w r m : Nat} (h : Admissible w r m) :
    (shortenedReedMullerCode (m - r - 1) m w).carrier ≤
      (shortenedReedMullerCode r m w).dual.carrier := by
  have hdegree : r + (m - r - 1) < m := by
    have htwo : 2 * r < m := h.2.2
    have hrm : r < m := by omega
    omega
  intro z hz
  refine ((shortenedReedMullerCode r m w).mem_dual z).2 ?_
  intro x hx
  rcases (mem_shortenedReedMullerCode z).1 hz with
    ⟨fullZ, hfullZ, hlowZ, hkeptZ⟩
  rcases (mem_shortenedReedMullerCode x).1 hx with
    ⟨fullX, hfullX, _hlowX, hkeptX⟩
  rw [← hkeptZ, ← hkeptX,
    wordPairing_restrictKept_eq_of_restrictLow_eq_zero fullZ fullX hlowZ]
  exact (reedMullerCode r m).orthogonal_of_mem_dual
    (reedMullerCode_le_dual_of_add_lt hdegree hfullZ) hfullX
end QEC.Coding.PuncturedReedMuller
