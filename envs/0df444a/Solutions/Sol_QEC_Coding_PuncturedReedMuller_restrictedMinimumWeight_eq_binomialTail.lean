-- Prove2me | solution 1 for QEC.Coding.PuncturedReedMuller.restrictedMinimumWeight_eq_binomialTail
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T15:14:38.728344+00:00
-- url     : https://prove2.me/submissions/a88e1652-ac48-4e28-94e5-0ba03abf09f8

import Definitions.Def_QEC_Coding_ReedMuller_Base
import Definitions.Def_QEC_Coding_ReedMuller_Punctured
import Theorems.Thm_QEC_Coding_PuncturedReedMuller_restrictedNonzeroWeightSet_nonempty
import Theorems.Thm_QEC_Coding_PuncturedReedMuller_restrictedMinimumWeight_le_binomialTail

set_option autoImplicit false
noncomputable section
open QEC
open QEC.Coding
open QEC.Coding.PuncturedReedMuller
open ReedMuller
namespace QEC.Coding.PuncturedReedMuller
theorem _root_.solution
    {m r w : Nat} (hnoKernel : w < m - r) :
    restrictedMinimumWeight r m w = binomialTail (m - r) w := by
  apply le_antisymm
  · exact restrictedMinimumWeight_le_binomialTail (by omega)
  · unfold restrictedMinimumWeight
    apply le_csInf (restrictedNonzeroWeightSet_nonempty r m w)
    intro weight hweight
    rcases (mem_restrictedNonzeroWeightSet).1 hweight with
      ⟨word, hword, hnonzero, rfl⟩
    exact binomialTail_le_restrictedWeight hnoKernel hword hnonzero
end QEC.Coding.PuncturedReedMuller
