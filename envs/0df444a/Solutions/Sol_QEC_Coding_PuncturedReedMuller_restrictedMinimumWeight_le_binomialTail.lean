-- Prove2me | solution 1 for QEC.Coding.PuncturedReedMuller.restrictedMinimumWeight_le_binomialTail
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T14:09:14.44348+00:00
-- url     : https://prove2.me/submissions/632c9592-5010-447e-8852-6446b08c1a6e

import Definitions.Def_QEC_Coding_ReedMuller_Base
import Definitions.Def_QEC_Coding_ReedMuller_Punctured
import Theorems.Thm_QEC_Coding_PuncturedReedMuller_restrictedMinimumWeight_le_restrictedWeight

set_option autoImplicit false
noncomputable section
open QEC
open QEC.Coding
open QEC.Coding.PuncturedReedMuller
open ReedMuller
namespace QEC.Coding.PuncturedReedMuller
theorem _root_.solution
    {m r w : Nat} (hrm : r ≤ m) :
    restrictedMinimumWeight r m w ≤ binomialTail (m - r) w := by
  obtain ⟨word, hword, hnonzero, hweight⟩ :=
    exists_reedMullerCodeword_restrictedWeight_eq_binomialTail (w := w) hrm
  calc
    restrictedMinimumWeight r m w ≤ restrictedWeight w word :=
      restrictedMinimumWeight_le_restrictedWeight hword hnonzero
    _ = binomialTail (m - r) w := hweight
end QEC.Coding.PuncturedReedMuller
