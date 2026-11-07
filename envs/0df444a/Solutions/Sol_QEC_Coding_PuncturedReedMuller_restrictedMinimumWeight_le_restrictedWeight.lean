-- Prove2me | solution 1 for QEC.Coding.PuncturedReedMuller.restrictedMinimumWeight_le_restrictedWeight
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T14:06:42.051911+00:00
-- url     : https://prove2.me/submissions/5c9ce094-223d-48ed-bfa8-225d4a4af3b1

import Definitions.Def_QEC_Coding_ReedMuller_Base
import Definitions.Def_QEC_Coding_ReedMuller_Punctured
import Theorems.Thm_QEC_Coding_PuncturedReedMuller_restrictedWeight_mem_restrictedNonzeroWeightSet

set_option autoImplicit false
noncomputable section
open QEC
open QEC.Coding
open QEC.Coding.PuncturedReedMuller
open ReedMuller
namespace QEC.Coding.PuncturedReedMuller
theorem _root_.solution
    {r m w : Nat} {word : Word (ZMod 2) (BooleanPoint m)}
    (hword : word ∈ (reedMullerCode r m).carrier) (hnonzero : word ≠ 0) :
    restrictedMinimumWeight r m w ≤ restrictedWeight w word := by
  exact csInf_le' (restrictedWeight_mem_restrictedNonzeroWeightSet hword hnonzero)
end QEC.Coding.PuncturedReedMuller
