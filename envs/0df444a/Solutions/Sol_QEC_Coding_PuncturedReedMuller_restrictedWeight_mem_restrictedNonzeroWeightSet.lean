-- Prove2me | solution 1 for QEC.Coding.PuncturedReedMuller.restrictedWeight_mem_restrictedNonzeroWeightSet
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T14:03:43.055956+00:00
-- url     : https://prove2.me/submissions/2112ad9a-b3f5-4c09-9a4a-9a4129021ea4

import Definitions.Def_QEC_Coding_ReedMuller_Base
import Definitions.Def_QEC_Coding_ReedMuller_Punctured

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
    restrictedWeight w word ∈ restrictedNonzeroWeightSet r m w :=
  ⟨word, hword, hnonzero, rfl⟩
end QEC.Coding.PuncturedReedMuller
