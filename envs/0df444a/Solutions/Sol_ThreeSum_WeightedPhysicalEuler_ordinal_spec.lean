-- Prove2me | solution 1 for ThreeSum.WeightedPhysicalEuler.ordinal_spec
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:00:10.430311+00:00
-- url     : https://prove2.me/submissions/65d1ad46-9d7b-4941-8e4a-e4facbf598fd

import Definitions.Def_Submission_Weighted_EulerMetadata
import Definitions.Def_Submission_ThreeSum_LightTernaryEulerMemo
import Definitions.Def_Submission_ThreeSum_TernaryPartialEuler
import Definitions.Def_Submission_Weighted_PhysicalEuler

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedPhysicalEuler
open Finset ThreeSum.TernaryJointType ThreeSum.TernaryBank ThreeSum.TernaryEuler
open ThreeSum.TernaryCodeSemantics
open ThreeSum.WeightedBankEnumeration (cacheCost)
set_option maxHeartbeats 3000000
namespace ThreeSum.WeightedPhysicalEuler
theorem _root_.solution {N : ℕ} {words : ℕ → TritWord N} {n : ℕ} {w : TritWord N}
    (h : ∃ j<n, words j=w) : ordinal words n w<n ∧ words (ordinal words n w)=w := by
  unfold ordinal
  rw [dif_pos h]
  exact h.choose_spec
end ThreeSum.WeightedPhysicalEuler
