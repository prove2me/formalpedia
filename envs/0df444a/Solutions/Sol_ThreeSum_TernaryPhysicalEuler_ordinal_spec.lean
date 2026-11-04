-- Prove2me | solution 1 for ThreeSum.TernaryPhysicalEuler.ordinal_spec
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:00:11.817889+00:00
-- url     : https://prove2.me/submissions/8aa96b7a-bf5a-4bb7-a831-996faa3672d0

import Definitions.Def_Submission_ThreeSum_LightTernaryEulerMetadata
import Definitions.Def_Submission_ThreeSum_LightTernaryEulerMemo
import Definitions.Def_Submission_ThreeSum_TernaryPartialEuler
import Definitions.Def_Submission_ThreeSum_TernaryPhysicalEuler

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryPhysicalEuler
open Finset ThreeSum.TernaryJointType ThreeSum.TernaryBank ThreeSum.TernaryEuler
open ThreeSum.TernaryCodeSemantics
set_option maxHeartbeats 3000000
namespace ThreeSum.TernaryPhysicalEuler
theorem _root_.solution {N : ℕ} {words : ℕ → TritWord N} {n : ℕ} {w : TritWord N}
    (h : ∃ j<n, words j=w) : ordinal words n w<n ∧ words (ordinal words n w)=w := by
  unfold ordinal
  rw [dif_pos h]
  exact h.choose_spec
end ThreeSum.TernaryPhysicalEuler
