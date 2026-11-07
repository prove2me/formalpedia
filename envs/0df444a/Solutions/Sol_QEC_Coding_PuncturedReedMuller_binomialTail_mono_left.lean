-- Prove2me | solution 1 for QEC.Coding.PuncturedReedMuller.binomialTail_mono_left
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T15:14:34.037562+00:00
-- url     : https://prove2.me/submissions/d9c62510-8e8e-423e-8108-e1d13c785bb0

import Definitions.Def_QEC_Coding_ReedMuller_Base
import Definitions.Def_QEC_Coding_ReedMuller_Punctured

set_option autoImplicit false
noncomputable section
open QEC
open QEC.Coding
open QEC.Coding.PuncturedReedMuller
open ReedMuller
namespace QEC.Coding.PuncturedReedMuller
theorem _root_.solution {a b w : Nat} (hab : a ≤ b) :
    binomialTail a w ≤ binomialTail b w := by
  induction b, hab using Nat.le_induction with
  | base => exact le_rfl
  | succ b _ ih =>
      calc
        binomialTail a w ≤ binomialTail b w := ih
        _ ≤ binomialTail (b + 1) w := by
          change binomialFrom b (w + 1) ≤ binomialFrom (b + 1) (w + 1)
          rw [binomialFrom_succ]
          exact Nat.le_add_right _ _
end QEC.Coding.PuncturedReedMuller
