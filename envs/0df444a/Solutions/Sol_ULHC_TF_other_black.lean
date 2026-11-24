-- Prove2me | solution 1 for ULHC.TF.other_black
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:45:06.281056+00:00
-- url     : https://prove2.me/submissions/591d5c36-f040-4c0f-84b5-6b00f1f334fd

import Definitions.Def_ULHC_StripCount
import Definitions.Def_ULHC_TwoFactor
import Theorems.Thm_ULHC_TF_black_q

set_option autoImplicit true
open ULHC
open Finset
open ULHC.TF
namespace ULHC.TF
theorem _root_.solution {e : Edge} {v : Pt} (hv : e.p = v ∨ e.q = v) :
    Black (other e v) ↔ ¬ Black v := by
  unfold other
  by_cases h : e.p = v
  · rw [if_pos h, ← h, black_q]
  · rw [if_neg h, ← hv.resolve_left h, black_q]; tauto
end ULHC.TF
