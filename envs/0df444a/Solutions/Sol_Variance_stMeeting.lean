-- Prove2me | solution 1 for Variance.stMeeting
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:30:43.085923+00:00
-- url     : https://prove2.me/submissions/35cd49cf-3f60-4070-b4b0-18134e60be53

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Variance_Defs
import Definitions.Def_Eight_SecNetworks_Grouping
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Definitions.Def_Variance_Cov
import Theorems.Thm_Eight_SecNetworks_meeting_le


set_option autoImplicit false
section
section
open Variance
open Finset Eight.SecNetworks
namespace Variance
theorem _root_.solution : StMeeting := by
  intro g P c hs hP p
  refine le_trans (le_of_eq ?_) (meeting_le hs hP p)
  unfold ordered
  rw [filter_filter]
end Variance
