-- Prove2me | solution 1 for ThmCount.stPadKeepsCount
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T11:13:37.760222+00:00
-- url     : https://prove2.me/submissions/dfb1e2c7-f5f6-4256-95c0-404ecd37d6c0

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ThmCount_Defs
import Definitions.Def_Wrap_FrontEnd
import Definitions.Def_WidthK_Decode
import Definitions.Def_ToTuring_Poly_Decode
import Mathlib.Tactic
import Definitions.Def_ThmCount_FrontEnd
import Theorems.Thm_ThmCount_numSat_pad4
import Theorems.Thm_ThmCount_dropFour_binary
import Theorems.Thm_Wrap_pad4KeepsSatAndMeetsSideConditions


set_option autoImplicit false
section
section
section
open ThmCount
open Groundwork Groundwork.Decode
namespace ThmCount
theorem _root_.solution : StPadKeepsCount := fun n φ h =>
  ⟨(Wrap.pad4KeepsSatAndMeetsSideConditions n φ h).1, numSat_pad4 φ, by rw [dropFour_binary, numSat_pad4]⟩
end ThmCount
