-- Prove2me | solution 1 for ThmCount.stRates
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T11:19:53.647859+00:00
-- url     : https://prove2.me/submissions/318d5f16-f640-416c-befc-c8fe883003b1

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ThmCount_Defs
import Definitions.Def_Wrap_Arith
import Definitions.Def_Wrap_ArithRate
import Definitions.Def_VariableBound_Paper_Arith
import Mathlib.Tactic
import Definitions.Def_ThmCount_Rates
import Theorems.Thm_ThmCount_rate_le
import Theorems.Thm_ThmCount_time_le

set_option autoImplicit false
section
section
open ThmCount
namespace ThmCount
theorem _root_.solution : StRates := fun C q a d => by
  obtain ⟨K, hK⟩ := time_le C q a d
  refine ⟨K, fun n hn => ?_⟩
  obtain ⟨h1, h2⟩ := rate_le hn (e := (1 : ℝ) / 20) (by norm_num)
  exact hK n _ h1 h2
end ThmCount
