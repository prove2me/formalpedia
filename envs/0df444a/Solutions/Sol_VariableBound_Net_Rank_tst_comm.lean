-- Prove2me | solution 1 for VariableBound.Net.Rank.tst_comm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T02:19:58.378948+00:00
-- url     : https://prove2.me/submissions/8c01f736-2390-4255-ac04-35f423b7b028

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_VariableBound_Net_Defs
import Definitions.Def_VariableBound_Net_Rank

set_option autoImplicit false
section
section
open VariableBound VariableBound.Net
open Groundwork Groundwork.Prog
open VariableBound.Net.Rank
namespace VariableBound.Net.Rank
theorem _root_.solution (g n : ℕ) (D : Dat) (a b κ : ℕ) : tst g n D a b κ = tst g n D b a κ := by
  unfold tst
  rw [min_comm, max_comm]
end VariableBound.Net.Rank
