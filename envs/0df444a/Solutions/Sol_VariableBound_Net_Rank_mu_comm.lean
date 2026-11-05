-- Prove2me | solution 1 for VariableBound.Net.Rank.mu_comm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T02:20:12.015802+00:00
-- url     : https://prove2.me/submissions/e9fd3e7b-3baf-4969-91db-8398cf1cd4b7

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
theorem _root_.solution (g : ℕ) (D : Dat) (y a b κ : ℕ) : mu g D y a b κ = mu g D y b a κ := by
  unfold mu
  rw [min_comm, max_comm]
end VariableBound.Net.Rank
