-- Prove2me | solution 1 for VariableBound.Net.Rank.rank_lt_two_pow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T05:34:31.946951+00:00
-- url     : https://prove2.me/submissions/f7f8a195-3a16-4aad-9022-4d01944a8e71

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_VariableBound_Net_Defs
import Definitions.Def_VariableBound_Net_Rank
import Theorems.Thm_VariableBound_Net_Rank_rank_lt
import Theorems.Thm_Groundwork_PolyT_count
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.count
attribute [local fun_prop] Groundwork.PolyT.length



set_option autoImplicit false
section
section
open VariableBound VariableBound.Net
open Groundwork Groundwork.Prog
open VariableBound.Net.Rank
namespace VariableBound.Net.Rank
theorem _root_.solution (x : List Bool) (t μ : ℕ) (ht : x.length = t) (hμ : x.count true = μ) : rank x < 2 ^ cw t μ := by
  subst ht hμ
  exact (rank_lt x).trans_le (Nat.le_pow_clog (by norm_num) _)
end VariableBound.Net.Rank
