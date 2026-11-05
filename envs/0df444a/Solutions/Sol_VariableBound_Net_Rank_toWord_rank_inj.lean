-- Prove2me | solution 1 for VariableBound.Net.Rank.toWord_rank_inj
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T05:41:30.131779+00:00
-- url     : https://prove2.me/submissions/9fc6724b-831c-43a2-b7cc-fa502b1b5a51

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_VariableBound_Net_Defs
import Definitions.Def_VariableBound_Net_Rank
import Theorems.Thm_VariableBound_Net_Rank_rank_inj
import Theorems.Thm_VariableBound_Net_Rank_rank_lt_two_pow
import Theorems.Thm_Groundwork_PolyT_count
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_TM_Run_trans
import Theorems.Thm_Groundwork_ofWord_toWord
attribute [local fun_prop] Groundwork.PolyT.count
attribute [local fun_prop] Groundwork.PolyT.length



set_option autoImplicit false
section
section
open VariableBound VariableBound.Net
open Groundwork Groundwork.Prog
open VariableBound.Net.Rank
namespace VariableBound.Net.Rank
theorem _root_.solution (x x' : List Bool) (t μ : ℕ) (ht : x.length = t) (ht' : x'.length = t) (hμ : x.count true = μ) (hμ' : x'.count true = μ) :
    toWord (cw t μ) (rank x) = toWord (cw t μ) (rank x') ↔ x = x' := by
  refine ⟨fun h => ?_, fun h => by rw [h]⟩
  have h1 := congrArg ofWord h
  rw [ofWord_toWord (rank_lt_two_pow x t μ ht hμ), ofWord_toWord (rank_lt_two_pow x' t μ ht' hμ')] at h1
  exact rank_inj x x' (ht.trans ht'.symm) (hμ.trans hμ'.symm) h1
end VariableBound.Net.Rank
