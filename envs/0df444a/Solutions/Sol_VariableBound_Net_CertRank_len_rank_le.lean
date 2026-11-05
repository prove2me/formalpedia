-- Prove2me | solution 1 for VariableBound.Net.CertRank.len_rank_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T05:34:34.241987+00:00
-- url     : https://prove2.me/submissions/8acfe280-2b10-4f6e-9a8a-68d348f69ff6

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_VariableBound_Net_Rank
import Definitions.Def_ClauseBound_ParityChecks_CertLib
import Definitions.Def_VariableBound_Net_CertRank
import Theorems.Thm_ClauseBound_ParityChecks_Params_choose_le_two_pow
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_RebalanceArith_size_le
import Theorems.Thm_VariableBound_Net_Rank_rank_lt
attribute [local fun_prop] Groundwork.PolyT.length



set_option autoImplicit false
section
section
open VariableBound VariableBound.Net
open Groundwork PaddedDescent.F ClauseBound.ParityChecks.CertLib
open VariableBound.Net.CertRank
namespace VariableBound.Net.CertRank
theorem _root_.solution (x : List Bool) : len (rank x) ≤ len x := by
  rw [len_nat, len_bools]
  have h : Nat.size (rank x) ≤ x.length := by
    rw [Nat.size_le]
    exact (Rank.rank_lt x).trans_le (Nat.choose_le_two_pow _ _)
  omega
end VariableBound.Net.CertRank
