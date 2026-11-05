-- Prove2me | solution 1 for VariableBound.Net.CertRank.choose_min
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T05:34:35.296637+00:00
-- url     : https://prove2.me/submissions/522ef29f-8db4-42b4-959c-a96049bc46f5

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_VariableBound_Net_Rank
import Definitions.Def_ClauseBound_ParityChecks_CertLib
import Definitions.Def_VariableBound_Net_CertRank

set_option autoImplicit false
section
section
open VariableBound VariableBound.Net
open Groundwork PaddedDescent.F ClauseBound.ParityChecks.CertLib
open VariableBound.Net.CertRank
namespace VariableBound.Net.CertRank
theorem _root_.solution (t μ : ℕ) : t.choose (min μ (t + 1)) = t.choose μ := by
  rcases Nat.le_total μ (t + 1) with h | h
  · rw [min_eq_left h]
  · rw [min_eq_right h, Nat.choose_eq_zero_of_lt (by omega), Nat.choose_eq_zero_of_lt (by omega)]
end VariableBound.Net.CertRank
