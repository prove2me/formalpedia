-- Prove2me | solution 1 for Variance.stPairProb
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:30:18.142548+00:00
-- url     : https://prove2.me/submissions/f9e1658c-d442-4f1e-aa89-272201f38a8c

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Variance_Defs
import Definitions.Def_Eight_SecNetworks_Grouping
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Definitions.Def_Variance_Cov
import Theorems.Thm_Eight_SecNetworks_pair_prob


set_option autoImplicit false
section
section
open Variance
open Finset Eight.SecNetworks
namespace Variance
theorem _root_.solution : StPairProb := by
  intro g K γ γ' p hp
  exact pair_prob (mem_filter.1 hp).2 γ γ'
end Variance
