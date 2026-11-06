-- Prove2me | solution 1 for PairsToBound.three_le_widthOr3
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T06:57:28.942097+00:00
-- url     : https://prove2.me/submissions/081b2440-5d42-4649-b2c8-b087e21c39ad

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PairsToBound_Defs
import Definitions.Def_SparsificationLemma_StepSparsify
import Mathlib.Tactic.Ring
import Definitions.Def_PairsToBound_Width
import Theorems.Thm_PairsToBound_start_le_foldr_max

set_option autoImplicit false
section
section
open PairsToBound
open Sat3 (CNF)
namespace PairsToBound
theorem _root_.solution {n : ℕ} (φ : CNF n) : 3 ≤ widthOr3 φ := start_le_foldr_max _ 3
end PairsToBound
