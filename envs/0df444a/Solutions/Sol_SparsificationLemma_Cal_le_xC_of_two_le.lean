-- Prove2me | solution 1 for SparsificationLemma.Cal.le_xC_of_two_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:14:55.222131+00:00
-- url     : https://prove2.me/submissions/e91bd34b-d92b-44b1-a144-09337d4480ad

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SparsificationLemma_Cal_Defs
import Definitions.Def_SparsificationLemma_Cal_Real
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Definitions.Def_SparsificationLemma_Cal_Alpha

set_option autoImplicit false
section
section
open SparsificationLemma SparsificationLemma.Cal
namespace SparsificationLemma.Cal
theorem _root_.solution {k : ℕ} {ε : ℚ} (hk : 2 ≤ k) (h0 : 0 < ε) (h1 : ε ≤ 1) : 32 ≤ xC k ε := by
  have hk' : (2 : ℚ) ≤ (k : ℚ) := by exact_mod_cast hk
  rw [xC, le_div_iff₀ h0]
  nlinarith
end SparsificationLemma.Cal
