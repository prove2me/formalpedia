-- Prove2me | solution 1 for VariableBound.Net.SizeU.two_mul_pairs_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T06:30:29.94837+00:00
-- url     : https://prove2.me/submissions/d8571fe8-d941-4bc2-8edd-7ec45f52b5ec

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_VariableBound_Net_Defs
import Definitions.Def_VariableBound_Net_Tests
import Definitions.Def_VariableBound_Params_Ineq
import Definitions.Def_ClauseBound_ParityChecks_Binom
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_VariableBound_Net_SizeU

set_option autoImplicit false
section
section
open VariableBound VariableBound.Net VariableBound.Net.SizeU
open Finset Groundwork AppVariables
variable {k g n nb M : ℕ} {D : Dat} {fl : Bool} {y : ℕ}
namespace VariableBound.Net.SizeU
theorem _root_.solution (g : ℕ) : 2 * ∑ b ∈ range g, b ≤ g ^ 2 := by
  rw [Nat.mul_comm, sum_range_id_mul_two, pow_two]
  exact Nat.mul_le_mul_left _ (Nat.sub_le _ _)
end VariableBound.Net.SizeU
