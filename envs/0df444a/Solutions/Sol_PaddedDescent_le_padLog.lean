-- Prove2me | solution 1 for PaddedDescent.le_padLog
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T20:36:30.421066+00:00
-- url     : https://prove2.me/submissions/13775f74-5ab1-427c-bfb1-9f3d6d1a62e4

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PaddedDescent_PadRate
import Definitions.Def_PaddedDescent_BrutePad
import Definitions.Def_ToTuring_Poly_Decode
import Definitions.Def_PaddedDescent_Reduce
import Theorems.Thm_Groundwork_TM_Run_trans


set_option autoImplicit false
section
open PaddedDescent
open Groundwork Groundwork.Decode Sat3 Turing
namespace PaddedDescent
theorem _root_.solution {C₀ n : ℕ} (h : 2 ^ sOf n ≤ C₀) : n ≤ padLog C₀ n := by
  have h1 : n < 2 ^ sOf n * (n / 2 ^ sOf n + 1) := Nat.lt_mul_div_succ n (Nat.two_pow_pos _)
  exact h1.le.trans (Nat.mul_le_mul_right _ h)
end PaddedDescent
