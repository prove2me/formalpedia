-- Prove2me | solution 2 for UniformInK.Thresholds.thetaU_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T06:42:49.676475+00:00
-- url     : https://prove2.me/submissions/91eda817-8cb5-4c28-964b-41d8a6ede14b

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_UniformInK_Spars_Defs
import Mathlib.Tactic.Ring
import Definitions.Def_UniformInK_Spars_Thresholds

set_option autoImplicit false
section
section
open UniformInK
open Finset
open UniformInK.Thresholds
namespace UniformInK.Thresholds
theorem _root_.solution {τ : ℕ} (hτ : 0 < τ) (i : ℕ) : 0 < thetaU τ i := by
  cases i with
  | zero => exact Nat.one_pos
  | succ i => exact Nat.mul_pos (by omega) (Nat.pow_pos hτ)
end UniformInK.Thresholds
