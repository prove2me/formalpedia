-- Prove2me | solution 1 for UniformInK.Thresholds.mul_betaSU_le
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-04T23:31:06.452613+00:00
-- url     : https://prove2.me/submissions/a51092da-5b4f-48da-b3a0-8599895cdd10

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

theorem solution (τ r : ℕ) : τ * betaSU τ r ≤ thetaU τ r := by
  cases r with
  | zero => simp [betaSU]
  | succ r =>
      rw [betaSU, thetaU, pow_succ]
      ring_nf
      exact le_rfl
