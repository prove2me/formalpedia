-- Prove2me | solution 1 for SparsificationLemma.Geo.log_le_mul_log_two
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:32:39.315139+00:00
-- url     : https://prove2.me/submissions/1535df88-c8f6-4e13-88e1-85dea249dae8

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SparsificationLemma_Geo_Defs
import Definitions.Def_SparsificationLemma_Geo_Tau
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Definitions.Def_SparsificationLemma_Geo_Eps

set_option autoImplicit false
section
section
open SparsificationLemma SparsificationLemma.Geo
open UniformInK
namespace SparsificationLemma.Geo
theorem _root_.solution {y : ℝ} (hy : 0 < y) : Real.log y ≤ y * Real.log 2 := by
  have hL1 := Real.log_two_gt_d9
  have hL2 := Real.log_two_lt_d9
  have h1 : Real.log (y / 2) ≤ y / 2 - 1 := Real.log_le_sub_one_of_pos (by positivity)
  rw [Real.log_div hy.ne' (by norm_num)] at h1
  nlinarith
end SparsificationLemma.Geo
