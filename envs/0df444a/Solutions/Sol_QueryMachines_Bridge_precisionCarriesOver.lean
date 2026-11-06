-- Prove2me | solution 1 for QueryMachines.Bridge.precisionCarriesOver
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T06:58:43.222053+00:00
-- url     : https://prove2.me/submissions/4f4ff80d-b279-4a5c-a03e-2d9a3ba197a1

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedToPadded_Defs
import Definitions.Def_ToTuring_Lib_Nat1
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp
import Definitions.Def_CountedToPadded_Need
import Theorems.Thm_Groundwork_PolyT_div_pow
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_TM_Run_trans
attribute [local fun_prop] Groundwork.PolyT.div_pow
attribute [local fun_prop] Groundwork.PolyT.length



set_option autoImplicit false
section
section
open QueryMachines QueryMachines.Bridge
open Groundwork PaddedDescent.F Printed CliqueLevels Proof
namespace QueryMachines.Bridge
theorem _root_.solution : PrecisionCarriesOver := by
  rintro e e' slU C ⟨h1, h2, h3⟩ h
  refine ⟨h1, fun l => (h2 l).trans (h l).1, fun l => ?_⟩
  obtain ⟨g1, g2, g3⟩ := h l
  have he : 0 < e l := lt_of_lt_of_le (by positivity) (h2 l)
  have he' : 0 < e' l := he.trans_le g1
  have hh : 2 / e l ≤ (2 / e' l) ^ 2 := by
    rw [div_pow, div_le_div_iff₀ he (by positivity)]
    nlinarith
  calc (2 : ℝ) ^ (slU (List.replicate l ())).length ≤ (2 / e l) ^ C := h3 l
    _ ≤ ((2 / e' l) ^ 2) ^ C := pow_le_pow_left₀ (by positivity) hh C
    _ = (2 / e' l) ^ (2 * C) := (pow_mul _ 2 C).symm
end QueryMachines.Bridge
