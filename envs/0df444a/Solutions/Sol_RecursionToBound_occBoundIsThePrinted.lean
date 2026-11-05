-- Prove2me | solution 1 for RecursionToBound.occBoundIsThePrinted
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:49:31.659525+00:00
-- url     : https://prove2.me/submissions/693d8544-b0c3-4d00-aaae-d97524c7d31d

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_RecursionToBound_Defs
import Definitions.Def_PairsToBound_Arith
import Definitions.Def_SparsificationLemma_Cal_Alpha
import Definitions.Def_SparsificationLemma_Cal_Beta
import Definitions.Def_VariableBound_Paper_Arith
import Definitions.Def_VariableBound_Printed_VariablesA_Setting
import Definitions.Def_VariableBound_Params_Ineq
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.GCongr
import Definitions.Def_RecursionToBound_Numbers
import Theorems.Thm_RecursionToBound_epsOf_pos
import Theorems.Thm_RecursionToBound_epsOf_le_one
import Theorems.Thm_SparsificationLemma_Cal_stAlpha
import Theorems.Thm_SparsificationLemma_Cal_stDegLe
import Theorems.Thm_SparsificationLemma_Cal_stDegSum


set_option autoImplicit false
section
section
open RecursionToBound
open Finset ClauseBound.ParityChecks UniformInK VariableBound.Net SparsificationLemma MainTheoremForms PairsToBound VariableBound.Paper
namespace RecursionToBound
theorem _root_.solution : OccBoundIsThePrinted := by
  intro k r hk h1 h2
  have hε0 := epsOf_pos h1 h2
  have hε1 := epsOf_le_one r
  obtain ⟨-, hα, -, -, -⟩ := Cal.stAlpha k (epsOf r) hk hε0 hε1
  have hs := (Cal.stDegSum (Cal.alphaC k (epsOf r)) k (by omega) (by omega)).2.1
  have hd := Cal.stDegLe k (epsOf r) hk hε0 hε1
  have h3 : (occBound k r : ℝ) ≤ 2 * ((2 + 4 * Cal.alphaC k (epsOf r) * (32 * Cal.alphaC k (epsOf r)) ^ (k - 2) : ℕ) : ℝ) + 2 := by
    unfold occBound thresholds
    exact_mod_cast Nat.add_le_add_right (Nat.mul_le_mul_left 2 hs) 2
  linarith
end RecursionToBound
