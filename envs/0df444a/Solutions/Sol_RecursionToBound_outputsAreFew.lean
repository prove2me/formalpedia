-- Prove2me | solution 1 for RecursionToBound.outputsAreFew
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T08:16:07.606418+00:00
-- url     : https://prove2.me/submissions/271709f7-4a35-4c58-94fd-b285d46eb38a

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_RecursionToBound_Defs
import Definitions.Def_SparsificationLemma_StepSparsify
import Definitions.Def_SparsificationLemma_Side
import Definitions.Def_SparsificationLemma_One
import Definitions.Def_SparsificationLemma_Cal_Facts
import Definitions.Def_StepSparsify_CalLeaves
import Definitions.Def_VariableBound_Printed_VariablesA_Level
import Definitions.Def_VariableBound_Printed_VariablesA_Main
import Definitions.Def_ClauseBound_Alg_Decode
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Definitions.Def_RecursionToBound_Tree
import Theorems.Thm_RecursionToBound_Eps_pos
import Theorems.Thm_RecursionToBound_Eps_le_one
import Theorems.Thm_RecursionToBound_Eps_cast
import Theorems.Thm_RecursionToBound_Eps_pos_of_le
import Theorems.Thm_Groundwork_TM_Run_trans
import Theorems.Thm_SparsificationLemma_StepSparsify_outputs_le


set_option autoImplicit false
section
section
open RecursionToBound
open Finset Turing Groundwork Groundwork.Prog PaddedDescent PaddedDescent.F CountKSat CountKSatRate ClauseBound.Alg ClauseBound.TopN ClauseBound.ParityChecks UniformInK VariableBound VariableBound.Net SparsificationLemma MainTheoremForms PairsToBound
open PaddedDescent.F.Mark (occ)
open Sat3 (CNF)
namespace RecursionToBound
theorem _root_.solution : OutputsAreFew := by
  intro k n r e ψ hk he0 he1 hlo hhi hψ
  obtain ⟨h1, h2⟩ := Eps.pos_of_le he0 hlo
  have hc := Eps.cast r
  have a1 : e ≤ ((epsOf r : ℚ) : ℝ) := by
    rw [hc]
    exact le_min hlo he1
  have a2 : ((epsOf r : ℚ) : ℝ) ≤ 2 * e := by
    rw [hc]
    exact (min_le_left _ _).trans hhi
  have a3 : ((epsOf r : ℚ) : ℝ) ≤ 1 := by
    rw [hc]
    exact min_le_right _ _
  exact ⟨a1, a2, a3, SparsificationLemma.StepSparsify.outputs_le hk (Eps.pos h1 h2) (Eps.le_one r) hψ,
    Real.rpow_le_rpow_of_exponent_le one_le_two (mul_le_mul_of_nonneg_right a2 (Nat.cast_nonneg n))⟩
end RecursionToBound
