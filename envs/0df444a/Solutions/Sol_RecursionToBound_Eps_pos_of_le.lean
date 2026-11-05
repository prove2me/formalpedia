-- Prove2me | solution 1 for RecursionToBound.Eps.pos_of_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T02:40:27.0118+00:00
-- url     : https://prove2.me/submissions/802e895b-ebf1-41de-8e1f-96789af021f9

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

set_option autoImplicit false
section
section
open RecursionToBound
open Finset Turing Groundwork Groundwork.Prog PaddedDescent PaddedDescent.F CountKSat CountKSatRate ClauseBound.Alg ClauseBound.TopN ClauseBound.ParityChecks UniformInK VariableBound VariableBound.Net SparsificationLemma MainTheoremForms PairsToBound
open PaddedDescent.F.Mark (occ)
open Sat3 (CNF)
open RecursionToBound.Eps
namespace RecursionToBound.Eps
theorem _root_.solution {r : ℕ × ℕ} {e : ℝ} (he : 0 < e) (h : e ≤ (r.1 : ℝ) / (r.2 : ℝ)) : 0 < r.1 ∧ 0 < r.2 := by
  have hp : 0 < (r.1 : ℝ) / (r.2 : ℝ) := lt_of_lt_of_le he h
  constructor
  · rcases Nat.eq_zero_or_pos r.1 with h0 | h0
    · rw [h0, Nat.cast_zero, zero_div] at hp
      exact absurd hp (lt_irrefl _)
    · exact h0
  · rcases Nat.eq_zero_or_pos r.2 with h0 | h0
    · rw [h0, Nat.cast_zero, div_zero] at hp
      exact absurd hp (lt_irrefl _)
    · exact h0
end RecursionToBound.Eps
