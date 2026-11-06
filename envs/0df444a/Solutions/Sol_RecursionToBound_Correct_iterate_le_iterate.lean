-- Prove2me | solution 1 for RecursionToBound.Correct.iterate_le_iterate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T09:57:46.101348+00:00
-- url     : https://prove2.me/submissions/d3fcf45d-9aca-46d4-b7e6-a75ad01e0aeb

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_RecursionToBound_Defs
import Definitions.Def_RecursionToBound_Tree
import Definitions.Def_PairsToBound_Width
import Definitions.Def_PairsToBound_Exhaust
import Definitions.Def_SparsificationLemma_StepSparsify
import Definitions.Def_SparsificationLemma_Side
import Definitions.Def_SparsificationLemma_One
import Definitions.Def_SparsificationLemma_Gen
import Definitions.Def_SparsificationLemma_Len
import Definitions.Def_SparsificationLemma_Cal_Facts
import Definitions.Def_SparsificationLemma_Cal_Beta
import Definitions.Def_SparsificationLemma_Cal_Thr
import Definitions.Def_SparsificationLemma_Cal_Alpha
import Definitions.Def_StepSparsify_Walk
import Definitions.Def_UniformInK_Tree_Stack
import Definitions.Def_CountKSat_InOut
import Definitions.Def_CountKSatRate_Walk
import Definitions.Def_CountKSatRate_Brute
import Definitions.Def_RecursionWithPieces_Main
import Definitions.Def_VariableBound_Printed_VariablesA_Level
import Definitions.Def_ClauseBound_Alg_Decode
import Definitions.Def_WidthK_Decode
import Definitions.Def_ToTuring_Poly_NetFun
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Linarith
import Definitions.Def_RecursionToBound_Correct
import Theorems.Thm_RecursionToBound_Correct_le_roundS
import Theorems.Thm_CircuitLowerBound_Tab_Enc_step
import Theorems.Thm_ClauseBound_ParityChecks_Run_Inv_step
import Theorems.Thm_ClauseBound_Part_Lower_step
import Theorems.Thm_CountKSatRate_Top_le_roundS
import Theorems.Thm_GeneralPieces_Pcs_Le_zero
import Theorems.Thm_Groundwork_TM_Run_trans
import Theorems.Thm_PaddedDescent_F_Arith_Inv_step
import Theorems.Thm_VariableBound_Net_Main_val
import Theorems.Thm_WidthK_InvK_step


set_option autoImplicit false
section
section
open RecursionToBound
open Finset Turing Groundwork Groundwork.Prog PaddedDescent PaddedDescent.F CountKSat CountKSatRate ClauseBound.Alg ClauseBound.TopN ClauseBound.ParityChecks UniformInK VariableBound VariableBound.Net SparsificationLemma MainTheoremForms PairsToBound
open PaddedDescent.F.Mark (occ)
open Sat3 (CNF)
open PaddedDescent.F.Mark (WfL nSat)
open Groundwork.Sparsify (PFml leaves round)
open RecursionToBound.Correct
namespace RecursionToBound.Correct
theorem _root_.solution {σ : Type} (step : σ → Option (σ × σ)) (val : σ → ℕ) (st : List σ × ℕ) (i j : ℕ) :
    ((roundS step val)^[i] st).2 ≤ ((roundS step val)^[j + i] st).2 := by
  induction j with
  | zero => rw [Nat.zero_add]
  | succ j ih =>
    rw [Nat.succ_add, Function.iterate_succ_apply']
    exact ih.trans (le_roundS step val _)
end RecursionToBound.Correct
