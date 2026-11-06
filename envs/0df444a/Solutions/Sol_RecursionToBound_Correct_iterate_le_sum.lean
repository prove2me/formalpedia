-- Prove2me | solution 1 for RecursionToBound.Correct.iterate_le_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T10:13:00.004582+00:00
-- url     : https://prove2.me/submissions/4dd1429b-24c2-4163-8f11-54afb21b1ba6

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
import Theorems.Thm_RecursionToBound_Correct_iterate_le_iterate
import Theorems.Thm_CircuitLowerBound_Tab_Enc_step
import Theorems.Thm_ClauseBound_Inst_Half_CertSmall_d
import Theorems.Thm_ClauseBound_ParityChecks_Run_Inv_step
import Theorems.Thm_ClauseBound_Part_Lower_step
import Theorems.Thm_CountKSatRate_Top_iterate_le_iterate
import Theorems.Thm_CountKSatRate_stRoundSEnd
import Theorems.Thm_GeneralPieces_Pcs_Le_sum
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_PolyT_map
import Theorems.Thm_Groundwork_PolyT_sum
import Theorems.Thm_PaddedDescent_F_Arith_Inv_step
import Theorems.Thm_VariableBound_Net_Main_val
import Theorems.Thm_WidthK_InvK_step
attribute [local fun_prop] Groundwork.PolyT.length
attribute [local fun_prop] Groundwork.PolyT.map
attribute [local fun_prop] Groundwork.PolyT.sum



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
theorem _root_.solution {σ : Type} (step : σ → Option (σ × σ)) (val : σ → ℕ) (d : ℕ) (s : σ)
    (hd : ∀ x ∈ leaves step d s, step x = none) (i : ℕ) : ((roundS step val)^[i] ([s], 0)).2 ≤ ((leaves step d s).map val).sum := by
  have h := iterate_le_iterate step val ([s], 0) i (2 * (leaves step d s).length - 1)
  rwa [stRoundSEnd σ step val d s hd _ (Nat.le_add_right _ _)] at h
end RecursionToBound.Correct
