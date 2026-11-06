-- Prove2me | solution 1 for RecursionWithPieces.tiedAt_of
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T12:31:42.234774+00:00
-- url     : https://prove2.me/submissions/d986bab8-c886-401e-b060-618a20b044c7

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_UniformInKStatement
import Definitions.Def_RecursionWithPieces_Defs
import Definitions.Def_UniformInK_Top_Defs
import Definitions.Def_RecursionWithPieces_Master
import Definitions.Def_GeneralPieces_Main
import Definitions.Def_GeneralPieces_Tied_Bound
import Definitions.Def_GeneralPieces_Top_CaseI
import Definitions.Def_GeneralPieces_Num_TopDisplay
import Definitions.Def_GeneralPieces_Num_PartAUse
import Definitions.Def_GeneralPieces_ThmRunningTime
import Definitions.Def_ClauseBound_Alg_Need
import Definitions.Def_SparsifyThenCount_Main
import Definitions.Def_SparsifyThenCount_PlanUsed
import Definitions.Def_SparsifyThenCount_Correct
import Definitions.Def_SparsifyThenCount_CorrectB
import Definitions.Def_SparsifyThenCount_Tied
import Definitions.Def_VariableBound_MainPrinted
import Definitions.Def_VariableBound_Printed_Tied
import Definitions.Def_VariableBound_Paper_Decide
import Definitions.Def_VariableBound_StepParity
import Definitions.Def_VariableBound_Family_Main
import Definitions.Def_VariableBound_Field_Family
import Definitions.Def_VariableBound_Params_Spec
import Definitions.Def_VariableBound_Params_Ineq
import Definitions.Def_VariableBound_Search_Correct
import Definitions.Def_VariableBound_Net_Main
import Definitions.Def_VariableBound_Net_Ev
import Definitions.Def_VariableBound_Count_Correct
import Definitions.Def_VariableBound_Top_Budget
import Definitions.Def_VariableBound_Top_ArithPlan
import Definitions.Def_StepSparsify_WalkCount
import Definitions.Def_StepSparsify_CalServes
import Definitions.Def_UniformInK_Top_Correct
import Definitions.Def_UniformInK_Top_CorrectB
import Definitions.Def_UniformInK_Top_Leaves
import Definitions.Def_ClauseBound_MainBoth
import Definitions.Def_ClauseBound_Both_TimeM
import Definitions.Def_ClauseBound_Alg_TopVal
import Definitions.Def_ClauseBound_Alg_Decode
import Definitions.Def_CountKSatRate_Pad
import Definitions.Def_CountKSatRate_Brute
import Definitions.Def_RecursionWithPieces_Main
import Theorems.Thm_RecursionWithPieces_algAB
import Theorems.Thm_ClauseBound_Both_rN_nonneg
import Theorems.Thm_ClauseBound_Both_rPow_nonneg
import Theorems.Thm_CountKSatRate_stPaddedW
import Theorems.Thm_GeneralPieces_thmRunningTime_b_tied
import Theorems.Thm_GeneralPieces_thmRunningTime_c_m_tied
import Theorems.Thm_P2M_GeneralPieces_x_Of_ge_2a558e3f9765
import Theorems.Thm_P2M_GeneralPieces_x_Of_pow_e8c07e605600
import Theorems.Thm_P2M_Groundwork_PB_id__8af0b594aff4
import Theorems.Thm_P2M_Groundwork_PolyT_id__1c5d0f44cc8f
import Theorems.Thm_RecursionWithPieces_master_of_isPiecesB
import Theorems.Thm_SparsifyThenCount_stPlanUsed
import Theorems.Thm_SparsifyThenCount_stRateZero
import Theorems.Thm_VariableBound_Decide_polyT_bitOf
import Theorems.Thm_VariableBound_Net_Main_val
import Theorems.Thm_VariableBound_tied_of_alg
attribute [local fun_prop] P2M_Groundwork_PolyT_id__1c5d0f44cc8f



set_option autoImplicit false
section
section
open RecursionWithPieces
open Groundwork PaddedDescent PaddedDescent.F CountKSat CountKSatRate ClauseBound.Alg ClauseBound.Both ClauseBound.ParityChecks ClauseBound.TopN UniformInK VariableBound VariableBound.Decide SparsifyThenCount GeneralPieces
namespace RecursionWithPieces
theorem _root_.solution {Θ : ℕ → ℕ → ℕ → ℕ} {Lc : ℕ → ℕ → ℕ} (hΘ : StepSparsify.Serves Θ Lc) {c : ℕ} {P₀ : PiecesF} {A : (lam : ℕ) → ℕ → Pieces.Four lam} {val : AppRunningTime.ValQ → ℤ}
    (h : Tied.IsPiecesB c P₀ A val) : TiedAt Θ c P₀ A val := by
  have hA : Alg (SatK.rN 1 (1 / 2)) (SatM.rPow (1 / 2)) (fnAll Θ P₀ val c) (expAll P₀ val c) := master_of_isPiecesB (algAB Θ Lc hΘ) h
  obtain ⟨C₀, hC⟩ := thmRunningTime_b_tied c
  exact ⟨h, ⟨C₀, hC _ _ P₀ A val h.1 (x₀Of_ge c) (x₀Of_pow c)⟩, thmRunningTime_c_m_tied h.1, hA, tied_of_alg stPaddedW hA PolyT.id' (rN_nonneg _) (rPow_nonneg _),
    tied_of_alg stPaddedW hA polyT_bitOf (rN_nonneg _) (rPow_nonneg _), stPlanUsed _ _ _ _ _ _ _ hA stRateZero⟩
end RecursionWithPieces
