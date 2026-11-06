-- Prove2me | solution 1 for RecursionToBound.Correct.countOutput_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T10:34:46.865926+00:00
-- url     : https://prove2.me/submissions/ec138168-fd94-45e3-84b7-3ffed800eab1

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
import Theorems.Thm_RecursionToBound_Correct_occ_le_DeltaOf
import Theorems.Thm_RecursionToBound_Correct_nSat_eq_cntN
import Theorems.Thm_RecursionToBound_Correct_mem_deltas_of
import Theorems.Thm_RecursionToBound_Correct_fitsD_of
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_TM_Run_trans
import Theorems.Thm_PaddedDescent_F_Top_correct
import Theorems.Thm_RecursionWithPieces_countAB
import Theorems.Thm_SparsificationLemma_StepSparsify_count_no_clause
import Theorems.Thm_SparsificationLemma_stLenOfOcc
attribute [local fun_prop] Groundwork.PolyT.length



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
theorem _root_.solution {Idx : Type} [Enc Idx] {S : Solver Idx} {e : ℕ → ℝ} {C₀ : ℕ} (Q : S.Seq e C₀) {k n l : ℕ} {r : ℕ × ℕ} (pad : U) (x : CNode) (hΦ : IsKCNF k n (out x))
    (hb : SparsificationLemma.StepSparsify.DeltaOf n (out x) ≤ occBound k r) (hn : SparsificationLemma.StepSparsify.DeltaOf n (out x) ≤ n + 1) (hL : 29 * LD (SparsificationLemma.StepSparsify.DeltaOf n (out x)) + 19 ≤ n)
    (hpad : 2 ^ needOutputs S k r (Q.idx l) n ≤ pad.length) : countOutput S k pad (Q.idx l) n x = cntN n (out x) := by
  unfold countOutput
  cases hx : out x with
  | nil => exact (SparsificationLemma.StepSparsify.count_no_clause n).symm
  | cons C Φ =>
    rw [← hx]
    have h2 : 2 ≤ SparsificationLemma.StepSparsify.DeltaOf n (out x) := le_max_left _ _
    have hne : (out x).isEmpty = false := by rw [hx]; rfl
    rw [hne, cond_false]
    have hwf : WfL k n [out x] := by
      intro y hy
      rw [List.mem_singleton.1 hy]
      exact hΦ
    exact (RecursionWithPieces.countAB Idx S (fun i => ∃ l, i = Q.idx l) Q.correct k pad (Q.idx l) n (SparsificationLemma.StepSparsify.DeltaOf n (out x)) (out x) ⟨l, rfl⟩ (Q.K_two l)
      hwf (occ_le_DeltaOf hΦ) (stLenOfOcc k n _ (out x) hΦ (occ_le_DeltaOf hΦ)) h2 hL (fitsD_of S (Q.idx l) (mem_deltas_of h2 hb hn) hpad)).trans (nSat_eq_cntN n _)
end RecursionToBound.Correct
