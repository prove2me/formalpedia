-- Prove2me | solution 1 for RecursionToBound.Correct.fitsD_of
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T09:47:22.897216+00:00
-- url     : https://prove2.me/submissions/ed206534-ee4a-459a-b607-6e77564dcf5f

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
import Theorems.Thm_Groundwork_Prog_NetE_le_foldr_max
import Theorems.Thm_Groundwork_TM_Run_trans


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
theorem _root_.solution {Idx : Type} [Enc Idx] (S : Solver Idx) {k n Δ F : ℕ} {r : ℕ × ℕ} (i : Idx) (hΔ : Δ ∈ deltas k r n) (hF : 2 ^ needOutputs S k r i n ≤ F) : FitsD S k i n Δ F := by
  have h1 : needAt S k i n Δ ≤ needOutputs S k r i n := Groundwork.Prog.NetE.le_foldr_max (List.mem_map.2 ⟨Δ, hΔ, rfl⟩)
  have h2 : 2 ^ needAt S k i n Δ ≤ F := (Nat.pow_le_pow_right (by norm_num) h1).trans hF
  have hp : ∀ a : ℕ, a ≤ needAt S k i n Δ → 2 ^ a ≤ F := fun a ha => (Nat.pow_le_pow_right (by norm_num) ha).trans h2
  refine ⟨hp _ ?_, (Nat.lt_size_self _).le.trans (hp _ ?_), (Nat.lt_size_self _).le.trans (hp _ ?_)⟩ <;> (unfold needAt; omega)
end RecursionToBound.Correct
