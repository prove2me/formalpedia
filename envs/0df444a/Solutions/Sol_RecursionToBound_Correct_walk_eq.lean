-- Prove2me | solution 1 for RecursionToBound.Correct.walk_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T10:30:25.134444+00:00
-- url     : https://prove2.me/submissions/dfb73eec-2bf0-4b60-9592-cddd0d0be53c

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
import Theorems.Thm_RecursionToBound_Correct_iterate_le_sum
import Theorems.Thm_RecursionToBound_Correct_depth_le
import Theorems.Thm_CountKSatRate_Top_iterate_le_sum
import Theorems.Thm_CountKSatRate_stRoundS
import Theorems.Thm_GeneralPieces_Pcs_Le_sum
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_PolyT_map
import Theorems.Thm_Groundwork_PolyT_sum
import Theorems.Thm_Groundwork_TM_Run_trans
import Theorems.Thm_SparsificationLemma_Cal_stThrCal
import Theorems.Thm_SparsificationLemma_stCountOfExactlyOne
import Theorems.Thm_SparsificationLemma_stExactlyOne
import Theorems.Thm_SparsificationLemma_stOutputsSame
import Theorems.Thm_SparsificationLemma_stTreeG
import Theorems.Thm_StepSparsify_stWalkSG
import Theorems.Thm_UniformInK_stStateLenU
import Theorems.Thm_VariableBound_Net_Main_val
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
theorem _root_.solution {α k n m : ℕ} {ψ : PFml} (hk : 2 ≤ k) (hα : k ^ 2 ≤ α) (hψ : IsKCNF k n ψ) (hm : ψ.length ≤ m) (pad : U) (val : CNode → ℕ)
    (h1 : 2 * (leaves (stepC (Cal.thetaC α) k) (bsumU (32 * α) k * n) (rootC (List.replicate n (), ψ))).length ≤ pad.length + 1)
    (h2 : stackLenCU k (32 * α) n m ≤ pad.length)
    (h3 : ((leaves (stepC (Cal.thetaC α) k) (bsumU (32 * α) k * n) (rootC (List.replicate n (), ψ))).map val).sum < 2 ^ (n + 1)) :
    _root_.StepSparsify.walkSG (Cal.thetaC α) k pad val (rootC (List.replicate n (), ψ)) =
      ((leaves (stepC (Cal.thetaC α) k) (bsumU (32 * α) k * n) (rootC (List.replicate n (), ψ))).map val).sum := by
  have hα1 : 1 ≤ α := le_trans (Nat.one_le_pow _ _ (by omega)) hα
  obtain ⟨-, t2, -, t4⟩ := stTreeG stExactlyOne stCountOfExactlyOne stOutputsSame k α n (bsumU (32 * α) k * n) (Cal.thetaC α) (Cal.betaC α) (by omega) hα
    (Cal.stThrCal α k hα1) (depth_le hα1 hk n) ψ hψ
  obtain ⟨r, hr⟩ : ∃ r, r = rootC (List.replicate n (), ψ) := ⟨_, rfl⟩
  rw [← hr] at t2 t4 h1 h3 ⊢
  have hleaf : ∀ x ∈ leaves (stepC (Cal.thetaC α) k) (bsumU (32 * α) k * n) r, stepC (Cal.thetaC α) k x = none := fun x hx => (t2 x hx).1
  refine _root_.StepSparsify.stWalkSG (Cal.thetaC α) k pad val r (bsumU (32 * α) k * n) hleaf h1 fun i => le_trans ?_ h2
  obtain ⟨s1, s2⟩ := t4 i
  have hc : ((roundS (stepC (Cal.thetaC α) k) val)^[i] ([r], 0)).2 < 2 ^ (n + 1) := lt_of_le_of_lt (iterate_le_sum _ val _ r hleaf i) h3
  have e := stRoundS _ (stepC (Cal.thetaC α) k) val i [r] []
  rw [List.map_nil, List.sum_nil] at e
  rw [e] at hc ⊢
  exact stStateLenU k (32 * α) n m _ _ s1 (fun x hx => ⟨(s2 x hx).1.trans (Nat.mul_le_mul_right _ hm), (s2 x hx).2⟩) hc
end RecursionToBound.Correct
