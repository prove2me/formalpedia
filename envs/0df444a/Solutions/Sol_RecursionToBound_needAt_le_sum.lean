-- Prove2me | solution 1 for RecursionToBound.needAt_le_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T08:10:22.325442+00:00
-- url     : https://prove2.me/submissions/4214b088-4d92-4678-9030-8e9a459c1aaa

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_RecursionToBound_Defs
import Definitions.Def_VariableBound_Top_ArithDefs
import Definitions.Def_RecursionToBound_Numbers
import Definitions.Def_VariableBound_Top_ArithNat
import Definitions.Def_UniformInK_Top_ArithMaster
import Definitions.Def_VariableBound_Net_Main
import Definitions.Def_VariableBound_Net_StepCost
import Definitions.Def_VariableBound_Printed_VariablesA_Level
import Definitions.Def_VariableBound_Printed_VariablesA_Arith
import Definitions.Def_VariableBound_Paper_Arith
import Definitions.Def_ClauseBound_Alg_TopArith
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.GCongr
import Definitions.Def_RecursionToBound_OneOutput
import Theorems.Thm_RecursionToBound_lamS_mono
import Theorems.Thm_RecursionToBound_size_nPrMax_le
import Theorems.Thm_RecursionToBound_boundsGrowWithDelta
import Theorems.Thm_RecursionToBound_objMax_mono
import Theorems.Thm_VariableBound_Net_Main_nPrMax
import Theorems.Thm_VariableBound_Net_Main_size


set_option autoImplicit false
section
section
open RecursionToBound
open Groundwork PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.TopArith ClauseBound.ParityChecks UniformInK VariableBound.Net MainTheoremForms VariableBound.Paper
namespace RecursionToBound
theorem _root_.solution {Idx : Type} [Enc Idx] (S : Solver Idx) (i : Idx) (k n : ℕ) {Δ D : ℕ} (h : Δ ≤ D) :
    needAt S k i n Δ ≤ 3 * S.K i ^ 8 * (S.K i).size + PbD (S.K i) n D * (2 * (3 * S.K i ^ 8) / S.K i + 1) +
      (S.K i - 1) * lamS (S.K i) (3 * S.K i ^ 8) (UbD k (S.K i) n D) (PbD (S.K i) n D) +
      S.need (i, List.replicate (lamS (S.K i) (3 * S.K i ^ 8) (UbD k (S.K i) n Δ) (PbD (S.K i) n Δ)) (),
        List.replicate (bitsS (S.K i) (3 * S.K i ^ 8) (PbD (S.K i) n Δ) (BbD k n)) ()) +
      3 * S.K i ^ 8 * (3 * S.K i ^ 8) * 2 * Nat.size (objMax n D) +
      (Nat.size (8 * (10 * n + 1) * (sbMax D + 1) * (Nat.size (D * n) + 2) + 8) + 1) := by
  obtain ⟨hU, hP, -, hsb⟩ := boundsGrowWithDelta k (S.K i) n Δ D h
  have a2 : PbD (S.K i) n Δ * (2 * (3 * S.K i ^ 8) / S.K i + 1) ≤ PbD (S.K i) n D * (2 * (3 * S.K i ^ 8) / S.K i + 1) := Nat.mul_le_mul_right _ hP
  have a3 : (S.K i - 1) * lamS (S.K i) (3 * S.K i ^ 8) (UbD k (S.K i) n Δ) (PbD (S.K i) n Δ) ≤
      (S.K i - 1) * lamS (S.K i) (3 * S.K i ^ 8) (UbD k (S.K i) n D) (PbD (S.K i) n D) := Nat.mul_le_mul_left _ (lamS_mono _ _ hU hP)
  have a4 := size_nPrMax_le (S.K i) n Δ
  have a5 : 3 * S.K i ^ 8 * (3 * S.K i ^ 8) * 2 * Nat.size (objMax n Δ) ≤ 3 * S.K i ^ 8 * (3 * S.K i ^ 8) * 2 * Nat.size (objMax n D) :=
    Nat.mul_le_mul_left _ (Nat.size_le_size (objMax_mono n h))
  have a6 : Nat.size (8 * (10 * n + 1) * (sbMax Δ + 1) * (Nat.size (Δ * n) + 2) + 8) ≤ Nat.size (8 * (10 * n + 1) * (sbMax D + 1) * (Nat.size (D * n) + 2) + 8) :=
    Nat.size_le_size (Nat.add_le_add_right (Nat.mul_le_mul (Nat.mul_le_mul_left _ (Nat.succ_le_succ hsb)) (Nat.add_le_add_right (Nat.size_le_size (Nat.mul_le_mul_right n h)) 2)) 8)
  unfold needAt needNet
  generalize S.need _ = nd
  generalize 3 * S.K i ^ 8 * (S.K i).size = x1
  generalize PbD (S.K i) n Δ * (2 * (3 * S.K i ^ 8) / S.K i + 1) = x2 at a2 ⊢
  generalize PbD (S.K i) n D * (2 * (3 * S.K i ^ 8) / S.K i + 1) = y2 at a2 ⊢
  generalize (S.K i - 1) * lamS (S.K i) (3 * S.K i ^ 8) (UbD k (S.K i) n Δ) (PbD (S.K i) n Δ) = x3 at a3 ⊢
  generalize (S.K i - 1) * lamS (S.K i) (3 * S.K i ^ 8) (UbD k (S.K i) n D) (PbD (S.K i) n D) = y3 at a3 ⊢
  generalize Nat.size (nPrMax (S.K i) n Δ) = x4 at a4 ⊢
  generalize 3 * S.K i ^ 8 * (3 * S.K i ^ 8) * 2 * Nat.size (objMax n Δ) = x5 at a4 a5
  generalize 3 * S.K i ^ 8 * (3 * S.K i ^ 8) * 2 * Nat.size (objMax n D) = y5 at a5 ⊢
  generalize Nat.size (8 * (10 * n + 1) * (sbMax Δ + 1) * (Nat.size (Δ * n) + 2) + 8) = x6 at a6 ⊢
  generalize Nat.size (8 * (10 * n + 1) * (sbMax D + 1) * (Nat.size (D * n) + 2) + 8) = y6 at a6 ⊢
  omega
end RecursionToBound
