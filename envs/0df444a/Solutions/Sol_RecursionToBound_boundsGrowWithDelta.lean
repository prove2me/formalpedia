-- Prove2me | solution 1 for RecursionToBound.boundsGrowWithDelta
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T01:44:17.836924+00:00
-- url     : https://prove2.me/submissions/c513098d-dce9-45fb-a61f-cb739cf436cd

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
import Theorems.Thm_RecursionToBound_LD_mono
import Theorems.Thm_RecursionToBound_objMax_mono

set_option autoImplicit false
section
section
open RecursionToBound
open Finset ClauseBound.ParityChecks UniformInK VariableBound.Net SparsificationLemma MainTheoremForms PairsToBound VariableBound.Paper
namespace RecursionToBound
theorem _root_.solution : BoundsGrowWithDelta := by
  intro k K n Δ Δ' h
  have hLD := LD_mono h
  have hsb : sbMax Δ ≤ sbMax Δ' := by
    unfold sbMax
    exact Nat.mul_le_mul (Nat.mul_le_mul_left 32 h) hLD
  have htb : tbMax n Δ ≤ tbMax n Δ' := by
    unfold tbMax
    have := Nat.clog_mono_right 2 (Nat.mul_le_mul_right n h)
    omega
  refine ⟨?_, ?_, ?_, hsb⟩
  · unfold UbD
    have h1 : Nat.clog 2 (96 * Δ * LD Δ) ≤ Nat.clog 2 (96 * Δ' * LD Δ') := Nat.clog_mono_right 2 (Nat.mul_le_mul (Nat.mul_le_mul_left 96 h) hLD)
    exact Nat.add_le_add_right (Nat.add_le_add (Nat.mul_le_mul_left _ (Nat.add_le_add_left hLD n)) (Nat.mul_le_mul_left _ h1)) _
  · unfold PbD PD
    refine Nat.ceil_mono ?_
    unfold P0
    have a1 : (Δ : ℚ) ≤ Δ' := by exact_mod_cast h
    have a2 : (tbMax n Δ : ℚ) ≤ tbMax n Δ' := by exact_mod_cast htb
    have a3 : (sbMax Δ : ℚ) ≤ sbMax Δ' := by exact_mod_cast hsb
    gcongr
  · unfold nPrMax PaddedDescent.F.Mark.nProf
    exact Nat.pow_le_pow_left (Nat.succ_le_succ (objMax_mono n h)) _
end RecursionToBound
