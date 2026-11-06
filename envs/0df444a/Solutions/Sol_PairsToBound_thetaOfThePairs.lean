-- Prove2me | solution 1 for PairsToBound.thetaOfThePairs
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:10:05.189877+00:00
-- url     : https://prove2.me/submissions/dff987a0-2e08-4dbd-9447-51c6b52d08a5

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PairsToBound_Defs
import Definitions.Def_GeneralPieces_Rec_Seq
import Definitions.Def_GeneralPieces_ThmRunningTime
import Definitions.Def_GeneralPieces_Rec_Chain
import Definitions.Def_GeneralPieces_Rec_Rate
import Definitions.Def_GeneralPieces_Rec_PartB
import Definitions.Def_GeneralPieces_Num_PartA
import Definitions.Def_GeneralPieces_Num_PartAUse
import Definitions.Def_GeneralPieces_Num_Asymptotic
import Definitions.Def_ClauseBound_Alg_Need
import Definitions.Def_PairsToBound_Pairs
import Theorems.Thm_PairsToBound_half_le_inv_sqrt_two
import Theorems.Thm_PairsToBound_inv_between_sqrt
import Theorems.Thm_GeneralPieces_PartA_logK_eq_x
import Theorems.Thm_GeneralPieces_PartA_thmRunningTime_a
import Theorems.Thm_GeneralPieces_thmRunningTime_a
import Theorems.Thm_Groundwork_PolyT_div_pow
import Theorems.Thm_PaddedDescent_F_CertSide_he2
attribute [local fun_prop] Groundwork.PolyT.div_pow
attribute [local fun_prop] PaddedDescent.F.CertSide.he2



set_option autoImplicit false
section
section
open PairsToBound
open Turing Groundwork PaddedDescent.F ClauseBound.Alg ClauseBound.Gen ClauseBound.Gen.Seq Levels.Gen GeneralPieces MainTheoremForms
namespace PairsToBound
theorem _root_.solution : ThetaOfThePairs := by
  intro x₀ l hx
  have hA := PartA.thmRunningTime_a (1 / Real.sqrt 2) x₀ half_le_inv_sqrt_two.1 half_le_inv_sqrt_two.2 hx
  have hlo : (x₀ : ℝ) * 2 ^ l ≤ lg (K x₀ l) := by
    unfold lg
    rw [PartA.logK_eq_x]
    have h' : ((2 ^ l * x₀ : ℕ) : ℝ) ≤ (x x₀ l : ℝ) := by exact_mod_cast PartA.x_ge_pow x₀ l
    push_cast at h'
    linarith
  have hhi : lg (K x₀ l) ≤ (3 * x₀ + 6) * 2 ^ l := by
    unfold lg
    rw [hA.logK]
    have h1 : (0 : ℝ) ≤ l := by positivity
    have h2 : (0 : ℝ) ≤ x₀ := by positivity
    linarith
  obtain ⟨he1, he2⟩ := hA.e_bounds l
  have hs : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have htp : (Real.sqrt 2 ^ l) ^ 2 = 2 ^ l := by rw [← pow_mul, mul_comm, pow_mul, Real.sq_sqrt (by norm_num)]
  have hx0 : (0 : ℝ) < x₀ := by exact_mod_cast (by omega : 0 < x₀)
  obtain ⟨g1, g2⟩ := inv_between_sqrt hx0 (pow_pos hs l) htp hlo hhi
  have hpow : (1 / Real.sqrt 2) ^ l = 1 / Real.sqrt 2 ^ l := by rw [div_pow, one_pow]
  refine ⟨he1, he2, hlo, hhi, ?_, ?_⟩
  · rw [hpow] at he1
    rw [mul_div_assoc]
    linarith
  · rw [hpow] at he2
    rw [mul_div_assoc]
    linarith
end PairsToBound
