-- Prove2me | solution 1 for P2M_GeneralPieces_Rate_K2L_le__0b58532c6456
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T05:16:28.158185+00:00
-- url     : https://prove2.me/submissions/3d26ba9d-94e7-4ec2-9488-39095c75cdf2

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Rec_Chain
import Definitions.Def_GeneralPieces_Num_PartAUse
import Definitions.Def_ClauseBound_Gen_Rate
import Definitions.Def_ClauseBound_Gen_Rate
import Definitions.Def_ClauseBound_Gen_Rate
import Definitions.Def_GeneralPieces_Rec_Rate
import Theorems.Thm_ClauseBound_Gen_Rate_X_cast
import Theorems.Thm_ClauseBound_Gen_Rate_two_lam_le
import Theorems.Thm_GeneralPieces_Chain_K_sq_L_le
import Theorems.Thm_Groundwork_PolyT_all
attribute [local fun_prop] Groundwork.PolyT.all



set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Rate
open Groundwork PaddedDescent.F ClauseBound.Alg ClauseBound.Gen ClauseBound.Gen.Rate Levels.Gen
variable {P : PiecesF} {ρ : ℝ} {c x₀ : ℕ}
namespace GeneralPieces.Rate
theorem _root_.solution (hP : Par P ρ c) (hm : P.m = 1) (hx : 18 ≤ x₀) (l lam B : ℕ) (hlam : 1 ≤ lam) :
    (K x₀ l : ℝ) ^ 2 * lamNextG P (step P x₀ l) lam ≤ (ρ + 3 * zeta l) * ((g x₀ l : ℝ) ^ 4 * lam) +
      c / 4 * (g x₀ l : ℝ) ^ 4 * Real.logb 2 ((K x₀ (l + 1) : ℝ) * (lam + B)) + (K x₀ l : ℝ) ^ 2 := by
  have hlm : (1 : ℝ) ≤ lam := by exact_mod_cast hlam
  have hlog : Real.logb 2 (2 * (lam : ℝ)) ≤ Real.logb 2 ((K x₀ (l + 1) : ℝ) * (lam + B)) := by
    have h : ((2 * lam : ℕ) : ℝ) ≤ ((g x₀ l ^ 2 * (lam + B) : ℕ) : ℝ) := by exact_mod_cast two_lam_le hx l lam B
    rw [X_cast] at h
    push_cast at h
    exact Real.logb_le_logb_of_le (by norm_num) (by positivity) h
  have h1 := Chain.K_sq_L_le hP hm x₀ l lam hx hlam
  have h2 := mul_le_mul_of_nonneg_left hlog (by positivity : 0 ≤ (c : ℝ) / 4 * (g x₀ l : ℝ) ^ 4)
  linarith
end GeneralPieces.Rate
