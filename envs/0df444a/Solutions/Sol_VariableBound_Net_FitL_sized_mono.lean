-- Prove2me | solution 1 for VariableBound.Net.FitL.sized_mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T06:36:10.04309+00:00
-- url     : https://prove2.me/submissions/2235c3a0-1632-4fb0-9e11-895e61b262c7

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_VariableBound_Net_Defs
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.NormNum
import Definitions.Def_VariableBound_Net_Fit
import Theorems.Thm_Groundwork_TM_Run_trans


set_option autoImplicit false
section
section
open VariableBound VariableBound.Net VariableBound.Net.FitL
open Groundwork PaddedDescent.F
open PaddedDescent.F.Mark (qv WfL occ nProf)
open ClauseBound.ParityChecks (LD)
namespace VariableBound.Net.FitL
theorem _root_.solution {J σ τ : Type} [Fintype J] [LinearOrder J] {N : Network J σ τ} {P P' B B' : ℕ} (h : N.Sized P B) (hP : P ≤ P') (hB : B ≤ B') : N.Sized P' B' where
  card_S a := (h.card_S a).trans (Nat.pow_le_pow_right (by norm_num) hP)
  c_symm := h.c_symm
  sum_c a := (h.sum_c a).trans hP
  card_lab := h.card_lab
  abs_W a z := (h.abs_W a z).trans (pow_le_pow_right₀ (by norm_num) hB)
  abs_f a b z θ := (h.abs_f a b z θ).trans (pow_le_pow_right₀ (by norm_num) hB)
  abs_Ψ a b z z' hab := (h.abs_Ψ a b z z' hab).trans (pow_le_pow_right₀ (by norm_num) hB)
end VariableBound.Net.FitL
