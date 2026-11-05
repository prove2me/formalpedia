-- Prove2me | solution 1 for PaddedDescent.F.Price.min_price_nat
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T22:11:13.329194+00:00
-- url     : https://prove2.me/submissions/b7bbee5e-97b3-4e03-9d0f-ef0899b390e8

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PaddedDescent_F_Prog
import Definitions.Def_StepMachines_Prog_SidePresents
import Definitions.Def_NetworkStatements
import Mathlib.Algebra.Polynomial.Coeff
import Definitions.Def_PaddedDescent_F_Price
import Theorems.Thm_PaddedDescent_F_Price_rho_lt
import Theorems.Thm_Groundwork_Prog_min_price_le


set_option autoImplicit false
section
section
set_option exponentiation.threshold 1024
open PaddedDescent PaddedDescent.F PaddedDescent.F.Price
open Groundwork Groundwork.Prog Groundwork.Grid
namespace PaddedDescent.F.Price
theorem _root_.solution (g n y : ℕ) : g ^ 2 * (g - 1) * n + min (priceRow g n y) (priceCol g n y) ≤ Ubar g n := by
  have h := min_price_le g n y
  have hρ := rho_lt
  have h0 : (0 : ℝ) ≤ (g : ℝ) ^ 4 * n := by positivity
  have h1 : ((min (priceRow g n y) (priceCol g n y) : ℕ) : ℝ) ≤ 717 / 800 * ((g : ℝ) ^ 4 * n) + (g : ℝ) ^ 4 / 2 := by
    nlinarith
  have h2 : 800 * min (priceRow g n y) (priceCol g n y) ≤ 717 * g ^ 4 * n + 400 * g ^ 4 := by
    have : (800 : ℝ) * ((min (priceRow g n y) (priceCol g n y) : ℕ) : ℝ) ≤ 717 * (g : ℝ) ^ 4 * n + 400 * (g : ℝ) ^ 4 := by
      linarith
    exact_mod_cast this
  unfold Ubar
  generalize min (priceRow g n y) (priceCol g n y) = p at h2
  generalize 717 * g ^ 4 * n = A at h2 ⊢
  generalize g ^ 4 = D at h2 ⊢
  omega
end PaddedDescent.F.Price
