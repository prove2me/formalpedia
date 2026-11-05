-- Prove2me | solution 1 for PaddedDescent.F.Price.U_side_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T22:14:18.742187+00:00
-- url     : https://prove2.me/submissions/939daf0a-5e44-4d2b-ac80-53e443c5c83d

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PaddedDescent_F_Prog
import Definitions.Def_StepMachines_Prog_SidePresents
import Definitions.Def_NetworkStatements
import Mathlib.Algebra.Polynomial.Coeff
import Definitions.Def_PaddedDescent_F_Price
import Theorems.Thm_PaddedDescent_F_Price_min_price_nat
import Theorems.Thm_Groundwork_Grid_U_sideN_col
import Theorems.Thm_Groundwork_Grid_U_sideN_row


set_option autoImplicit false
section
section
set_option exponentiation.threshold 1024
open PaddedDescent PaddedDescent.F PaddedDescent.F.Price
open Groundwork Groundwork.Prog Groundwork.Grid
namespace PaddedDescent.F.Price
theorem _root_.solution (g n : ℕ) (Rm : Inst (Fin (g * g)) (List Bool)) (y : ℕ) :
    (sideN g (decide (priceCol g n y < priceRow g n y)) n Rm y).U ≤ Ubar g n := by
  have h := min_price_nat g n y
  by_cases hlt : priceCol g n y < priceRow g n y
  · rw [decide_eq_true hlt, U_sideN_col]
    rwa [min_eq_right hlt.le] at h
  · rw [decide_eq_false hlt, U_sideN_row]
    rwa [min_eq_left (by omega)] at h
end PaddedDescent.F.Price
