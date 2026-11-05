-- Prove2me | solution 1 for PaddedDescent.F.Price.rho_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T22:07:51.027456+00:00
-- url     : https://prove2.me/submissions/1ffe9085-3ee3-420f-b402-5389faa556e4

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PaddedDescent_F_Prog
import Definitions.Def_StepMachines_Prog_SidePresents
import Definitions.Def_NetworkStatements
import Mathlib.Algebra.Polynomial.Coeff
import Definitions.Def_PaddedDescent_F_Price

set_option autoImplicit false
section
section
set_option exponentiation.threshold 1024
open PaddedDescent PaddedDescent.F PaddedDescent.F.Price
open Groundwork Groundwork.Prog Groundwork.Grid
namespace PaddedDescent.F.Price
theorem _root_.solution : ρ < 717 / 800 := by
  have h : Real.logb 2 ((12 : ℝ) ^ 200) < Real.logb 2 ((2 : ℝ) ^ 717) :=
    Real.logb_lt_logb (by norm_num) (by norm_num) (by norm_num)
  rw [Real.logb_pow, Real.logb_pow, Real.logb_self_eq_one (by norm_num)] at h
  unfold ρ
  push_cast at h
  linarith
end PaddedDescent.F.Price
