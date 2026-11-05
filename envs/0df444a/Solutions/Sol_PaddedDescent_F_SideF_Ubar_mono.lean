-- Prove2me | solution 1 for PaddedDescent.F.SideF.Ubar_mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:22:00.542193+00:00
-- url     : https://prove2.me/submissions/5991331a-08a7-4b53-aa85-23e1c9fc6ecf

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PaddedDescent_F_RebalG
import Definitions.Def_PaddedDescent_F_Price
import Definitions.Def_StepMachines_Prog_SidePresents
import Definitions.Def_NetworkStatements
import Mathlib.Algebra.Polynomial.Coeff
import Definitions.Def_PaddedDescent_F_SideF

set_option autoImplicit false
section
section
open PaddedDescent PaddedDescent.F PaddedDescent.F.SideF
open Groundwork Groundwork.Prog Groundwork.Grid Finset
namespace PaddedDescent.F.SideF
theorem _root_.solution {g a b : ℕ} (h : a ≤ b) : Ubar g a ≤ Ubar g b := by
  unfold Ubar
  have h1 : g ^ 2 * (g - 1) * a ≤ g ^ 2 * (g - 1) * b := Nat.mul_le_mul_left _ h
  have h2 : 717 * g ^ 4 * a / 800 ≤ 717 * g ^ 4 * b / 800 := Nat.div_le_div_right (Nat.mul_le_mul_left _ h)
  omega
end PaddedDescent.F.SideF
