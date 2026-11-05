-- Prove2me | solution 1 for PaddedDescent.F.SideF.bNext_mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:22:08.431212+00:00
-- url     : https://prove2.me/submissions/64a686c1-5de4-4cc7-b147-a01970ebe26e

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PaddedDescent_F_RebalG
import Definitions.Def_PaddedDescent_F_Price
import Definitions.Def_StepMachines_Prog_SidePresents
import Definitions.Def_NetworkStatements
import Mathlib.Algebra.Polynomial.Coeff
import Definitions.Def_PaddedDescent_F_SideF
import Theorems.Thm_PaddedDescent_F_SideF_Pn_mono

set_option autoImplicit false
section
section
open PaddedDescent PaddedDescent.F PaddedDescent.F.SideF
open Groundwork Groundwork.Prog Groundwork.Grid Finset
namespace PaddedDescent.F.SideF
theorem _root_.solution {K g a b B : ℕ} (h : a ≤ b) : bNext K g a B ≤ bNext K g b B := by
  unfold bNext
  exact Nat.add_le_add (Nat.mul_le_mul_right _ (Pn_mono h))
    (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (Nat.add_le_add_left (Nat.mul_le_mul_left _ h) _)))
end PaddedDescent.F.SideF
