-- Prove2me | solution 1 for PaddedDescent.F.SideF.capM_mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:22:01.624104+00:00
-- url     : https://prove2.me/submissions/e2b3e1c8-1bc3-4d87-acd2-f9882cbe183b

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
theorem _root_.solution {g a b : ℕ} (h : a ≤ b) : capM g a ≤ capM g b := by
  unfold capM
  exact Nat.add_le_add (Nat.mul_le_mul_left _ h) (Nat.mul_le_mul_left _ h)
end PaddedDescent.F.SideF
