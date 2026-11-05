-- Prove2me | solution 1 for PaddedDescent.F.SideF.Pn_mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T01:41:05.581379+00:00
-- url     : https://prove2.me/submissions/a639c966-f89f-46aa-8e54-3fbc544295c2

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
theorem _root_.solution {g a b : ℕ} (h : a ≤ b) : Pn g a ≤ Pn g b := Nat.mul_le_mul_left _ h
end PaddedDescent.F.SideF
