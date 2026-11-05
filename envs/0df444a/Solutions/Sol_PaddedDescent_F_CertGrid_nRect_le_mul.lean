-- Prove2me | solution 1 for PaddedDescent.F.CertGrid.nRect_le_mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:10:18.286273+00:00
-- url     : https://prove2.me/submissions/7fba0bc1-72e1-4f87-942f-c74515da37ce

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PaddedDescent_F_Interfaces
import Definitions.Def_PaddedDescent_F_FuelCert
import Definitions.Def_ToTuring_Poly_Digits
import Definitions.Def_ToTuring_Poly_Words
import Definitions.Def_PaddedDescent_F_CertGrid
import Theorems.Thm_PaddedDescent_F_CertGrid_nRect_eq_mul
import Theorems.Thm_Groundwork_TM_Run_trans


set_option autoImplicit false
section
section
open PaddedDescent PaddedDescent.F PaddedDescent.F.CertGrid
open Groundwork Groundwork.Prog
variable {α : Type} [Enc α]
namespace PaddedDescent.F.CertGrid
theorem _root_.solution (g : ℕ) : nRect g ≤ g * g * (g * g) := by
  rw [nRect_eq_mul]
  have h : g * (g - 1) / 2 ≤ g * g := (Nat.div_le_self _ _).trans (Nat.mul_le_mul_left _ (Nat.sub_le _ _))
  exact Nat.mul_le_mul h h
end PaddedDescent.F.CertGrid
