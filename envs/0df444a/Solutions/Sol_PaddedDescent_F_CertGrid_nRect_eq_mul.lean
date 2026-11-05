-- Prove2me | solution 1 for PaddedDescent.F.CertGrid.nRect_eq_mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T01:19:47.541104+00:00
-- url     : https://prove2.me/submissions/8ef90be8-63a9-4514-bddc-7ac4a7d0a1f3

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PaddedDescent_F_Interfaces
import Definitions.Def_PaddedDescent_F_FuelCert
import Definitions.Def_ToTuring_Poly_Digits
import Definitions.Def_ToTuring_Poly_Words
import Definitions.Def_PaddedDescent_F_CertGrid

set_option autoImplicit false
section
section
open PaddedDescent PaddedDescent.F PaddedDescent.F.CertGrid
open Groundwork Groundwork.Prog
variable {α : Type} [Enc α]
namespace PaddedDescent.F.CertGrid
theorem _root_.solution (g : ℕ) : nRect g = g * (g - 1) / 2 * (g * (g - 1) / 2) := by
  unfold nRect
  rw [Nat.choose_two_right, sq]
end PaddedDescent.F.CertGrid
