-- Prove2me | solution 1 for PaddedDescent.F.Mark.Cert.mu_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:25:38.320638+00:00
-- url     : https://prove2.me/submissions/3d4428eb-ac0a-4501-808d-cc26ef9dc2fe

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PaddedDescent_F_Interfaces
import Definitions.Def_PaddedDescent_F_FuelCert
import Definitions.Def_ToTuring_Poly_Digits
import Definitions.Def_PaddedDescent_F_CertMark
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length



set_option autoImplicit false
section
section
open PaddedDescent PaddedDescent.F PaddedDescent.F.Mark PaddedDescent.F.Mark.Cert
open Groundwork Groundwork.Prog Groundwork.Grid
variable {α : Type} [Enc α]
namespace PaddedDescent.F.Mark.Cert
theorem _root_.solution (g : ℕ) (Ls : List Fml) (y a b i : ℕ) : mu g Ls y a b i ≤ (cls Ls).length := by
  unfold mu digit; exact Nat.le_of_lt_succ (Nat.mod_lt _ (Nat.succ_pos _))
end PaddedDescent.F.Mark.Cert
