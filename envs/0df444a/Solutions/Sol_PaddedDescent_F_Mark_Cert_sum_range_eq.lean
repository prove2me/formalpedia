-- Prove2me | solution 1 for PaddedDescent.F.Mark.Cert.sum_range_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T01:43:08.461204+00:00
-- url     : https://prove2.me/submissions/d7c7175d-077b-4020-894e-923651dce7d7

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PaddedDescent_F_Interfaces
import Definitions.Def_PaddedDescent_F_FuelCert
import Definitions.Def_ToTuring_Poly_Digits
import Definitions.Def_PaddedDescent_F_CertMark
import Theorems.Thm_Groundwork_PolyT_congr
import Theorems.Thm_Groundwork_PolyT_map
import Theorems.Thm_Groundwork_PolyT_sum
attribute [local fun_prop] Groundwork.PolyT.map
attribute [local fun_prop] Groundwork.PolyT.sum



set_option autoImplicit false
section
section
open PaddedDescent PaddedDescent.F PaddedDescent.F.Mark PaddedDescent.F.Mark.Cert
open Groundwork Groundwork.Prog Groundwork.Grid
variable {α : Type} [Enc α]
namespace PaddedDescent.F.Mark.Cert
theorem _root_.solution (g : ℕ) (F : ℕ → ℕ → ℕ) : ((List.range g).map fun a => ((List.range a).map fun a' => F a' a).sum).sum =
    ((List.range g).map fun a => (((List.range g).take a).map fun a' => F a' a).sum).sum := by
  congr 1
  refine List.map_congr_left fun a ha => ?_
  rw [List.take_range, min_eq_left (List.mem_range.1 ha).le]
end PaddedDescent.F.Mark.Cert
