-- Prove2me | solution 1 for WidthK.ProgMain.nf_length_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T19:37:42.868909+00:00
-- url     : https://prove2.me/submissions/02426140-c642-4d93-9e8e-7d5fd95d5739

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SparsifyWidthK_Interfaces
import Mathlib.Tactic.Linarith
import Definitions.Def_SparsifyWidthK_ProgMain
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length



set_option autoImplicit false
section
section
open WidthK WidthK.ProgMain
open Finset Groundwork Groundwork.Sparsify WidthK.Prog
namespace WidthK.ProgMain
theorem _root_.solution {s : PFml} (hs : NF s) : s.length = (toFin s).card := by
  rw [toFin, List.toFinset_card_of_nodup hs.2, List.length_map]
end WidthK.ProgMain
