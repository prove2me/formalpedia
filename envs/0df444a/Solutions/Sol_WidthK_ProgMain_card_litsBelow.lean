-- Prove2me | solution 1 for WidthK.ProgMain.card_litsBelow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T19:39:53.13727+00:00
-- url     : https://prove2.me/submissions/e1fe639d-00ce-4c6c-87bd-0c9a9672a455

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SparsifyWidthK_Interfaces
import Mathlib.Tactic.Linarith
import Definitions.Def_SparsifyWidthK_ProgMain

set_option autoImplicit false
section
section
open WidthK WidthK.ProgMain
open Finset Groundwork Groundwork.Sparsify WidthK.Prog
namespace WidthK.ProgMain
theorem _root_.solution (n : ℕ) : (litsBelow n).card ≤ 2 * n := by
  rw [litsBelow, Finset.card_product, Finset.card_range, Finset.card_univ, Fintype.card_bool, Nat.mul_comm]
end WidthK.ProgMain
