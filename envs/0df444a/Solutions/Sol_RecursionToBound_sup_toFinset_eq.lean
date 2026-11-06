-- Prove2me | solution 1 for RecursionToBound.sup_toFinset_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T06:51:05.98626+00:00
-- url     : https://prove2.me/submissions/d85a2e33-6b65-4c4c-a32e-d00fccc906ad

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_RecursionToBound_Defs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.ByContra
import Definitions.Def_RecursionToBound_Cert_Numbers
import Theorems.Thm_Groundwork_PolyT_map
attribute [local fun_prop] Groundwork.PolyT.map



set_option autoImplicit false
section
section
open RecursionToBound
open Finset SparsificationLemma
namespace RecursionToBound
theorem _root_.solution (f : ℕ → ℕ) (l : List ℕ) : l.toFinset.sup f = (l.map f).foldr max 0 := by
  induction l with
  | nil => rfl
  | cons a l ih => rw [List.toFinset_cons, Finset.sup_insert, ih, List.map_cons, List.foldr_cons]
end RecursionToBound
