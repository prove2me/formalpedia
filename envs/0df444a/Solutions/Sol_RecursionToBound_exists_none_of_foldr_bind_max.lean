-- Prove2me | solution 1 for RecursionToBound.exists_none_of_foldr_bind_max
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T06:51:58.455555+00:00
-- url     : https://prove2.me/submissions/05832989-cfac-4e4b-ab13-39e698f1d66f

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
import Theorems.Thm_RecursionToBound_foldr_bind_max
import Theorems.Thm_Groundwork_PolyT_map
attribute [local fun_prop] Groundwork.PolyT.map



set_option autoImplicit false
section
section
open RecursionToBound
open Finset SparsificationLemma
namespace RecursionToBound
theorem _root_.solution {f : ℕ → Option ℕ} {l : List ℕ} (h : l.foldr (fun a o => o.bind fun v => (f a).map (max v)) (some 0) = none) :
    ∃ a ∈ l, f a = none := by
  rw [foldr_bind_max] at h
  by_contra hc
  rw [if_pos (List.all_eq_true.2 fun a ha => ?_)] at h
  · exact Option.some_ne_none _ h
  · exact Option.isSome_iff_ne_none.2 fun hn => hc ⟨a, ha, hn⟩
end RecursionToBound
