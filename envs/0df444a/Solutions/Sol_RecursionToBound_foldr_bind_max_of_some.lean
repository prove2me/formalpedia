-- Prove2me | solution 1 for RecursionToBound.foldr_bind_max_of_some
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T06:51:57.354426+00:00
-- url     : https://prove2.me/submissions/1a765275-ce8a-4315-8387-f830082a3956

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
import Theorems.Thm_Groundwork_PolyT_congr
import Theorems.Thm_Groundwork_PolyT_map
attribute [local fun_prop] Groundwork.PolyT.map



set_option autoImplicit false
section
section
open RecursionToBound
open Finset SparsificationLemma
namespace RecursionToBound
theorem _root_.solution {f : ℕ → Option ℕ} {g : ℕ → ℕ} {l : List ℕ} (h : ∀ a ∈ l, f a = some (g a)) :
    l.foldr (fun a o => o.bind fun v => (f a).map (max v)) (some 0) = some ((l.map g).foldr max 0) := by
  rw [foldr_bind_max, if_pos (List.all_eq_true.2 fun a ha => by rw [h a ha]; rfl)]
  congr 2
  exact List.map_congr_left fun a ha => by rw [h a ha]; rfl
end RecursionToBound
