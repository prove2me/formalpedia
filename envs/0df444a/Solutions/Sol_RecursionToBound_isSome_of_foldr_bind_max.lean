-- Prove2me | solution 1 for RecursionToBound.isSome_of_foldr_bind_max
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T06:52:03.262235+00:00
-- url     : https://prove2.me/submissions/321e325e-4b5b-48e7-a6a5-0a28ef9a615c

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
theorem _root_.solution {f : ℕ → Option ℕ} {l : List ℕ} {v : ℕ} (h : l.foldr (fun a o => o.bind fun v => (f a).map (max v)) (some 0) = some v) :
    ∀ a ∈ l, (f a).isSome = true := by
  rw [foldr_bind_max] at h
  split_ifs at h with hc
  exact List.all_eq_true.1 hc
end RecursionToBound
