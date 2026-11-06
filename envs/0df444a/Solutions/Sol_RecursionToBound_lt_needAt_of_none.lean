-- Prove2me | solution 1 for RecursionToBound.lt_needAt_of_none
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:00:47.818425+00:00
-- url     : https://prove2.me/submissions/cc8ec68c-12ae-41e8-9084-a7aab08e584d

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_RecursionToBound_Cert_Numbers
import Definitions.Def_ToTuring_Poly_NetFun
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.ByContra
import Definitions.Def_RecursionToBound_Guard
import Theorems.Thm_RecursionToBound_lt_needNet_of_none
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length



set_option autoImplicit false
section
section
open RecursionToBound
open Groundwork Groundwork.Prog PaddedDescent.F ClauseBound.Alg ClauseBound.TopN VariableBound.Net
variable {Idx : Type} [Enc Idx] {S : Solver Idx}
namespace RecursionToBound
theorem _root_.solution (hS : S.Poly) {b : U} {k : ℕ} {i : Idx} {n Δ : ℕ} (h : needAtC S b k i n Δ = none) : b.length < needAt S k i n Δ := by
  unfold needAtC at h
  have h1 := lt_needNet_of_none hS (Option.map_eq_none_iff.1 h)
  unfold needAt
  omega
end RecursionToBound
