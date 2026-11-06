-- Prove2me | solution 1 for RecursionToBound.needAtC_eq_some
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:10:11.94941+00:00
-- url     : https://prove2.me/submissions/2688128b-b160-4c76-b7d6-59554e769dcb

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_RecursionToBound_Cert_Numbers
import Definitions.Def_ToTuring_Poly_NetFun
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.ByContra
import Definitions.Def_RecursionToBound_Guard
import Theorems.Thm_RecursionToBound_needNetC_eq_some

set_option autoImplicit false
section
section
open RecursionToBound
open Groundwork Groundwork.Prog PaddedDescent.F ClauseBound.Alg ClauseBound.TopN VariableBound.Net
variable {Idx : Type} [Enc Idx] {S : Solver Idx}
namespace RecursionToBound
theorem _root_.solution (hS : S.Poly) {b : U} {k : ℕ} {i : Idx} {n Δ w : ℕ} (h : needAtC S b k i n Δ = some w) : w = needAt S k i n Δ := by
  unfold needAtC at h
  obtain ⟨v, hv, rfl⟩ := Option.map_eq_some_iff.1 h
  rw [needNetC_eq_some hS hv]
  rfl
end RecursionToBound
