-- Prove2me | solution 1 for RecursionToBound.lt_needNet_of_none
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T06:52:11.080215+00:00
-- url     : https://prove2.me/submissions/6215b416-a9d8-4119-b7ee-dc34d11f62f2

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_RecursionToBound_Cert_Numbers
import Definitions.Def_ToTuring_Poly_NetFun
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.ByContra
import Definitions.Def_RecursionToBound_Guard
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_TM_Run_trans
attribute [local fun_prop] Groundwork.PolyT.length



set_option autoImplicit false
section
section
open RecursionToBound
open Groundwork Groundwork.Prog PaddedDescent.F ClauseBound.Alg ClauseBound.TopN VariableBound.Net
variable {Idx : Type} [Enc Idx] {S : Solver Idx}
namespace RecursionToBound
theorem _root_.solution (hS : S.Poly) {b : U} {i : Idx} {Ub P B : ℕ} (h : needNetC S b i Ub P B = none) : b.length < needNet S i Ub P B := by
  unfold needNetC at h
  have h1 := Option.map_eq_none_iff.1 h
  by_contra hc
  have h2 : S.need (i, List.replicate (lamS (S.K i) (3 * S.K i ^ 8) Ub P) (), List.replicate (bitsS (S.K i) (3 * S.K i ^ 8) P B) ()) ≤ b.length :=
    ((le_max_right _ _).trans (le_max_right _ _)).trans (not_lt.1 hc)
  rw [hS.needC_some b _ h2] at h1
  exact Option.some_ne_none _ h1
end RecursionToBound
