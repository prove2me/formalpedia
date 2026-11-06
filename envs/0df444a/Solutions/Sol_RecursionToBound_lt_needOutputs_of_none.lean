-- Prove2me | solution 1 for RecursionToBound.lt_needOutputs_of_none
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:10:55.688662+00:00
-- url     : https://prove2.me/submissions/fdeec380-d417-492a-87d4-4a010a15b914

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_RecursionToBound_Cert_Numbers
import Definitions.Def_ToTuring_Poly_NetFun
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.ByContra
import Definitions.Def_RecursionToBound_Guard
import Theorems.Thm_RecursionToBound_lt_needAt_of_none
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_Prog_NetE_le_foldr_max
import Theorems.Thm_RecursionToBound_exists_none_of_foldr_bind_max
attribute [local fun_prop] Groundwork.PolyT.length



set_option autoImplicit false
section
section
open RecursionToBound
open Groundwork Groundwork.Prog PaddedDescent.F ClauseBound.Alg ClauseBound.TopN VariableBound.Net
variable {Idx : Type} [Enc Idx] {S : Solver Idx}
namespace RecursionToBound
theorem _root_.solution (hS : S.Poly) {b : U} {k : ℕ} {r : ℕ × ℕ} {i : Idx} {n : ℕ} (h : needOutputsC S b k r i n = none) : b.length < needOutputs S k r i n := by
  unfold needOutputsC at h
  obtain ⟨Δ, hΔ, hn⟩ := exists_none_of_foldr_bind_max h
  exact (lt_needAt_of_none hS hn).trans_le (NetE.le_foldr_max (List.mem_map_of_mem hΔ))
end RecursionToBound
