-- Prove2me | solution 1 for RecursionToBound.planFailsOnlyAboveN
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:27:54.496243+00:00
-- url     : https://prove2.me/submissions/24c7b212-a12e-4c86-82a2-53c25f237f44

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_RecursionToBound_Cert_Numbers
import Definitions.Def_ToTuring_Poly_NetFun
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.ByContra
import Definitions.Def_RecursionToBound_Guard
import Theorems.Thm_RecursionToBound_needOutputsC_eq_some
import Theorems.Thm_RecursionToBound_lt_needOutputs_of_none

set_option autoImplicit false
section
section
open RecursionToBound
open Groundwork Groundwork.Prog PaddedDescent.F ClauseBound.Alg ClauseBound.TopN VariableBound.Net
variable {Idx : Type} [Enc Idx] {S : Solver Idx}
namespace RecursionToBound
theorem _root_.solution : PlanFailsOnlyAboveN := by
  intro Idx _ S hS n₁ k n i r
  constructor
  · intro v h
    unfold planAt at h
    split_ifs at h with hn
    obtain ⟨w, hw, h2⟩ := Option.bind_eq_some_iff.1 h
    split_ifs at h2 with hc
    have e := Option.some.inj h2
    rw [needOutputsC_eq_some hS hw] at e hc
    exact ⟨hn, e.symm, e ▸ hc⟩
  · intro h hn
    unfold planAt at h
    rw [if_pos hn] at h
    cases hw : needOutputsC S (List.replicate n ()) k r i n with
    | none =>
      have h1 := lt_needOutputs_of_none hS hw
      rw [List.length_replicate] at h1
      omega
    | some w =>
      rw [hw, Option.bind_some] at h
      split_ifs at h with hc
      rw [← needOutputsC_eq_some hS hw]
      omega
end RecursionToBound
