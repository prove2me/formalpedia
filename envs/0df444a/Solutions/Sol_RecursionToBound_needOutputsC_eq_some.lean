-- Prove2me | solution 1 for RecursionToBound.needOutputsC_eq_some
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:19:10.078743+00:00
-- url     : https://prove2.me/submissions/3b7b4668-f763-4ced-b789-78dce7a7552f

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_RecursionToBound_Cert_Numbers
import Definitions.Def_ToTuring_Poly_NetFun
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.ByContra
import Definitions.Def_RecursionToBound_Guard
import Theorems.Thm_RecursionToBound_needAtC_eq_some
import Theorems.Thm_RecursionToBound_foldr_bind_max_of_some
import Theorems.Thm_RecursionToBound_isSome_of_foldr_bind_max


set_option autoImplicit false
section
section
open RecursionToBound
open Groundwork Groundwork.Prog PaddedDescent.F ClauseBound.Alg ClauseBound.TopN VariableBound.Net
variable {Idx : Type} [Enc Idx] {S : Solver Idx}
namespace RecursionToBound
theorem _root_.solution (hS : S.Poly) {b : U} {k : ℕ} {r : ℕ × ℕ} {i : Idx} {n w : ℕ} (h : needOutputsC S b k r i n = some w) : w = needOutputs S k r i n := by
  unfold needOutputsC at h
  have h1 : ∀ Δ ∈ deltas k r n, needAtC S b k i n Δ = some (needAt S k i n Δ) := fun Δ hΔ => by
    obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1 (isSome_of_foldr_bind_max h Δ hΔ)
    rw [hv, needAtC_eq_some hS hv]
  rw [foldr_bind_max_of_some h1] at h
  exact (Option.some.inj h).symm
end RecursionToBound
