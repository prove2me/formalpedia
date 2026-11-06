-- Prove2me | solution 1 for RecursionToBound.needNetC_eq_some
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T06:52:10.099224+00:00
-- url     : https://prove2.me/submissions/b5dcafe8-5179-4dc0-9b2c-20da47be14cd

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_RecursionToBound_Cert_Numbers
import Definitions.Def_ToTuring_Poly_NetFun
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.ByContra
import Definitions.Def_RecursionToBound_Guard

set_option autoImplicit false
section
section
open RecursionToBound
open Groundwork Groundwork.Prog PaddedDescent.F ClauseBound.Alg ClauseBound.TopN VariableBound.Net
variable {Idx : Type} [Enc Idx] {S : Solver Idx}
namespace RecursionToBound
theorem _root_.solution (hS : S.Poly) {b : U} {i : Idx} {Ub P B w : ℕ} (h : needNetC S b i Ub P B = some w) : w = needNet S i Ub P B := by
  unfold needNetC at h
  obtain ⟨v, hv, rfl⟩ := Option.map_eq_some_iff.1 h
  rw [hS.needC_eq _ _ _ hv]
  rfl
end RecursionToBound
