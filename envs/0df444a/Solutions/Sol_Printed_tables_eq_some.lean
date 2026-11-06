-- Prove2me | solution 1 for Printed.tables_eq_some
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T06:03:13.789236+00:00
-- url     : https://prove2.me/submissions/b1e24224-b7c6-4370-9214-8bd491699dd6

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Printed_Close
import Definitions.Def_Printed_Coding
import Definitions.Def_Printed_Absorb
import Definitions.Def_QueryMachines_Poly
import Definitions.Def_ToTuring_Poly_Brute
import Mathlib.Tactic
import Definitions.Def_Printed_Achievable
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_mem_words
attribute [local fun_prop] Groundwork.PolyT.length
attribute [local simp] Groundwork.mem_words



set_option autoImplicit false
section
section
open Printed
open Finset Groundwork Groundwork.Prog Eight.SecNetworks QueryMachines
namespace Printed
theorem _root_.solution {K lam : ℕ} {W : ℕ → List Bool → ℤ} {x : TableQuery} {v : ℤ} (h : tables K lam W x = some v) :
    x.1 < K ∧ x.2 ∈ words ((K - 1) * lam) ∧ v = W x.1 x.2 := by
  change (if x.1 < K ∧ x.2.length = (K - 1) * lam then some (W x.1 x.2) else none) = some v at h
  by_cases hx : x.1 < K ∧ x.2.length = (K - 1) * lam
  · rw [if_pos hx] at h
    exact ⟨hx.1, mem_words.2 hx.2, (Option.some.inj h).symm⟩
  · rw [if_neg hx] at h
    cases h
end Printed
