-- Prove2me | solution 1 for SparsificationLemma.Cal.thetaC_of_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T01:34:37.079236+00:00
-- url     : https://prove2.me/submissions/ddaf1b6e-e71e-416d-9b36-25671bd79af5

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SparsificationLemma_Cal_Defs
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Ring
import Definitions.Def_SparsificationLemma_Cal_Beta

set_option autoImplicit false
section
section
open SparsificationLemma SparsificationLemma.Cal
open Finset
namespace SparsificationLemma.Cal
theorem _root_.solution (α : ℕ) {c : ℕ} (hc : 1 ≤ c) : thetaC α c = α * betaC α c := by
  obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_le' hc
  rfl
end SparsificationLemma.Cal
