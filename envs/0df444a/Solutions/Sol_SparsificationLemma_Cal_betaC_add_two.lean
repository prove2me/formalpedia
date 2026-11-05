-- Prove2me | solution 1 for SparsificationLemma.Cal.betaC_add_two
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T01:33:52.665628+00:00
-- url     : https://prove2.me/submissions/916bdc45-c470-4630-9c89-2f005aba038f

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
theorem _root_.solution (α c : ℕ) : betaC α (c + 2) = ∑ h : Fin (c + 1), 4 * α * betaC α (c + 1 - h) * betaC α (h + 1) := by rw [betaC]
end SparsificationLemma.Cal
