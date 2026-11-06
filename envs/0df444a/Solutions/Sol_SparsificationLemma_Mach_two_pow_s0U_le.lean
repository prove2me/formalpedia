-- Prove2me | solution 1 for SparsificationLemma.Mach.two_pow_s0U_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:35:49.950579+00:00
-- url     : https://prove2.me/submissions/00337522-d7ec-444f-a803-892f9cd2b6d1

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SparsificationLemma_Mach_Defs
import Definitions.Def_SparsificationLemma_Geo_S
import Definitions.Def_SparsificationLemma_Mach_Len
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Definitions.Def_SparsificationLemma_Mach_Full

set_option autoImplicit false
section
section
open SparsificationLemma SparsificationLemma.Mach
open Groundwork Groundwork.Prog Groundwork.Sparsify CountKSat CountKSatRate UniformInK PaddedDescent SparsificationLemma.Geo Turing
namespace SparsificationLemma.Mach
theorem _root_.solution {k : ℕ} (hk : 1 ≤ k) : 2 ^ s0U k ≤ 4 * k ^ 2 := by
  have hpos : 0 < Nat.size k := Nat.size_pos.2 hk
  obtain ⟨j, hj⟩ : ∃ j, Nat.size k = j + 1 := ⟨Nat.size k - 1, by omega⟩
  have h1 : 2 ^ j ≤ k := Nat.lt_size.1 (by omega)
  have h2 : 2 ^ s0U k = 4 * (2 ^ j) ^ 2 := by rw [s0U, hj]; ring
  rw [h2]
  exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h1 2)
end SparsificationLemma.Mach
