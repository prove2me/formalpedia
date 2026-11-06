-- Prove2me | solution 1 for SparsificationLemma.Mach.poly_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:44:48.962478+00:00
-- url     : https://prove2.me/submissions/a3db6b43-3691-4095-ba4f-87c77bd3bc54

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SparsificationLemma_Mach_Defs
import Definitions.Def_SparsificationLemma_Mach_Full
import Definitions.Def_SparsificationLemma_Len
import Definitions.Def_WidthK_Decode
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Definitions.Def_SparsificationLemma_Mach_LemSparsification
import Theorems.Thm_SparsificationLemma_Mach_length_encIn_le
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length



set_option autoImplicit false
section
section
open SparsificationLemma SparsificationLemma.Mach
open Groundwork Groundwork.Prog Groundwork.Sparsify CountKSat CountKSatRate UniformInK PaddedDescent SparsificationLemma.Geo Turing
namespace SparsificationLemma.Mach
theorem _root_.solution (C s : ℕ) {n : ℕ} {φ : Sat3.CNF n} (h3 : SatK.IsKCNF 3 φ) :
    C * ((encIn s 3 φ).length + 2 ^ 3) ^ C ≤ (C * (s + 412) ^ C + 4 * C) * (n + 1) ^ (C * (s + 412) ^ C + 4 * C) := by
  calc C * ((encIn s 3 φ).length + 2 ^ 3) ^ C ≤ C * ((s + 412) * (n + 1) ^ 4) ^ C :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (length_encIn_le s h3) C)
    _ = C * (s + 412) ^ C * (n + 1) ^ (4 * C) := by rw [mul_pow, ← pow_mul]; ring
    _ ≤ (C * (s + 412) ^ C + 4 * C) * (n + 1) ^ (C * (s + 412) ^ C + 4 * C) :=
        Nat.mul_le_mul (Nat.le_add_right _ _) (Nat.pow_le_pow_right (by omega) (Nat.le_add_left _ _))
end SparsificationLemma.Mach
