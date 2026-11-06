-- Prove2me | solution 1 for SplitCount.stack_size
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T10:51:35.42317+00:00
-- url     : https://prove2.me/submissions/c984eab1-1f67-4286-91a3-eed57beb9754

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SplitCount_Defs
import Definitions.Def_SplitCount_Sizes
import Definitions.Def_SplitCount_Width
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_SplitCount_Leaf
import Theorems.Thm_SplitCount_clause_bound
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_Prog_size_list_le
import Theorems.Thm_Groundwork_TM_Run_trans
import Theorems.Thm_Groundwork_size_prod
import Theorems.Thm_SplitCount_size_list_le
import Theorems.Thm_SplitCount_size_node_le
import Theorems.Thm_SplitCount_size_unary
attribute [local fun_prop] Groundwork.PolyT.length
attribute [local simp] Groundwork.size_prod



set_option autoImplicit false
section
section
open SplitCount
open Groundwork Groundwork.Prog Paper CountKSat Eight.Width Occ
namespace SplitCount
theorem _root_.solution {k Dd Sk n m M : ℕ} {st : List NNode} (hn : n ≤ M) (hm : m ≤ M) (h1 : 1 ≤ M) (s1 : st.length ≤ Dd * n + 1)
    (s2 : ∀ x ∈ st, x.1 = List.replicate n () ∧ (leafF x.2).length ≤ (m + n) * Sk ∧ ∀ C ∈ leafF x.2, C.length ≤ max k 2 ∧ ∀ l ∈ C, l.1 < n) :
    size st ≤ stackConst k Dd Sk * M ^ 3 := by
  obtain ⟨w, hw⟩ : ∃ w, w = max k 2 := ⟨_, rfl⟩
  obtain ⟨Q, hQ⟩ : ∃ Q, Q = 4 * w + 2 := ⟨_, rfl⟩
  rw [stackConst, ← hw, ← hQ]
  rw [← hw] at s2
  have hq : w * (n + 2 + 1) + 1 + 1 ≤ Q * M := hQ ▸ clause_bound hn h1
  have hM2 : M ≤ M ^ 2 := Nat.le_self_pow (by norm_num) M
  have h1M2 : 1 ≤ M ^ 2 := Nat.one_le_pow _ _ h1
  have h1M3 : 1 ≤ M ^ 3 := Nat.one_le_pow _ _ h1
  have hf : ∀ x ∈ st, size x ≤ (4 * (Sk * Q) + 5) * M ^ 2 := by
    intro x hx
    obtain ⟨x1, x2, x3⟩ := s2 x hx
    have b1 : size x.1 ≤ n * 2 + 1 := x1 ▸ size_unary n
    have b2 := size_node_le x2 x3
    have b3 : (m + n) * Sk * (w * (n + 2 + 1) + 1 + 1) ≤ 2 * (Sk * Q) * M ^ 2 := by
      calc (m + n) * Sk * (w * (n + 2 + 1) + 1 + 1) ≤ (2 * M) * Sk * (Q * M) := Nat.mul_le_mul (Nat.mul_le_mul_right _ (by omega)) hq
        _ = 2 * (Sk * Q) * M ^ 2 := by ring
    have e2 : (4 * (Sk * Q) + 5) * M ^ 2 = 2 * (2 * (Sk * Q) * M ^ 2) + 5 * M ^ 2 := by ring
    rw [size_prod]
    omega
  refine (size_list_le s1 hf).trans ?_
  have hp : Dd * n + 1 ≤ (Dd + 1) * M := by
    have a1 : Dd * n ≤ Dd * M := Nat.mul_le_mul_left _ hn
    have a3 : (Dd + 1) * M = Dd * M + M := by ring
    omega
  have hp2 : (4 * (Sk * Q) + 5) * M ^ 2 + 1 ≤ (4 * (Sk * Q) + 6) * M ^ 2 := by
    have a3 : (4 * (Sk * Q) + 6) * M ^ 2 = (4 * (Sk * Q) + 5) * M ^ 2 + M ^ 2 := by ring
    omega
  calc (Dd * n + 1) * ((4 * (Sk * Q) + 5) * M ^ 2 + 1) + 1 ≤ (Dd + 1) * M * ((4 * (Sk * Q) + 6) * M ^ 2) + 1 := Nat.succ_le_succ (Nat.mul_le_mul hp hp2)
    _ = (Dd + 1) * (4 * (Sk * Q) + 6) * M ^ 3 + 1 := by ring
    _ ≤ (Dd + 1) * (4 * (Sk * Q) + 6) * M ^ 3 + M ^ 3 := Nat.add_le_add_left h1M3 _
    _ = ((Dd + 1) * (4 * (Sk * Q) + 6) + 1) * M ^ 3 := by ring
end SplitCount
