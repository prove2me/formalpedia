-- Prove2me | solution 1 for Sat3Graph.size_dnode_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T10:52:08.167881+00:00
-- url     : https://prove2.me/submissions/380ac02e-fae3-4708-8fa5-ff5e15c43fec

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Sat3Graph_Defs
import Definitions.Def_Sat3Graph_Ask
import Definitions.Def_SplitSat_Sizes
import Definitions.Def_GraphProblems_Sets
import Definitions.Def_GraphProblems_Read
import Mathlib.Tactic
import Definitions.Def_Sat3Graph_Dominating
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_Prog_SatTopK_size_fml_le
import Theorems.Thm_Groundwork_Prog_size_list_le
import Theorems.Thm_Groundwork_RebalanceArith_size_le
import Theorems.Thm_Groundwork_TM_Run_trans
import Theorems.Thm_Groundwork_size_nat
import Theorems.Thm_Groundwork_size_prod
import Theorems.Thm_SplitSat_size_fml_le
import Theorems.Thm_SplitSat_size_list_le
import Theorems.Thm_SplitSat_size_unary_le
attribute [local fun_prop] Groundwork.PolyT.length
attribute [local simp] Groundwork.size_nat
attribute [local simp] Groundwork.size_prod



set_option autoImplicit false
section
section
open Sat3Graph
open Groundwork Groundwork.Prog Groundwork.Sparsify CountKSat GraphProblems Paper SizeCircuit SplitSat
namespace Sat3Graph
theorem _root_.solution {w n s : ℕ} {x : DNode} (hs : s ≤ n) (h1 : x.1 = (List.replicate n (), s)) (h2 : x.2.1.length ≤ n)
    (h3 : ∀ D ∈ x.2.1, D.length ≤ n ∧ ∀ u ∈ D, u < n) (h4 : x.2.2.length ≤ 2 * n) (h5 : Shaped w n x.2.2) :
    size x ≤ (4 * w + 12) * (n + 2) ^ 3 := by
  have s1 := size_unary_le n
  have s2 : size s ≤ n + 2 := by
    have : s.size ≤ n + 1 := Nat.size_le.2 (lt_of_le_of_lt hs (Nat.lt_two_pow_self.trans (Nat.pow_lt_pow_right (by norm_num) (by omega))))
    rw [size_nat]
    omega
  have s3 : size x.2.1 ≤ n * (n * (n + 1 + 1) + 1 + 1) + 1 :=
    SplitSat.size_list_le h2 fun D hD => SplitSat.size_list_le (h3 D hD).1 fun u hu => by
      have : u.size ≤ n := Nat.size_le.2 (((h3 D hD).2 u hu).trans Nat.lt_two_pow_self)
      rw [size_nat]
      omega
  have s4 : size x.2.2 ≤ 2 * n * (w * (n + 2 + 1) + 1 + 1) + 1 := size_fml_le h4 h5
  have sx : size x = size (List.replicate n ()) + size s + (size x.2.1 + size x.2.2) := by
    rw [size_prod, size_prod, h1]
    rfl
  rw [sx]
  have e1 : n * (n * (n + 1 + 1) + 1 + 1) ≤ (n + 2) ^ 3 := by nlinarith
  have e2 : 2 * n * (w * (n + 2 + 1) + 1 + 1) ≤ (4 * w + 4) * (n + 2) ^ 3 := by
    have : (n + 2) ^ 2 ≤ (n + 2) ^ 3 := Nat.pow_le_pow_right (by omega) (by norm_num)
    have h6 : 2 * n * (w * (n + 2 + 1) + 1 + 1) ≤ (4 * w + 4) * (n + 2) ^ 2 := by nlinarith
    exact h6.trans (Nat.mul_le_mul_left _ this)
  have e3 : n + 2 ≤ (n + 2) ^ 3 := Nat.le_self_pow (by norm_num) _
  have e4 : (4 * w + 12) * (n + 2) ^ 3 = (4 * w + 4) * (n + 2) ^ 3 + 8 * (n + 2) ^ 3 := by ring
  omega
end Sat3Graph
