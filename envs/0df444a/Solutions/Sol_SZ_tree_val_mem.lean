-- Prove2me | solution 1 for SZ.tree_val_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T02:59:15.85144+00:00
-- url     : https://prove2.me/submissions/ec2b3a6d-050d-42a6-91d0-40080a51ee04

import Definitions.Def_SZ_SqrtThree
import Mathlib.Algebra.AlgebraicCard
import Mathlib.SetTheory.Cardinal.Continuum
import Definitions.Def_SZ_CoverTree
import Theorems.Thm_SZ_valS_stepS
import Theorems.Thm_SZ_node_st_succ
import Theorems.Thm_SZ_node_st_zero
import Theorems.Thm_SZ_nodeDigit_adm
section
namespace SZ
open Filter Topology
private theorem t3_lb : (1.7 : ℝ) < Real.sqrt 3 :=
  (Real.lt_sqrt (by norm_num)).mpr (by norm_num)
private theorem t3_ub : Real.sqrt 3 < 1.8 := by
  have h : Real.sqrt 3 < Real.sqrt (1.8 ^ 2) := Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  rwa [Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 1.8)] at h
end SZ
end

set_option autoImplicit false
open SZ
open Filter Topology
namespace SZ
theorem _root_.solution (β : ℕ → Bool) (k : ℕ) :
    0 ≤ valS (node β k).st ∧ valS (node β k).st ≤ 3 + 3 * Real.sqrt 3 := by
  induction k with
  | zero =>
    rw [node_st_zero, valS]
    norm_num
    constructor <;> linarith [t3_lb, t3_ub]
  | succ k ih =>
    obtain ⟨-, hlo, hhi⟩ := nodeDigit_adm β (node β k) ih.1 ih.2
    rw [node_st_succ, valS_stepS, treeDigit]
    constructor <;> linarith
end SZ
