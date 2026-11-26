-- Prove2me | solution 1 for OpenQuantumProblem35.combineFirst_rightIndex
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T23:03:22.620375+00:00
-- url     : https://prove2.me/submissions/fad14d2e-80d5-4f98-a058-6eef29b254bf

module
public import Mathlib
public import Definitions.Def_AME125_Defs
public import Theorems.Thm_OpenQuantumProblem35_mkStateVector_apply
public import Theorems.Thm_OpenQuantumProblem35_permuteState_apply
public import Theorems.Thm_OpenQuantumProblem35_combineFirst_leftIndex
attribute [local simp] OpenQuantumProblem35.mkStateVector_apply
attribute [local simp] OpenQuantumProblem35.permuteState_apply
attribute [local simp] OpenQuantumProblem35.combineFirst_leftIndex

set_option autoImplicit false
@[expose] public section
public section
open scoped BigOperators
open OpenQuantumProblem35
namespace OpenQuantumProblem35
theorem _root_.solution {n d m : ℕ} (hm : m ≤ n)
    (x : Config m d) (y : Config (n - m) d) (i : Fin (n - m)) :
    combineFirst (n := n) (d := d) m hm x y (rightIndex hm i) = y i := by
  have hnot : ¬ m + i.1 < m := by omega
  simp [combineFirst, rightIndex, hnot]
end OpenQuantumProblem35
