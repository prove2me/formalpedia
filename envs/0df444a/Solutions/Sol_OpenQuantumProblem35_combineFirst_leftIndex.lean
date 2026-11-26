-- Prove2me | solution 1 for OpenQuantumProblem35.combineFirst_leftIndex
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T23:02:09.636326+00:00
-- url     : https://prove2.me/submissions/ce8ab818-4a5a-4201-bde0-7e0107547df3

module
public import Mathlib
public import Definitions.Def_AME125_Defs
public import Theorems.Thm_OpenQuantumProblem35_mkStateVector_apply
public import Theorems.Thm_OpenQuantumProblem35_permuteState_apply
attribute [local simp] OpenQuantumProblem35.mkStateVector_apply
attribute [local simp] OpenQuantumProblem35.permuteState_apply

set_option autoImplicit false
@[expose] public section
public section
open scoped BigOperators
open OpenQuantumProblem35
namespace OpenQuantumProblem35
theorem _root_.solution {n d m : ℕ} (hm : m ≤ n)
    (x : Config m d) (y : Config (n - m) d) (i : Fin m) :
    combineFirst (n := n) (d := d) m hm x y (leftIndex hm i) = x i := by
  simp [combineFirst, leftIndex, i.2]
end OpenQuantumProblem35
