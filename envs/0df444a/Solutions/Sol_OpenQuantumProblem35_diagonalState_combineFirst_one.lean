-- Prove2me | solution 1 for OpenQuantumProblem35.diagonalState_combineFirst_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T23:09:43.920553+00:00
-- url     : https://prove2.me/submissions/fc5a1d72-c26d-4eb8-9fda-2ab8f47b432c

module
public import Mathlib
public import Definitions.Def_AME125_Defs
public import Theorems.Thm_OpenQuantumProblem35_diagonalState_apply
public import Theorems.Thm_OpenQuantumProblem35_isConstantConfig_combineFirst_one_iff
attribute [local simp] OpenQuantumProblem35.diagonalState_apply

set_option autoImplicit false
@[expose] public section
public section
open scoped BigOperators
open OpenQuantumProblem35
namespace OpenQuantumProblem35
theorem _root_.solution {n d : ℕ} (hn : 1 ≤ n)
    (x : Config 1 d) (z : Config (n - 1) d) :
    diagonalState n d (combineFirst (n := n) (d := d) 1 hn x z) =
      if z = constantCompletion (n := n) (d := d) x then uniformCoeff d else 0 := by
  by_cases h : z = constantCompletion (n := n) (d := d) x
  · subst z
    have hconst :
        IsConstantConfig
          (combineFirst (n := n) (d := d) 1 hn x (constantCompletion (n := n) (d := d) x)) := by
      exact (isConstantConfig_combineFirst_one_iff hn x
        (constantCompletion (n := n) (d := d) x)).2 rfl
    rw [diagonalState_apply, if_pos hconst, if_pos rfl]
  · have h' : ¬ IsConstantConfig (combineFirst (n := n) (d := d) 1 hn x z) := by
      intro hx
      exact h ((isConstantConfig_combineFirst_one_iff hn x z).1 hx)
    rw [diagonalState_apply, if_neg h', if_neg h]
end OpenQuantumProblem35
