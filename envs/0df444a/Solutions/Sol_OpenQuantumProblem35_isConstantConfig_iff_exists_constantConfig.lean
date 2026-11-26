-- Prove2me | solution 1 for OpenQuantumProblem35.isConstantConfig_iff_exists_constantConfig
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T23:06:28.620457+00:00
-- url     : https://prove2.me/submissions/77d25ee9-6eff-43e6-84de-aa55fc6eb1a3

module
public import Mathlib
public import Definitions.Def_AME125_Defs
public import Theorems.Thm_OpenQuantumProblem35_mkStateVector_apply
public import Theorems.Thm_OpenQuantumProblem35_permuteState_apply
public import Theorems.Thm_OpenQuantumProblem35_combineFirst_leftIndex
public import Theorems.Thm_OpenQuantumProblem35_combineFirst_rightIndex
public import Theorems.Thm_OpenQuantumProblem35_card_config
public import Theorems.Thm_OpenQuantumProblem35_diagonalState_apply
attribute [local simp] OpenQuantumProblem35.mkStateVector_apply
attribute [local simp] OpenQuantumProblem35.permuteState_apply
attribute [local simp] OpenQuantumProblem35.combineFirst_leftIndex
attribute [local simp] OpenQuantumProblem35.combineFirst_rightIndex
attribute [local simp] OpenQuantumProblem35.card_config
attribute [local simp] OpenQuantumProblem35.diagonalState_apply

set_option autoImplicit false
@[expose] public section
public section
open scoped BigOperators
open OpenQuantumProblem35
namespace OpenQuantumProblem35
theorem _root_.solution {n d : ℕ} (hn : 1 ≤ n)
    (x : Config n d) :
    IsConstantConfig x ↔ ∃ a : Fin d, x = constantConfig (m := n) (d := d) a := by
  let i0 : Fin n := ⟨0, Nat.succ_le_iff.mp hn⟩
  constructor
  · intro hx
    refine ⟨x i0, ?_⟩
    funext i
    simpa [constantConfig] using hx i i0
  · rintro ⟨a, rfl⟩ i j
    simp [constantConfig]
end OpenQuantumProblem35
