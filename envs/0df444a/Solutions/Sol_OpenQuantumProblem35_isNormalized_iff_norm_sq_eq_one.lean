-- Prove2me | solution 1 for OpenQuantumProblem35.isNormalized_iff_norm_sq_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T23:00:47.627629+00:00
-- url     : https://prove2.me/submissions/cce2daf6-48ae-47a2-ad35-d471888db3d7

module
public import Mathlib
public import Definitions.Def_AME125_Defs
public import Theorems.Thm_OpenQuantumProblem35_mkStateVector_apply
attribute [local simp] OpenQuantumProblem35.mkStateVector_apply

set_option autoImplicit false
@[expose] public section
public section
open scoped BigOperators
open OpenQuantumProblem35
namespace OpenQuantumProblem35
theorem _root_.solution {n d : ℕ} (ψ : StateVector n d) :
    IsNormalized ψ ↔ ‖ψ‖ ^ 2 = 1 := by
  constructor
  · intro h
    rw [IsNormalized] at h
    calc
      ‖ψ‖ ^ 2 = (1 : ℝ) ^ 2 := by rw [h]
      _ = 1 := by norm_num
  · intro h
    rw [IsNormalized]
    have hsq : ‖ψ‖ ^ 2 = (1 : ℝ) ^ 2 := by
      simpa using h
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq with hnorm | hnorm
    · exact hnorm
    · have hnonneg : 0 ≤ ‖ψ‖ := norm_nonneg ψ
      have : False := by
        linarith
      exact False.elim this
end OpenQuantumProblem35
