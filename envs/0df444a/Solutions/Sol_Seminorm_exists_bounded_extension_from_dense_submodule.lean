-- Prove2me | solution 1 for Seminorm.exists_bounded_extension_from_dense_submodule
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-17T22:03:57.829786+00:00
-- url     : https://prove2.me/submissions/6f3c44f1-ca42-4ffb-943c-21a0610e175e

import Mathlib.Analysis.Seminorm
import Mathlib.Analysis.Normed.Operator.Extend
open scoped NNReal
set_option autoImplicit false

 theorem solution {V F : Type*} [AddCommGroup V] [Module ℝ V]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (q : Seminorm ℝ V) (S : Submodule ℝ V) (r : S →ₗ[ℝ] F) (C : ℝ≥0)
    (hdense : ∀ x : V, ∀ ε : ℝ, 0 < ε → ∃ y : S, q (x - y) < ε)
    (hbound : ∀ y : S, ‖r y‖ ≤ (C : ℝ) * q y) :
    ∃ T : V →ₗ[ℝ] F, (∀ x, ‖T x‖ ≤ (C : ℝ) * q x) ∧ ∀ y : S, T y = r y := by
  letI := q.toAddGroupSeminorm.toSeminormedAddCommGroup
  letI : NormedSpace ℝ V := ⟨fun a x => le_of_eq (map_smul_eq_mul q a x)⟩
  have hd : DenseRange S.subtype := by
    rw [Metric.denseRange_iff]
    intro x ε hε
    obtain ⟨y, hy⟩ := hdense x ε hε
    refine ⟨y, ?_⟩
    rw [dist_eq_norm]
    change q (x - (y : V)) < ε
    exact hy
  refine ⟨(r.extendOfNorm S.subtype).toLinearMap, ?_, ?_⟩
  · exact fun x => r.norm_extendOfNorm_apply_le hd C hbound x
  · exact fun y => r.extendOfNorm_eq hd ⟨C, hbound⟩ y


