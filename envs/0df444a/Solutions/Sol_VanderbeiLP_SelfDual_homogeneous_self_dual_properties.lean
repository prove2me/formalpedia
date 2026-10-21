-- Prove2me | solution 1 for VanderbeiLP.SelfDual.homogeneous_self_dual_properties
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T05:06:26.422033+00:00
-- url     : https://prove2.me/submissions/787a9191-9f45-4d01-997b-0b570a5d4dee

import Mathlib
import Definitions.Def_VanderbeiLP_SelfDual_HomogeneousSelfDual

set_option autoImplicit false
open Matrix VanderbeiLP.SelfDual

theorem skew_swap {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : IsSkewSymmetric A)
    (u v : Fin n → ℝ) : u ⬝ᵥ (A *ᵥ v) = -((A *ᵥ u) ⬝ᵥ v) := by
  rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hA, Matrix.neg_mulVec,
    neg_dotProduct]

theorem skew_quad {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : IsSkewSymmetric A)
    (v : Fin n → ℝ) : v ⬝ᵥ (A *ᵥ v) = 0 := by
  have h := skew_swap A hA v v
  rw [dotProduct_comm (A *ᵥ v) v] at h
  linarith

theorem solution {n : ℕ} (hn : 2 ≤ n)
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : IsSkewSymmetric A) :
    ((∃ x z : Fin n → ℝ, SelfDualFeasible A x z) ∧
      ∀ x z : Fin n → ℝ, SelfDualFeasible A x z → SelfDualOptimal A x z) ∧
    ((¬ ∃ x z : Fin n → ℝ, SelfDualFeasible A x z ∧ (∀ j, 0 < x j) ∧ ∀ j, 0 < z j) ∧
      ∀ x z : Fin n → ℝ, SelfDualFeasible A x z → z ⬝ᵥ x = 0) := by
  have key : ∀ x z : Fin n → ℝ, SelfDualFeasible A x z → z ⬝ᵥ x = 0 := by
    intro x z ⟨h, _, _⟩
    have hz : z = -(A *ᵥ x) := by
      rw [eq_neg_iff_add_eq_zero, add_comm]; exact h
    rw [hz, neg_dotProduct, dotProduct_comm, skew_quad A hA x, neg_zero]
  refine ⟨⟨⟨0, 0, by simp [SelfDualFeasible]⟩, fun x z hxz => ⟨hxz, fun x' z' _ => by simp⟩⟩,
    ?_, key⟩
  rintro ⟨x, z, hf, hx, hz⟩
  have h0 := key x z hf
  have hpos : 0 < z ⬝ᵥ x := by
    unfold dotProduct
    haveI : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
    exact Finset.sum_pos (fun j _ => mul_pos (hz j) (hx j)) Finset.univ_nonempty
  linarith
