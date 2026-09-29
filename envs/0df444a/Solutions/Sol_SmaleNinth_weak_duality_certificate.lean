-- Prove2me | solution 1 for SmaleNinth.weak_duality_certificate
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-24T12:07:18.969577+00:00
-- url     : https://prove2.me/submissions/a0cec79a-17a1-4222-95fe-70964f9a481a

import Definitions.Def_Polyhedron
import Mathlib.Tactic

open Matrix LinearOptimization Finset

theorem solution {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ) (c : Fin n → ℝ) {x : Fin n → ℝ} {y : Fin m → ℝ}
    (hx : x ∈ polyhedron A b) (hy0 : ∀ i, 0 ≤ y i)
    (hyA : ∀ k, ∑ i, y i * A i k = c k) :
    (∑ i, y i * b i) ≤ (∑ k, c k * x k) := by
  have hweighted : (∑ i, y i * b i) ≤
      ∑ i, y i * (A.mulVec x) i := by
    apply Finset.sum_le_sum
    intro i hi
    exact mul_le_mul_of_nonneg_left (hx i) (hy0 i)
  have hswap : (∑ k, c k * x k) =
      ∑ i, y i * (A.mulVec x) i := by
    have e : ∀ k, c k * x k = (∑ i, y i * A i k) * x k := by
      intro k
      rw [hyA k]
    rw [Finset.sum_congr rfl (fun k _ => e k)]
    simp only [Matrix.mulVec, dotProduct, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl (fun i _ =>
      Finset.sum_congr rfl (fun k _ => by ring))
  exact hweighted.trans_eq hswap.symm
