-- Prove2me | solution 1 for SmaleNinth.lp_complementary_slackness
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-08T02:33:54.911107+00:00
-- url     : https://prove2.me/submissions/465efd70-ca0b-4c78-9a71-f6bc84a98321

import Definitions.Def_Polyhedron
import Mathlib.Tactic

/-!
# Complementary slackness

The duality gap of a feasible primal-dual pair decomposes into the individual
slacks, each weighted by a nonnegative dual variable, so it vanishes exactly
when every product does.
-/

open Matrix LinearOptimization Finset

/-- **Complementary slackness.** -/
theorem solution {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ)
    {x : Fin n → ℝ} {y : Fin m → ℝ} (hx : x ∈ polyhedron A b) (hy0 : ∀ i, 0 ≤ y i)
    (hyA : ∀ k, ∑ i, y i * A i k = c k) :
    (∑ k, c k * x k = ∑ i, y i * b i) ↔ ∀ i, y i * ((A.mulVec x) i - b i) = 0 := by
  have hxi : ∀ i, b i ≤ (A.mulVec x) i := fun i => hx i
  have hgap : (∑ k, c k * x k) - (∑ i, y i * b i)
      = ∑ i, y i * ((A.mulVec x) i - b i) := by
    have h1 : ∑ k, c k * x k = ∑ i, y i * (A.mulVec x) i := by
      have e : ∀ k, c k * x k = (∑ i, y i * A i k) * x k := fun k => by rw [hyA k]
      rw [Finset.sum_congr rfl (fun k _ => e k)]
      simp only [Matrix.mulVec, dotProduct, Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun k _ => by ring))
    rw [h1, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun i _ => by ring)
  constructor
  · intro heq
    have hzero : ∑ i, y i * ((A.mulVec x) i - b i) = 0 := by rw [← hgap, heq]; ring
    have hnn : ∀ i ∈ Finset.univ, 0 ≤ y i * ((A.mulVec x) i - b i) := fun i _ =>
      mul_nonneg (hy0 i) (by linarith [hxi i])
    intro i
    exact (Finset.sum_eq_zero_iff_of_nonneg hnn).mp hzero i (Finset.mem_univ i)
  · intro h
    have : ∑ i, y i * ((A.mulVec x) i - b i) = 0 :=
      Finset.sum_eq_zero (fun i _ => h i)
    rw [this] at hgap
    linarith [hgap]
