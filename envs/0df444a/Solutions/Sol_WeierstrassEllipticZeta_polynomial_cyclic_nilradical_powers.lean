-- Prove2me | solution 1 for WeierstrassEllipticZeta.polynomial_cyclic_nilradical_powers
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-12T19:55:52.038057+00:00
-- url     : https://prove2.me/submissions/b8cc91a6-72ad-4b13-b47f-f459b4bf2257

import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.Eval.Algebra
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.RingTheory.Nilpotent.Lemmas



open Polynomial

theorem solution
    (K A : Type*) [Field K] [CommRing A] [Algebra K A]
    (x : A) (z : K)
    (hsurj : Function.Surjective (fun q : Polynomial K =>
      q.eval₂ (algebraMap K A) x))
    (hnil : ∀ q : Polynomial K,
      IsNilpotent (q.eval₂ (algebraMap K A) x) ↔ q.eval z = 0) :
    nilradical A = Ideal.span {x - algebraMap K A z} ∧
      ∀ k : ℕ,
        (nilradical A) ^ k = Ideal.span {(x - algebraMap K A z) ^ k} ∧
        ((nilradical A) ^ k = ⊥ ↔ nilpotencyClass (x - algebraMap K A z) ≤ k) := by
  have hx : IsNilpotent (x - algebraMap K A z) := by
    have h := (hnil (X - C z)).mpr (by simp)
    change IsNilpotent ((X - C z).eval₂ (algebraMap K A) x) at h
    rw [eval₂_sub, eval₂_X, eval₂_C] at h
    exact h
  have hN : nilradical A = Ideal.span {x - algebraMap K A z} := by
    apply le_antisymm
    · intro a ha
      obtain ⟨q, rfl⟩ := hsurj a
      have hq : q.eval z = 0 := (hnil q).mp (mem_nilradical.mp ha)
      obtain ⟨r, hr⟩ := dvd_iff_isRoot.mpr hq
      simp only [hr, eval₂_mul, eval₂_sub, eval₂_X, eval₂_C]
      exact Ideal.mul_mem_right _ _ (Ideal.subset_span (Set.mem_singleton _))
    · exact Ideal.span_le.mpr (Set.singleton_subset_iff.mpr (mem_nilradical.mpr hx))
  refine ⟨hN, fun k => ?_⟩
  have hp : (nilradical A) ^ k = Ideal.span {(x - algebraMap K A z) ^ k} := by
    rw [hN, Ideal.span_singleton_pow]
  refine ⟨hp, ?_⟩
  rw [hp, Ideal.span_singleton_eq_bot]
  exact ⟨fun h => Nat.sInf_le h, fun h => pow_eq_zero_of_le h (pow_nilpotencyClass hx)⟩

