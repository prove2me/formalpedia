-- Prove2me | solution 1 for TranscendenceTheory.formal_series_coefficient_denominator_bound
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-14T21:57:01.965337+00:00
-- url     : https://prove2.me/submissions/2a73eb20-e9dc-4cd6-9545-1a9e4c3807e9

import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Choose
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination

open PowerSeries

private lemma coeff_mul_split {S : Type*} [CommRing S]
    (q e : PowerSeries S) (k : ℕ) :
    coeff 0 q * coeff k e +
      ∑ j : Fin k, coeff (k - j.val) q * coeff j.val e = coeff k (q * e) := by
  rw [mul_comm q e, coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  rw [Finset.sum_range_succ]
  simp only [Nat.sub_self]
  rw [add_comm, Fin.sum_univ_eq_sum_range (fun j => coeff (k - j) q * coeff j e)]
  simp only [mul_comm]

theorem solution
    (R S : Type*) [CommRing R] [CommRing S]
    (φ : Polynomial R →+* S) (Q V : PowerSeries (Polynomial R))
    (E : PowerSeries S) (a b : ℕ)
    (h : PowerSeries.map φ Q * E = PowerSeries.map φ V)
    (hQ : ∀ k, (PowerSeries.coeff k Q).natDegree ≤ b)
    (hV : ∀ k, (PowerSeries.coeff k V).natDegree ≤ a) (k : ℕ) :
    ∃ P : Polynomial R, P.natDegree ≤ a + k * b ∧
      φ (PowerSeries.coeff 0 Q) ^ (k + 1) * PowerSeries.coeff k E = φ P := by
  classical
  induction k using Nat.strong_induction_on with
  | h k ih =>
    choose P hP using fun j : Fin k => ih j.val j.isLt
    let q := coeff 0 Q
    let T : Fin k → Polynomial R := fun j =>
      coeff (k - j.val) Q * q ^ (k - j.val - 1) * P j
    refine ⟨q ^ k * coeff k V - ∑ j : Fin k, T j, ?_, ?_⟩
    · apply (Polynomial.natDegree_sub_le _ _).trans
      apply max_le
      · exact (Polynomial.natDegree_mul_le_of_le
          (Polynomial.natDegree_pow_le_of_le k (hQ 0)) (hV k)).trans
          (by omega)
      · apply Polynomial.natDegree_sum_le_of_forall_le
        intro j _
        have hj : k - j.val - 1 + j.val + 1 = k := by omega
        have ht := Polynomial.natDegree_mul_le_of_le
          (Polynomial.natDegree_mul_le_of_le (hQ (k - j.val))
            (Polynomial.natDegree_pow_le_of_le (k - j.val - 1) (hQ 0))) (hP j).1
        apply ht.trans
        change b + (k - j.val - 1) * b + (a + j.val * b) ≤ a + k * b
        have hm := congrArg (fun t : ℕ => t * b) hj
        nlinarith only [hm]
    · have hc := coeff_mul_split (PowerSeries.map φ Q) E k
      rw [h] at hc
      simp only [coeff_map] at hc
      have ht (j : Fin k) :
          φ (T j) = φ q ^ k * (φ (coeff (k - j.val) Q) * coeff j.val E) := by
        have hj : k - j.val - 1 + (j.val + 1) = k := by omega
        dsimp [T]
        rw [map_mul, map_mul, map_pow, ← (hP j).2]
        change φ (coeff (k - j.val) Q) * φ q ^ (k - j.val - 1) *
          (φ q ^ (j.val + 1) * coeff j.val E) = _
        calc
          _ = φ q ^ (k - j.val - 1 + (j.val + 1)) *
              (φ (coeff (k - j.val) Q) * coeff j.val E) := by
            rw [pow_add]
            ring
          _ = _ := by rw [hj]
      simp only [map_sub, map_mul, map_pow, map_sum, ht]
      rw [← Finset.mul_sum]
      change φ q ^ (k + 1) * coeff k E =
        φ q ^ k * φ (coeff k V) - φ q ^ k *
          ∑ j : Fin k, φ (coeff (k - j.val) Q) * coeff j.val E
      rw [pow_succ]
      linear_combination φ q ^ k * hc
