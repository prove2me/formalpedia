-- Prove2me | solution 1 for TranscendenceTheory.finite_family_common_denominator
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-14T22:10:42.525604+00:00
-- url     : https://prove2.me/submissions/3eb5360d-4bfc-483f-80cc-ea6703a32bc9

import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

private lemma product_power_degree {R ι : Type*} [CommSemiring R]
    (q : ι → Polynomial R) (d N : ℕ) (hq : ∀ r, (q r).natDegree ≤ d) (s : Finset ι) :
    (∏ r ∈ s, q r ^ N).natDegree ≤ s.card * (N * d) := by
  calc
    _ ≤ ∑ r ∈ s, (q r ^ N).natDegree := Polynomial.natDegree_prod_le _ _
    _ ≤ ∑ _r ∈ s, N * d := Finset.sum_le_sum fun r _ =>
      Polynomial.natDegree_pow_le_of_le N (hq r)
    _ = _ := by simp

theorem solution
    (R ι : Type*) [CommSemiring R] [Fintype ι]
    (q : ι → Polynomial R) (H : ι → PowerSeries R) (d N : ℕ)
    (hq : ∀ r, (q r).natDegree ≤ d)
    (hH : ∀ r, (q r : PowerSeries R) * H r = 1)
    (P : ι → Fin N → Polynomial R)
    (hP : ∀ r k, (P r k).natDegree < d * (k.val + 1)) :
    let D : Polynomial R := ∏ r, q r ^ N
    D.natDegree ≤ d * N * Fintype.card ι ∧
      ∀ r k, ∃ A : Polynomial R, A.natDegree < d * N * Fintype.card ι ∧
        (D : PowerSeries R) * ((P r k : PowerSeries R) * H r ^ (k.val + 1)) =
          (A : PowerSeries R) := by
  classical
  dsimp only
  constructor
  · exact (product_power_degree q d N hq Finset.univ).trans (by simp [mul_comm, mul_left_comm])
  · intro r k
    let V : Polynomial R := ∏ t ∈ Finset.univ.erase r, q t ^ N
    have hdegV : V.natDegree ≤ (Finset.univ.erase r).card * (N * d) :=
      product_power_degree q d N hq (Finset.univ.erase r)
    have hcard : (Finset.univ.erase r).card + 1 = Fintype.card ι := by
      exact Finset.card_erase_add_one (Finset.mem_univ r)
    have hk : N - (k.val + 1) + (k.val + 1) = N := by omega
    refine ⟨P r k * q r ^ (N - (k.val + 1)) * V, ?_, ?_⟩
    · have hb := Polynomial.natDegree_mul_le_of_le
        (Polynomial.natDegree_mul_le_of_le (le_refl (P r k).natDegree)
          (Polynomial.natDegree_pow_le_of_le (N - (k.val + 1)) (hq r))) hdegV
      have hsum : d * (k.val + 1) + (N - (k.val + 1)) * d +
          (Finset.univ.erase r).card * (N * d) = d * N * Fintype.card ι := by
        calc
          _ = d * (N - (k.val + 1) + (k.val + 1)) +
              (Finset.univ.erase r).card * (N * d) := by ring
          _ = d * N + (Finset.univ.erase r).card * (N * d) := by rw [hk]
          _ = d * N * ((Finset.univ.erase r).card + 1) := by ring
          _ = _ := by rw [hcard]
      have hp := hP r k
      omega
    · have hpow : (q r : PowerSeries R) ^ N * H r ^ (k.val + 1) =
          (q r : PowerSeries R) ^ (N - (k.val + 1)) := by
        calc
          _ = (q r : PowerSeries R) ^ (N - (k.val + 1) + (k.val + 1)) *
              H r ^ (k.val + 1) := by rw [hk]
          _ = (q r : PowerSeries R) ^ (N - (k.val + 1)) *
              ((q r : PowerSeries R) * H r) ^ (k.val + 1) := by
            rw [pow_add, mul_pow]
            ring
          _ = _ := by rw [hH r, one_pow, mul_one]
      have hD : (∏ t, q t ^ N) = q r ^ N * V :=
        (Finset.mul_prod_erase Finset.univ (fun t => q t ^ N) (Finset.mem_univ r)).symm
      rw [hD]
      simp only [Polynomial.coe_mul, Polynomial.coe_pow]
      calc
        _ = ((P r k : PowerSeries R) * (V : PowerSeries R)) *
            ((q r : PowerSeries R) ^ N * H r ^ (k.val + 1)) := by ring
        _ = _ := by rw [hpow]; ring
