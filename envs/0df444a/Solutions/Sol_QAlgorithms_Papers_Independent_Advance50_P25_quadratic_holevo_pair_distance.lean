-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Advance50.P25.quadratic_holevo_pair_distance
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-11T20:13:51.97768+00:00
-- url     : https://prove2.me/submissions/961380a8-7e70-4db0-815a-66dbe8be1bd7

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P25

open scoped Matrix ComplexConjugate ComplexOrder

open QAlgorithms.Papers.Independent.Information100.P56 (IsLaw average entropy)

namespace Aux_QHPD

theorem key {m : ℕ} (g : Fin m → Fin m → ℝ) (hs : ∀ j k, g j k = g k j) (hd : ∀ j, g j j = 0) :
    ∑ j, ∑ k, g j k = 2 * ∑ j : Fin m, ∑ k : Fin m with j < k, g j k := by
  have h1 : ∀ j, ∑ k, g j k = (∑ k : Fin m with j < k, g j k) + ∑ k : Fin m with k < j, g j k := by
    intro j
    rw [Finset.sum_filter, Finset.sum_filter, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k _
    rcases lt_trichotomy j k with h | h | h
    · simp [h, lt_asymm h]
    · subst h
      simp [hd]
    · simp [h, lt_asymm h]
  have h2 : ∑ j : Fin m, ∑ k : Fin m with k < j, g j k =
      ∑ j : Fin m, ∑ k : Fin m with j < k, g j k := by
    simp only [Finset.sum_filter]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    rw [hs b a]
  rw [Finset.sum_congr rfl (fun j _ => h1 j), Finset.sum_add_distrib, h2]
  ring

end Aux_QHPD

open QAlgorithms.Papers.Independent.Advance50.P25 in
theorem solution {I : Type}
    [Fintype I] [DecidableEq I] [Nonempty I] {m : ℕ}
    (p : Fin m → ℝ) (rho : Fin m → Matrix I I ℂ) (hens : DensityEnsemble p rho) :
    generalEntropyHolevo quadraticEntropy p rho =
      ∑ j : Fin m, ∑ k : Fin m with j < k,
        p j * p k * hilbertSchmidtDistance (rho j) (rho k) := by
  have hsum : ∑ j, p j = 1 := hens.1.2
  have hA : (average rho p * average rho p).trace.re =
      ∑ j, ∑ k, p j * p k * (rho j * rho k).trace.re := by
    simp [average, Finset.sum_mul, Finset.mul_sum, Matrix.trace_sum, Complex.re_sum, mul_assoc]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro k _
    rw [Matrix.trace_mul_comm]
  have hB : ∀ j k, ((rho j - rho k) * (rho j - rho k)).trace.re =
      (rho j * rho j).trace.re + (rho k * rho k).trace.re - 2 * (rho j * rho k).trace.re := by
    intro j k
    have hc : (rho k * rho j).trace = (rho j * rho k).trace := Matrix.trace_mul_comm _ _
    simp only [sub_mul, mul_sub, Matrix.trace_sub, Complex.sub_re, hc]
    ring
  have hK := Aux_QHPD.key
    (fun j k => p j * p k * ((rho j * rho j).trace.re + (rho k * rho k).trace.re -
      2 * (rho j * rho k).trace.re))
    (fun j k => by
      have hc : (rho k * rho j).trace = (rho j * rho k).trace := Matrix.trace_mul_comm _ _
      simp only [hc]
      ring)
    (fun j => by ring)
  have e1 : ∑ j, ∑ k, p j * p k * (rho j * rho j).trace.re = ∑ j, p j * (rho j * rho j).trace.re := by
    apply Finset.sum_congr rfl
    intro j _
    have : ∑ k, p j * p k * (rho j * rho j).trace.re =
        p j * (rho j * rho j).trace.re * ∑ k, p k := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      ring
    rw [this, hsum, mul_one]
  have e2 : ∑ j, ∑ k, p j * p k * (rho k * rho k).trace.re = ∑ j, p j * (rho j * rho j).trace.re := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro k _
    have : ∑ j, p j * p k * (rho k * rho k).trace.re =
        p k * (rho k * rho k).trace.re * ∑ j, p j := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring
    rw [this, hsum, mul_one]
  have hG : ∑ j, ∑ k, p j * p k * ((rho j * rho j).trace.re + (rho k * rho k).trace.re -
      2 * (rho j * rho k).trace.re) =
      ∑ j, ∑ k, p j * p k * (rho j * rho j).trace.re +
        ∑ j, ∑ k, p j * p k * (rho k * rho k).trace.re -
        2 * ∑ j, ∑ k, p j * p k * (rho j * rho k).trace.re := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j _
    rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro k _
    ring
  have e3 : ∑ j, p j * (1 - (rho j * rho j).trace.re) =
      1 - ∑ j, p j * (rho j * rho j).trace.re := by
    have hpt : ∀ j, p j * (1 - (rho j * rho j).trace.re) =
        p j - p j * (rho j * rho j).trace.re := fun j => by ring
    simp_rw [hpt]
    rw [Finset.sum_sub_distrib, hsum]
  simp only [generalEntropyHolevo, quadraticEntropy, hilbertSchmidtDistance]
  rw [hA, e3]
  simp_rw [hB]
  linarith [hK, hG, e1, e2]
