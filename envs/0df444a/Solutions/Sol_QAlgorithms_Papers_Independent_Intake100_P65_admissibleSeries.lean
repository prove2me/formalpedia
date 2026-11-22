-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Intake100.P65.admissibleSeries
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-21T09:10:30.120182+00:00
-- url     : https://prove2.me/submissions/03703eea-142b-4870-9a9b-bf184b9492e2

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P65

noncomputable section

open scoped BigOperators TensorProduct

open QAlgorithms.Papers.Independent.Renew46.P16

open QAlgorithms.Papers.Independent.Support21.P08 (IrreducibleRepresentation)

open QAlgorithms.Papers.Independent.Support21.P12

open QAlgorithms.Papers.Independent.Support21.P14 (BrauerPairing oddPairingCount)

namespace QAlgorithms.Papers.Independent.Intake100.P65

universe u v

theorem reflect_zero {R : Type*} [CommRing R] [Invertible (2 : R)] (omega : ℕ → R) (a : ℕ) :
    ∑ b ∈ Finset.range (2*a), (-1 : R)^b * omega b * omega (2*a-1-b) = 0 := by
  set S := ∑ b ∈ Finset.range (2*a), (-1 : R)^b * omega b * omega (2*a-1-b) with hS
  have h2 : S = -S := by
    conv_lhs => rw [hS, ← Finset.sum_range_reflect]
    rw [hS, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun b hb => ?_
    have hb' := Finset.mem_range.mp hb
    have e1 : 2*a-1-(2*a-1-b) = b := by omega
    rw [e1]
    have e2 : (-1 : R)^(2*a-1-b) = -(-1 : R)^b := by
      have : (-1 : R)^(2*a-1-b) * (-1)^b = -1 := by
        rw [← pow_add]
        have : 2*a-1-b+b = 2*(a-1)+1 := by omega
        rw [this, pow_succ, pow_mul]; simp
      have hu : (-1 : R)^b * (-1)^b = 1 := by rw [← pow_add, ← two_mul, pow_mul]; simp
      calc (-1 : R)^(2*a-1-b) = (-1 : R)^(2*a-1-b) * ((-1)^b * (-1)^b) := by rw [hu, mul_one]
        _ = -(-1 : R)^b := by rw [← mul_assoc, this]; ring
    rw [e2]; ring
  have : (2 : R) * S = 0 := by linear_combination h2
  have := congrArg (fun x => ⅟(2:R) * x) this
  simpa [← mul_assoc] using this

theorem admissibleSeries (R : Type u) [CommRing R] [Invertible (2 : R)]
    (omega : ℕ → R) :
    OmegaAdmissible omega ↔
      (PowerSeries.X * PowerSeries.mk omega + 1 -
          PowerSeries.C (⅟ (2 : R)) * PowerSeries.X) *
        (PowerSeries.X * PowerSeries.mk (fun a => (-1 : R)^a * omega a) - 1 -
          PowerSeries.C (⅟ (2 : R)) * PowerSeries.X) =
      PowerSeries.C ((⅟ (2 : R))^2) * PowerSeries.X^2 - 1 := by
  set W := PowerSeries.mk omega with hW
  set V := PowerSeries.mk (fun a => (-1 : R)^a * omega a) with hV
  set c : R := ⅟ (2 : R) with hc
  have hc2 : c * 2 = 1 := by rw [hc]; simp
  set G := PowerSeries.X * (V * W) - W + V - PowerSeries.C c * PowerSeries.X * (W + V) with hG
  have hdiff : (PowerSeries.X * W + 1 - PowerSeries.C c * PowerSeries.X) *
        (PowerSeries.X * V - 1 - PowerSeries.C c * PowerSeries.X) -
      (PowerSeries.C (c^2) * PowerSeries.X^2 - 1) = PowerSeries.X * G := by
    rw [hG, map_pow]; ring
  have hc0 : PowerSeries.coeff 0 G = 0 := by
    simp [hG, hW, hV]
  have hcs : ∀ n, PowerSeries.coeff (n+1) G =
      (∑ k ∈ Finset.range (n+1), (-1 : R)^k * omega k * omega (n-k)) - omega (n+1)
        + (-1 : R)^(n+1) * omega (n+1) - c * (omega n + (-1 : R)^n * omega n) := by
    intro n
    rw [hG, map_sub, map_add, map_sub, PowerSeries.coeff_succ_X_mul, mul_assoc (PowerSeries.C c),
      PowerSeries.coeff_C_mul, PowerSeries.coeff_succ_X_mul, map_add, PowerSeries.coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    simp only [hW, hV, PowerSeries.coeff_mk]
  have key : (PowerSeries.X * W + 1 - PowerSeries.C c * PowerSeries.X) *
        (PowerSeries.X * V - 1 - PowerSeries.C c * PowerSeries.X) =
      PowerSeries.C (c^2) * PowerSeries.X^2 - 1 ↔ G = 0 := by
    rw [← sub_eq_zero, hdiff]
    constructor
    · intro h
      ext n
      have := congrArg (PowerSeries.coeff (n+1)) h
      simpa [PowerSeries.coeff_succ_X_mul] using this
    · intro h; rw [h, mul_zero]
  rw [key]
  constructor
  · intro hadm
    ext m
    rw [map_zero]
    rcases m with _ | n
    · exact hc0
    rw [hcs]
    rcases Nat.even_or_odd n with ⟨a, ha⟩ | ⟨a, ha⟩
    · have hn : n = 2*a := by omega
      subst hn
      have h1 := hadm a
      have e1 : (-1 : R)^(2*a+1) = -1 := by rw [pow_succ, pow_mul]; simp
      have e2 : (-1 : R)^(2*a) = 1 := by rw [pow_mul]; simp
      rw [e1, e2]
      linear_combination (-1 : R) * h1 - (omega (2*a)) * hc2
    · have hn : n = 2*(a+1)-1 := by omega
      have e1 : (-1 : R)^(n+1) = 1 := by rw [show n+1 = 2*(a+1) by omega, pow_mul]; simp
      have e2 : (-1 : R)^n = -1 := by rw [ha, pow_succ, pow_mul]; simp
      have hz := reflect_zero omega (a+1)
      rw [e1, e2]
      have hz' : ∑ k ∈ Finset.range (n+1), (-1 : R)^k * omega k * omega (n-k) = 0 := by
        rw [show n+1 = 2*(a+1) by omega]
        rw [← hz]
        refine Finset.sum_congr rfl fun b _ => ?_
        rw [show n - b = 2*(a+1)-1-b by omega]
      rw [hz']; ring
  · intro hG0 a
    have h := hcs (2*a)
    rw [hG0, map_zero] at h
    have e1 : (-1 : R)^(2*a+1) = -1 := by rw [pow_succ, pow_mul]; simp
    have e2 : (-1 : R)^(2*a) = 1 := by rw [pow_mul]; simp
    rw [e1, e2] at h
    linear_combination h - (omega (2*a)) * hc2

end QAlgorithms.Papers.Independent.Intake100.P65

end

theorem solution (R : Type*) [CommRing R] [Invertible (2 : R)]
    (omega : ℕ → R) :
    QAlgorithms.Papers.Independent.Intake100.P65.OmegaAdmissible omega ↔
      (PowerSeries.X * PowerSeries.mk omega + 1 -
          PowerSeries.C (⅟ (2 : R)) * PowerSeries.X) *
        (PowerSeries.X * PowerSeries.mk (fun a => (-1 : R)^a * omega a) - 1 -
          PowerSeries.C (⅟ (2 : R)) * PowerSeries.X) =
      PowerSeries.C ((⅟ (2 : R))^2) * PowerSeries.X^2 - 1 :=
  QAlgorithms.Papers.Independent.Intake100.P65.admissibleSeries R omega
