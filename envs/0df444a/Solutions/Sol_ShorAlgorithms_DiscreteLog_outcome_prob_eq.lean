-- Prove2me | solution 1 for ShorAlgorithms.DiscreteLog.outcome_prob_eq
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T16:11:47.263541+00:00
-- url     : https://prove2.me/submissions/40a64ba7-b5aa-4332-9f36-fefb591db2b6

import Mathlib
import Definitions.Def_ShorAlgorithms_DiscreteLog_outcomeProb
open ShorAlgorithms.DiscreteLog ShorAlgorithms.Shared
namespace AShorLog

lemma sqrt_inv_sq (q : ℕ) : ((Real.sqrt q : ℝ) : ℂ)⁻¹ * ((Real.sqrt q : ℝ) : ℂ)⁻¹ = (q : ℂ)⁻¹ := by
  rw [← mul_inv, ← Complex.ofReal_mul, Real.mul_self_sqrt (Nat.cast_nonneg q)]
  rfl

lemma sum_trunc {N q : ℕ} (hNq : N ≤ q) (F : ℕ → ℂ) :
    (∑ i : Fin q, if (i : ℕ) < N then F i else 0) = ∑ i ∈ Finset.range N, F i := by
  classical
  rw [← Finset.sum_range (fun i => if i < N then F i else 0)]
  calc
    _ = ∑ i ∈ Finset.range N, if i < N then F i else 0 := by
      symm
      apply Finset.sum_subset (Finset.range_mono hNq)
      intro i hi hin
      simp only [Finset.mem_range] at hin
      simp [hin]
    _ = _ := by apply Finset.sum_congr rfl; intro i hi; simp [Finset.mem_range.mp hi]

lemma power_congruence (p : ℕ) [hp : Fact p.Prime] (g : (ZMod p)ˣ) (hg : orderOf g = p - 1)
    (a b r k : ℕ) :
    (g ^ k = g ^ a * (g ^ r)⁻¹ ^ b) ↔
      (a : ℤ) - (r : ℤ) * (b : ℤ) ≡ (k : ℤ) [ZMOD ((p : ℤ) - 1)] := by
  have he : g ^ ((a : ℤ) - (r : ℤ) * b) = g ^ a * (g ^ r)⁻¹ ^ b := by
    rw [zpow_sub, zpow_natCast, zpow_mul, zpow_natCast, zpow_natCast, inv_pow]
  rw [← he, ← zpow_natCast g k, eq_comm, zpow_eq_zpow_iff_modEq, hg, Nat.cast_sub hp.out.one_le]
  simp only [Nat.cast_one]

lemma coefficient (p q a b c d : ℕ) :
    (((p - 1 : ℕ) : ℂ))⁻¹ *
      (((Real.sqrt q : ℝ) : ℂ)⁻¹ * Complex.exp (2 * Real.pi * Complex.I * (a : ℂ) * (c : ℂ) / (q : ℂ))) *
      (((Real.sqrt q : ℝ) : ℂ)⁻¹ * Complex.exp (2 * Real.pi * Complex.I * (b : ℂ) * (d : ℂ) / (q : ℂ))) =
    (1 / (((p - 1 : ℕ) : ℂ) * (q : ℂ))) * Complex.exp
      (2 * Real.pi * Complex.I / (q : ℂ) * ((a : ℂ) * c + (b : ℂ) * d)) := by
  calc
    _ = (((p - 1 : ℕ) : ℂ))⁻¹ *
      (((Real.sqrt q : ℝ) : ℂ)⁻¹ * ((Real.sqrt q : ℝ) : ℂ)⁻¹) *
      (Complex.exp (2 * Real.pi * Complex.I * (a : ℂ) * (c : ℂ) / (q : ℂ)) *
       Complex.exp (2 * Real.pi * Complex.I * (b : ℂ) * (d : ℂ) / (q : ℂ))) := by ring
    _ = _ := by
      rw [sqrt_inv_sq, ← Complex.exp_add]
      simp only [one_div, mul_inv]
      congr 2
      ring

lemma amplitude (p : ℕ) [hp : Fact p.Prime] (g : (ZMod p)ˣ) (hg : orderOf g = p - 1)
    (r q k : ℕ) (hpq : p < q) (c d : Fin q) :
    finalState p g (g ^ r) q (c, d, g ^ k) =
      (1 / (((p : ℂ) - 1) * (q : ℂ))) *
        ∑ a ∈ Finset.range (p - 1), ∑ b ∈ Finset.range (p - 1),
          if (a : ℤ) - (r : ℤ) * (b : ℤ) ≡ (k : ℤ) [ZMOD ((p : ℤ) - 1)] then
            Complex.exp (2 * Real.pi * Complex.I / (q : ℂ) *
              ((a : ℂ) * ((c : ℕ) : ℂ) + (b : ℂ) * ((d : ℕ) : ℂ)))
          else 0 := by
  classical
  let F (a b : ℕ) : ℂ := if (a : ℤ) - (r : ℤ) * (b : ℤ) ≡ (k : ℤ) [ZMOD ((p : ℤ) - 1)] then
    Complex.exp (2 * Real.pi * Complex.I / (q : ℂ) * ((a : ℂ) * (c : ℕ) + (b : ℂ) * (d : ℕ))) else 0
  have hN : p - 1 ≤ q := by omega
  have he : finalState p g (g ^ r) q (c, d, g ^ k) =
      (1 / (((p - 1 : ℕ) : ℂ) * (q : ℂ))) * ∑ a : Fin q,
        if (a : ℕ) < p - 1 then ∑ b : Fin q, if (b : ℕ) < p - 1 then F a b else 0 else 0 := by
    simp only [finalState, preFourierState, fourierMatrix, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    by_cases ha : (a : ℕ) < p - 1
    · simp only [ha, true_and, if_true, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro b _
      by_cases hb : (b : ℕ) < p - 1
      · simp only [hb, true_and, if_true, power_congruence p g hg, F]
        split_ifs
        · exact coefficient p q a b c d
        · simp
      · simp [hb]
    · simp [ha]
  rw [he, sum_trunc hN (fun a => ∑ b : Fin q, if (b : ℕ) < p - 1 then F a b else 0)]
  have hb (a : ℕ) := sum_trunc hN (F a)
  simp_rw [hb]
  simp only [Nat.cast_sub hp.out.one_le, Nat.cast_one, F]

end AShorLog

theorem solution (p : ℕ) [hp : Fact p.Prime] (g : (ZMod p)ˣ) (hg : orderOf g = p - 1)
    (r : ℕ) (hr : r < p - 1) (q l : ℕ) (hq : q = 2 ^ l) (hpq : p < q) (hqp : q < 2 * p)
    (c d : Fin q) (k : ℕ) (hk : k < p - 1) :
    outcomeProb p g (g ^ r) q c d (g ^ k) =
      ‖(1 / (((p : ℂ) - 1) * (q : ℂ))) *
        ∑ a ∈ Finset.range (p - 1), ∑ b ∈ Finset.range (p - 1),
          if (a : ℤ) - (r : ℤ) * (b : ℤ) ≡ (k : ℤ) [ZMOD ((p : ℤ) - 1)] then
            Complex.exp (2 * Real.pi * Complex.I / (q : ℂ) *
              ((a : ℂ) * ((c : ℕ) : ℂ) + (b : ℂ) * ((d : ℕ) : ℂ)))
          else 0‖ ^ 2  := by
  unfold ShorAlgorithms.DiscreteLog.outcomeProb
  rw [AShorLog.amplitude p g hg r q k hpq c d]
