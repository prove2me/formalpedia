-- Prove2me | solution 1 for SurgeryStepTypeI
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:14:33.643895+00:00
-- url     : https://prove2.me/submissions/b08164be-08ad-46fa-9c43-55963fb1d9a1

import Definitions.Def_Tablet_surgeryPotential
import Definitions.Def_Tablet_SurgeryStepTypeI

set_option autoImplicit false

theorem _root_.solution (δ ε : ℝ) (n : ℕ) (hε0 : 0 < ε) (hε1 : ε < 1)
    (hδ : 0 < δ) (hn : 0 < n) (L L' Ld β : ℝ) (m m' : ℕ)
    (hL'0 : 0 ≤ L') (hbeta : δ ≤ β)
    (hlen : L' ≤ L - (1 - ε) * β) (htot : L' + Ld ≤ L + 2 * ε * β)
    (hm : m' ≤ m + 3) :
    (n + 3) * ⌊L' / ((1 - ε) * δ)⌋₊ + m' + n
        ≤ (n + 3) * ⌊L / ((1 - ε) * δ)⌋₊ + m
      ∧ Ld + surgeryPotential ε δ n L' m' ≤ surgeryPotential ε δ n L m := by
-- BODY
  have h1e : (0:ℝ) < 1 - ε := by linarith
  have hc : (0:ℝ) < (1 - ε) * δ := mul_pos h1e hδ
  have hnR : (0:ℝ) < (n:ℝ) := by exact_mod_cast hn
  have hgap : (1 - ε) * δ ≤ L - L' := by nlinarith
  constructor
  · -- Measure drop: the length gap is at least one full step `(1-ε)δ`, so the floor term drops.
    have hd1 : L' / ((1 - ε) * δ) + 1 ≤ L / ((1 - ε) * δ) := by
      rw [div_add' _ _ _ (ne_of_gt hc), div_le_div_iff_of_pos_right hc]
      linarith
    have hfl : ⌊L' / ((1 - ε) * δ)⌋₊ + 1 ≤ ⌊L / ((1 - ε) * δ)⌋₊ := by
      have h0 : (0:ℝ) ≤ L' / ((1 - ε) * δ) := div_nonneg hL'0 hc.le
      rw [← Nat.floor_add_one h0]
      exact Nat.floor_le_floor hd1
    have hmul : (n + 3) * (⌊L' / ((1 - ε) * δ)⌋₊ + 1) ≤ (n + 3) * ⌊L / ((1 - ε) * δ)⌋₊ :=
      Nat.mul_le_mul (le_refl (n + 3)) hfl
    rw [Nat.mul_succ] at hmul
    generalize (n + 3) * ⌊L' / ((1 - ε) * δ)⌋₊ = a at hmul ⊢
    generalize (n + 3) * ⌊L / ((1 - ε) * δ)⌋₊ = b at hmul ⊢
    omega
  · -- Length step: `(A-1)(1-ε) = 2ε + 12ε⁻¹/n` and `3C = (12ε⁻¹/n)δ ≤ (12ε⁻¹/n)β`.
    simp only [surgeryPotential]
    have hA1 : (0:ℝ) ≤ 2 * ε / (1 - ε) + 12 * ε⁻¹ / ((n : ℝ) * (1 - ε)) := by positivity
    have hCpos : (0:ℝ) < 4 * ε⁻¹ * δ / (n : ℝ) := by positivity
    have hKpos : (0:ℝ) < 12 * ε⁻¹ / (n : ℝ) := by positivity
    have hstep1 : (2 * ε / (1 - ε) + 12 * ε⁻¹ / ((n : ℝ) * (1 - ε))) * ((1 - ε) * β)
        ≤ (2 * ε / (1 - ε) + 12 * ε⁻¹ / ((n : ℝ) * (1 - ε))) * (L - L') :=
      mul_le_mul_of_nonneg_left (by linarith) hA1
    have hid : (2 * ε / (1 - ε) + 12 * ε⁻¹ / ((n : ℝ) * (1 - ε))) * ((1 - ε) * β)
        = 2 * ε * β + (12 * ε⁻¹ / (n : ℝ)) * β := by field_simp
    have hmR : (m' : ℝ) ≤ (m : ℝ) + 3 := by exact_mod_cast hm
    have hstep2 : 4 * ε⁻¹ * δ / (n : ℝ) * (m' : ℝ)
        ≤ 4 * ε⁻¹ * δ / (n : ℝ) * ((m : ℝ) + 3) :=
      mul_le_mul_of_nonneg_left hmR hCpos.le
    have h3C : 4 * ε⁻¹ * δ / (n : ℝ) * 3 = (12 * ε⁻¹ / (n : ℝ)) * δ := by field_simp; ring
    have hKb : (12 * ε⁻¹ / (n : ℝ)) * δ ≤ (12 * ε⁻¹ / (n : ℝ)) * β :=
      mul_le_mul_of_nonneg_left hbeta hKpos.le
    nlinarith [hstep1, hid, hstep2, h3C, hKb, htot]
