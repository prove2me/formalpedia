-- Prove2me | solution 1 for SurgeryStepTypeII
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:15:02.582018+00:00
-- url     : https://prove2.me/submissions/24270738-654d-4a07-8cf7-b79d75f90877

import Definitions.Def_Tablet_surgeryPotential
import Definitions.Def_Tablet_SurgeryStepTypeII

set_option autoImplicit false

theorem _root_.solution (δ ε : ℝ) (n : ℕ) (hε0 : 0 < ε) (hε1 : ε < 1)
    (hδ : 0 < δ) (hn : 0 < n) (L L' Ld : ℝ) (m m' : ℕ)
    (hlen : L' ≤ L) (htot : L' + Ld ≤ L + 4 * ε⁻¹ * δ) (hm : m' + n ≤ m) :
    (n + 3) * ⌊L' / ((1 - ε) * δ)⌋₊ + m' + n
        ≤ (n + 3) * ⌊L / ((1 - ε) * δ)⌋₊ + m
      ∧ Ld + surgeryPotential ε δ n L' m' ≤ surgeryPotential ε δ n L m := by
-- BODY
  have h1e : (0:ℝ) < 1 - ε := by linarith
  have hc : (0:ℝ) < (1 - ε) * δ := mul_pos h1e hδ
  have hnR : (0:ℝ) < (n:ℝ) := by exact_mod_cast hn
  constructor
  · -- Measure drop: the floor term is monotone and the small-edge count drops by at least `n`.
    have hdiv : L' / ((1 - ε) * δ) ≤ L / ((1 - ε) * δ) := by gcongr
    have hfl : ⌊L' / ((1 - ε) * δ)⌋₊ ≤ ⌊L / ((1 - ε) * δ)⌋₊ := Nat.floor_le_floor hdiv
    have hmul : (n + 3) * ⌊L' / ((1 - ε) * δ)⌋₊ ≤ (n + 3) * ⌊L / ((1 - ε) * δ)⌋₊ :=
      Nat.mul_le_mul (le_refl (n + 3)) hfl
    generalize (n + 3) * ⌊L' / ((1 - ε) * δ)⌋₊ = a at hmul ⊢
    generalize (n + 3) * ⌊L / ((1 - ε) * δ)⌋₊ = b at hmul ⊢
    omega
  · -- Length step: `A ≥ 1` absorbs the length gap, and `C·n = 4ε⁻¹δ` pays the cut cost.
    simp only [surgeryPotential]
    have hA1 : (0:ℝ) ≤ 2 * ε / (1 - ε) + 12 * ε⁻¹ / ((n : ℝ) * (1 - ε)) := by positivity
    have hCpos : (0:ℝ) < 4 * ε⁻¹ * δ / (n : ℝ) := by positivity
    have hstep1 : (2 * ε / (1 - ε) + 12 * ε⁻¹ / ((n : ℝ) * (1 - ε))) * L'
        ≤ (2 * ε / (1 - ε) + 12 * ε⁻¹ / ((n : ℝ) * (1 - ε))) * L :=
      mul_le_mul_of_nonneg_left hlen hA1
    have hmR : (m' : ℝ) + (n : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    have hCn : 4 * ε⁻¹ * δ / (n : ℝ) * (n : ℝ) = 4 * ε⁻¹ * δ := by field_simp
    have hstep2 : 4 * ε⁻¹ * δ / (n : ℝ) * ((m' : ℝ) + (n : ℝ))
        ≤ 4 * ε⁻¹ * δ / (n : ℝ) * (m : ℝ) :=
      mul_le_mul_of_nonneg_left hmR hCpos.le
    nlinarith [hstep1, hstep2, hCn, htot]
