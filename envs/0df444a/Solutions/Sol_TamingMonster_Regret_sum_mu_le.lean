-- Prove2me | solution 1 for TamingMonster.Regret.sum_mu_le
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-01T17:12:17.389685+00:00
-- url     : https://prove2.me/submissions/250838d0-f621-49fb-84d2-b2b1a977fc53

import Mathlib
import Definitions.Def_TamingMonster_Regret_Setting
import Definitions.Def_TamingMonster_Regret_Algorithm
import Definitions.Def_TamingMonster_Regret_Analysis

set_option autoImplicit false

namespace TamingMonster.Regret

lemma d3b8_sum_inv_sqrt_le (T : ℕ) :
    ∑ t ∈ Finset.Icc 1 T, 1 / Real.sqrt (t : ℝ) ≤ 2 * Real.sqrt (T : ℝ) := by
  induction T with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_Icc_succ_top (by omega)]
    set a := Real.sqrt (n : ℝ) with ha
    set b := Real.sqrt ((n + 1 : ℕ) : ℝ) with hb
    have ha0 : 0 ≤ a := Real.sqrt_nonneg _
    have hb0 : 0 < b := Real.sqrt_pos.mpr (by positivity)
    have ha2 : a ^ 2 = (n : ℝ) := Real.sq_sqrt (by positivity)
    have hb2 : b ^ 2 = (n : ℝ) + 1 := by
      rw [hb, Real.sq_sqrt (by positivity)]; push_cast; ring
    have hab : a ≤ b := Real.sqrt_le_sqrt (by push_cast; linarith)
    have key : 1 / b ≤ 2 * b - 2 * a := by
      rw [div_le_iff₀ hb0]
      nlinarith [mul_le_mul_of_nonneg_right (show 2 * a ≤ a + b by linarith)
        (show 0 ≤ b - a by linarith)]
    linarith

lemma d3b8_epoch_spec {τ : ℕ → ℕ} (hτ0 : τ 0 = 0) (hτ : StrictMono τ) {t : ℕ} (ht : 1 ≤ t) :
    t ≤ τ (epochOf τ t) ∧ epochOf τ t ≠ 0 := by
  have hne : ({m : ℕ | t ≤ τ m} : Set ℕ).Nonempty := ⟨t, hτ.le_apply⟩
  have hmem := Nat.sInf_mem hne
  refine ⟨hmem, ?_⟩
  intro h0
  have : t ≤ τ (epochOf τ t) := hmem
  rw [h0, hτ0] at this
  omega

lemma d3b8_epoch_mono {τ : ℕ → ℕ} (hτ : StrictMono τ) {t T : ℕ} (htT : t ≤ T) :
    epochOf τ t ≤ epochOf τ T := by
  have hne : ({m : ℕ | T ≤ τ m} : Set ℕ).Nonempty := ⟨T, hτ.le_apply⟩
  have hmem : T ≤ τ (epochOf τ T) := Nat.sInf_mem hne
  exact Nat.sInf_le (show t ≤ τ (epochOf τ T) from le_trans htT hmem)

end TamingMonster.Regret

open MeasureTheory TamingMonster.Regret in
theorem solution {X : Type*} {K : ℕ} [NeZero K] (Pi : Finset (X → Fin K))
    (hPi : Pi.Nonempty) (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (τ : ℕ → ℕ) (hτ0 : τ 0 = 0) (hτ : StrictMono τ) (T : ℕ) :
    ∑ t ∈ Finset.Icc 1 T, muM Pi δ τ (epochOf τ t) ≤
      2 * Real.sqrt (dT Pi δ (τ (epochOf τ T)) * (τ (epochOf τ T) : ℝ) / (K : ℝ)) := by
  rcases Nat.eq_zero_or_pos T with hT | hT
  · subst hT
    simp only [Finset.Icc_eq_empty_of_lt (show 0 < 1 by norm_num), Finset.sum_empty]
    positivity
  set M := epochOf τ T with hM
  have hKpos : (0 : ℝ) < K := by
    have : K ≠ 0 := NeZero.ne K
    exact_mod_cast Nat.pos_of_ne_zero this
  have hcard : (1 : ℝ) ≤ (Pi.card : ℝ) := by exact_mod_cast hPi.card_pos
  -- dT is monotone on positive naturals and nonnegative there
  have hd_nonneg : ∀ s : ℕ, 1 ≤ s → 0 ≤ dT Pi δ s := by
    intro s hs
    unfold dT
    apply Real.log_nonneg
    rw [le_div_iff₀ hδ0]
    have : (1 : ℝ) ≤ (s : ℝ) := by exact_mod_cast hs
    nlinarith
  have hd_mono : ∀ s s' : ℕ, 1 ≤ s → s ≤ s' → dT Pi δ s ≤ dT Pi δ s' := by
    intro s s' hs hss'
    unfold dT
    have h1 : (1 : ℝ) ≤ (s : ℝ) := by exact_mod_cast hs
    have h2 : (s : ℝ) ≤ (s' : ℝ) := by exact_mod_cast hss'
    apply Real.log_le_log
    · positivity
    · apply div_le_div_of_nonneg_right _ hδ0.le
      have : (s : ℝ) ^ 2 ≤ (s' : ℝ) ^ 2 := by nlinarith
      have hc : (0 : ℝ) ≤ Pi.card := by positivity
      nlinarith
  obtain ⟨hTM, hM0⟩ := d3b8_epoch_spec hτ0 hτ (show 1 ≤ T from hT)
  have hτM1 : 1 ≤ τ M := le_trans hT hTM
  set D := dT Pi δ (τ M) / (K : ℝ) with hD
  have hD0 : 0 ≤ D := div_nonneg (hd_nonneg _ hτM1) hKpos.le
  have hterm : ∀ t ∈ Finset.Icc 1 T,
      muM Pi δ τ (epochOf τ t) ≤ Real.sqrt D * (1 / Real.sqrt (t : ℝ)) := by
    intro t ht
    rw [Finset.mem_Icc] at ht
    obtain ⟨htm, hm0⟩ := d3b8_epoch_spec hτ0 hτ ht.1
    have hmM : epochOf τ t ≤ M := d3b8_epoch_mono hτ ht.2
    have hτmM : τ (epochOf τ t) ≤ τ M := hτ.monotone hmM
    have hτm1 : 1 ≤ τ (epochOf τ t) := le_trans ht.1 htm
    have htpos : (0 : ℝ) < (t : ℝ) := by exact_mod_cast ht.1
    have ht_le : (t : ℝ) ≤ (τ (epochOf τ t) : ℝ) := by exact_mod_cast htm
    unfold muM
    rw [if_neg hm0]
    refine le_trans (min_le_right _ _) ?_
    rw [one_div, ← Real.sqrt_inv, ← Real.sqrt_mul hD0]
    apply Real.sqrt_le_sqrt
    have hre : D * (t : ℝ)⁻¹ = dT Pi δ (τ M) / ((K : ℝ) * (t : ℝ)) := by
      rw [hD]; field_simp
    rw [hre]
    apply div_le_div₀ (hd_nonneg _ hτM1) (hd_mono _ _ hτm1 hτmM) (by positivity)
    exact mul_le_mul_of_nonneg_left ht_le hKpos.le
  calc ∑ t ∈ Finset.Icc 1 T, muM Pi δ τ (epochOf τ t)
      ≤ ∑ t ∈ Finset.Icc 1 T, Real.sqrt D * (1 / Real.sqrt (t : ℝ)) := Finset.sum_le_sum hterm
    _ = Real.sqrt D * ∑ t ∈ Finset.Icc 1 T, 1 / Real.sqrt (t : ℝ) := by rw [Finset.mul_sum]
    _ ≤ Real.sqrt D * (2 * Real.sqrt (T : ℝ)) :=
        mul_le_mul_of_nonneg_left (d3b8_sum_inv_sqrt_le T) (Real.sqrt_nonneg _)
    _ ≤ Real.sqrt D * (2 * Real.sqrt (τ M : ℝ)) := by
        apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg _)
        have : (T : ℝ) ≤ (τ M : ℝ) := by exact_mod_cast hTM
        linarith [Real.sqrt_le_sqrt this]
    _ = 2 * Real.sqrt (dT Pi δ (τ M) * (τ M : ℝ) / (K : ℝ)) := by
        have hre : dT Pi δ (τ M) * (τ M : ℝ) / (K : ℝ) = D * (τ M : ℝ) := by
          rw [hD]; ring
        rw [hre, Real.sqrt_mul hD0]
        ring
