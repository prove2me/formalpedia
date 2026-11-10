-- Prove2me | solution 1 for PlatformCournot.appendix_A3_efficient_welfare
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-10T05:56:22.742205+00:00
-- url     : https://prove2.me/submissions/0dacce86-5734-4e2a-9ab5-85c51135f627

import Mathlib
import Definitions.Def_PlatformCournot_efficientWelfare
import Definitions.Def_PlatformCournot_linearCost

namespace Aux_PCA3

lemma integ (a b d : ℝ) : ∫ z in (0:ℝ)..d, (a - b * z) = a * d - b * d ^ 2 / 2 := by
  have hi : IntervalIntegrable (fun z : ℝ => b * z) MeasureTheory.volume 0 d :=
    (by fun_prop : Continuous (fun z : ℝ => b * z)).intervalIntegrable 0 d
  rw [intervalIntegral.integral_sub intervalIntegrable_const hi, intervalIntegral.integral_const,
    intervalIntegral.integral_const_mul, integral_id]
  simp only [smul_eq_mul, sub_zero]
  ring

lemma quad (a b d : ℝ) (hb : 0 < b) (hd : 0 ≤ d) :
    a * d - b * d ^ 2 / 2 ≤ (max a 0) ^ 2 / (2 * b) := by
  rcases le_or_gt 0 a with ha | ha
  · rw [max_eq_left ha, le_div_iff₀ (by positivity)]
    nlinarith [sq_nonneg (a - b * d)]
  · rw [max_eq_right ha.le]
    have : (0:ℝ) ^ 2 / (2 * b) = 0 := by simp
    rw [this]
    nlinarith [mul_nonneg hb.le (sq_nonneg d), mul_nonneg (neg_nonneg.mpr ha.le) hd]

end Aux_PCA3

open PlatformCournot in
theorem solution {n m : ℕ} (D : AffineDemand m) (hn : 1 ≤ n)
    (c : Fin n → ℝ) (hc : ∀ i, 0 ≤ c i) :
    efficientWelfare D (fun i => linearCost (c i)) Set.univ =
      ∑ j, (max (D.α j - ⨅ i, c i) 0) ^ 2 / (2 * D.β j) := by
  classical
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  obtain ⟨cm, hcm⟩ : ∃ cm, cm = ⨅ i, c i := ⟨_, rfl⟩
  rw [← hcm]
  obtain ⟨i0, hi0⟩ := exists_eq_ciInf_of_finite (f := c)
  rw [← hcm] at hi0
  have hle : ∀ i, cm ≤ c i := fun i => hcm ▸ ciInf_le (Finite.bddBelow_range c) i
  have hcm0 : 0 ≤ cm := hi0 ▸ hc i0
  unfold efficientWelfare
  apply IsGreatest.csSup_eq
  constructor
  · set x : Fin m → ℝ := fun j => max (D.α j - cm) 0 / D.β j with hx
    have hx0 : ∀ j, 0 ≤ x j := fun j => div_nonneg (le_max_right _ _) (D.β_pos j).le
    refine ⟨fun i j => if i = i0 then x j else 0, ?_, ?_⟩
    · intro i j
      refine ⟨?_, fun h => absurd (Set.mem_univ _) h⟩
      by_cases h : i = i0
      · simp only [h, if_true]; exact hx0 j
      · simp only [h, if_false]; exact le_refl 0
    · have hdem : ∀ j, demand (fun i j => if i = i0 then x j else 0) j = x j := by
        intro j; unfold demand; simp
      have hsup : ∀ i, supply (fun i j => if i = i0 then x j else 0) i
          = if i = i0 then ∑ j, x j else 0 := by
        intro i; unfold supply
        by_cases h : i = i0
        · simp [h]
        · simp [h]
      unfold socialWelfare
      simp only [hdem, hsup]
      rw [Finset.sum_eq_single i0 (fun b _ hb => by simp [hb, linearCost])
        (fun h => absurd (Finset.mem_univ _) h)]
      simp only [if_true, linearCost, hi0]
      rw [max_eq_left (mul_nonneg hcm0 (Finset.sum_nonneg (fun j _ => hx0 j))),
        Finset.mul_sum, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro j _
      simp only [AffineDemand.price]
      rw [Aux_PCA3.integ]
      have hb := D.β_pos j
      rcases le_or_gt 0 (D.α j - cm) with ha | ha
      · simp only [hx, max_eq_left ha]
        field_simp <;> ring
      · simp only [hx, max_eq_right ha.le]
        simp
  · rintro w ⟨q, hq, rfl⟩
    have hq0 : ∀ i j, 0 ≤ q i j := fun i j => (hq i j).1
    unfold socialWelfare
    have hcost : ∑ j, cm * demand q j ≤ ∑ i, linearCost (c i) (supply q i) := by
      calc ∑ j, cm * demand q j = ∑ i, cm * supply q i := by
            unfold demand supply
            simp only [← Finset.mul_sum]
            rw [Finset.sum_comm]
        _ ≤ ∑ i, linearCost (c i) (supply q i) := by
            apply Finset.sum_le_sum
            intro i _
            have hs : 0 ≤ supply q i := Finset.sum_nonneg (fun j _ => hq0 i j)
            unfold linearCost
            exact le_trans (mul_le_mul_of_nonneg_right (hle i) hs) (le_max_left _ _)
    have hmain : (∑ j, ∫ z in (0 : ℝ)..(demand q j), D.price j z) - ∑ j, cm * demand q j
        ≤ ∑ j, (max (D.α j - cm) 0) ^ 2 / (2 * D.β j) := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_le_sum
      intro j _
      simp only [AffineDemand.price]
      rw [Aux_PCA3.integ]
      have hd : 0 ≤ demand q j := Finset.sum_nonneg (fun i _ => hq0 i j)
      have := Aux_PCA3.quad (D.α j - cm) (D.β j) (demand q j) (D.β_pos j) hd
      linarith
    linarith
