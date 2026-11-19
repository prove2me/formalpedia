-- Prove2me | solution 1 for RGGDetect.lemma_1
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-18T06:09:58.328729+00:00
-- url     : https://prove2.me/submissions/b12650ec-e483-4c23-85a5-5ea930b77e79

import Mathlib

open MeasureTheory InformationTheory

theorem solution {Ω : Type*} [Fintype Ω] [Nonempty Ω] [MeasurableSpace Ω]
    [MeasurableSingletonClass Ω] (P Q : Measure Ω) [IsProbabilityMeasure P]
    [IsProbabilityMeasure Q] (hPQ : P ≪ Q) (qstar : ℝ) (hq : 0 < qstar)
    (hqmin : ∀ ω, 0 < Q.real {ω} → qstar ≤ Q.real {ω}) (T : Finset Ω) :
    InformationTheory.klDiv P Q ≤ ENNReal.ofReal
      (∑ ω ∈ T, (P.real {ω} / Q.real {ω} - 1) ^ 2 * Q.real {ω} +
        P.real (↑T : Set Ω)ᶜ * Real.log (1 / qstar) + Q.real (↑T : Set Ω)ᶜ) := by
  classical
  set p : Ω → ℝ := fun ω => P.real {ω} with hp
  set q : Ω → ℝ := fun ω => Q.real {ω} with hq'
  -- density at atoms
  have hden : ∀ ω, 0 < q ω → (P.rnDeriv Q ω).toReal = p ω / q ω := by
    intro ω hqω
    have h := Measure.setLIntegral_rnDeriv hPQ ({ω} : Set Ω)
    rw [lintegral_singleton] at h
    have hQ : Q {ω} ≠ 0 := by
      intro h0; simp [hq', measureReal_def, h0] at hqω
    have hQt : Q {ω} ≠ ⊤ := measure_ne_top _ _
    have : (P.rnDeriv Q ω) = P {ω} / Q {ω} := by
      rw [← h, ENNReal.mul_div_cancel_right hQ hQt]
    rw [this, ENNReal.toReal_div]; rfl
  have hzero : ∀ ω, q ω = 0 → p ω = 0 := by
    intro ω h0
    have : Q {ω} = 0 := by
      have := (ENNReal.toReal_eq_zero_iff _).mp h0
      rcases this with h | h
      · exact h
      · exact absurd h (measure_ne_top _ _)
    simp [hp, measureReal_def, hPQ this]
  -- KL as a finite sum
  have hkl : klDiv P Q = ENNReal.ofReal (∑ ω, klFun (P.rnDeriv Q ω).toReal * q ω) := by
    rw [klDiv_eq_lintegral_klFun_of_ac hPQ, lintegral_fintype,
      ENNReal.ofReal_sum_of_nonneg (fun ω _ => mul_nonneg (klFun_nonneg ENNReal.toReal_nonneg)
        measureReal_nonneg)]
    apply Finset.sum_congr rfl
    intro ω _
    rw [ENNReal.ofReal_mul (klFun_nonneg ENNReal.toReal_nonneg), measureReal_def,
      ENNReal.ofReal_toReal (measure_ne_top _ _)]
  rw [hkl]
  apply ENNReal.ofReal_le_ofReal
  -- termwise bound
  set g : Ω → ℝ := fun ω => if ω ∈ T then (p ω / q ω - 1) ^ 2 * q ω
    else p ω * Real.log (1 / qstar) + q ω with hg
  have hterm : ∀ ω, klFun (P.rnDeriv Q ω).toReal * q ω ≤ g ω := by
    intro ω
    have hq0 : 0 ≤ q ω := measureReal_nonneg
    rcases hq0.eq_or_lt with h0 | hpos
    · rw [← h0, mul_zero]
      simp only [hg]
      split_ifs
      · rw [← h0]; simp
      · rw [hzero ω h0.symm, ← h0]; simp
    · rw [hden ω hpos, klFun_apply]
      set L := p ω / q ω with hL
      have hp0 : 0 ≤ p ω := measureReal_nonneg
      have hL0 : 0 ≤ L := div_nonneg hp0 hpos.le
      simp only [hg]
      split_ifs with hT
      · -- L log L ≤ L (L - 1)
        have : L * Real.log L ≤ L * (L - 1) := by
          rcases hL0.eq_or_lt with hz | hz
          · rw [← hz]; simp
          · exact mul_le_mul_of_nonneg_left (by linarith [Real.log_le_sub_one_of_pos hz]) hL0
        have : L * Real.log L + 1 - L ≤ (L - 1) ^ 2 := by nlinarith
        exact mul_le_mul_of_nonneg_right this hpos.le
      · -- p log(p/q) + q - p ≤ p log(1/q*) + q
        have hp1 : p ω ≤ 1 := by
          simp only [hp]; exact measureReal_le_one
        have hqs : qstar ≤ q ω := hqmin ω hpos
        have e : (L * Real.log L + 1 - L) * q ω = p ω * Real.log L + q ω - p ω := by
          rw [hL]; field_simp
        rw [e]
        rcases hp0.eq_or_lt with hz | hz
        · rw [← hz]; simp
        · have hlog : Real.log L ≤ Real.log (1 / qstar) := by
            apply Real.log_le_log (div_pos hz hpos)
            rw [div_le_div_iff₀ hpos hq]
            nlinarith
          nlinarith [mul_le_mul_of_nonneg_left hlog hp0]
  calc ∑ ω, klFun (P.rnDeriv Q ω).toReal * q ω ≤ ∑ ω, g ω := Finset.sum_le_sum (fun ω _ => hterm ω)
    _ = ∑ ω ∈ T, (p ω / q ω - 1) ^ 2 * q ω + ∑ ω ∈ Tᶜ, (p ω * Real.log (1 / qstar) + q ω) := by
        rw [← Finset.sum_add_sum_compl T]
        congr 1
        · apply Finset.sum_congr rfl; intro ω hω; simp [hg, hω]
        · apply Finset.sum_congr rfl; intro ω hω
          simp only [Finset.mem_compl] at hω; simp [hg, hω]
    _ = _ := by
        rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.coe_compl]
        simp only [hp, hq', sum_measureReal_singleton]
        ring
