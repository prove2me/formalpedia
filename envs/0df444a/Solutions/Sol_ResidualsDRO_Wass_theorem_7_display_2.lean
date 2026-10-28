-- Prove2me | solution 1 for ResidualsDRO.Wass.theorem_7_display_2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T17:29:06.347572+00:00
-- url     : https://prove2.me/submissions/aea22628-8013-48ff-81ce-27c2a821e51c

import Mathlib
import Definitions.Def_WassersteinDRO_Duality_wassersteinDistance
import Definitions.Def_ResidualsDRO_Wass_Setting
import Definitions.Def_ResidualsDRO_Wass_Radius
open MeasureTheory ProbabilityTheory

open ResidualsDRO.Wass in
theorem solution {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {dx dy n : ℕ} (hdy : 1 ≤ dy) (hn : 1 ≤ n)
    (p a : ℝ) (hp : 1 ≤ p) (hpdy : p ≠ (dy : ℝ) / 2)
    (Pε : Measure (EuclideanSpace ℝ (Fin dy))) [IsProbabilityMeasure Pε]
    (hA1 : Assumption1 Pε p a)
    (fstar : EuclideanSpace ℝ (Fin dx) → EuclideanSpace ℝ (Fin dy))
    (eps : Fin n → Ω → EuclideanSpace ℝ (Fin dy)) (heps_meas : ∀ i, Measurable (eps i))
    (heps_indep : iIndepFun eps P) (heps_law : ∀ i, P.map (eps i) = Pε)
    (x : EuclideanSpace ℝ (Fin dx))
    (c₁ c₂ : ℝ) (hc₁ : 0 < c₁) (hc₂ : 0 < c₂) (hL2 : Lemma2Bound P Pε fstar eps x dy p a c₁ c₂)
    (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1) :
    P {ω | ENNReal.ofReal (kappa2 c₁ c₂ a p dy n α) <
        WassersteinDRO.Duality.wassersteinDistance p (trueEmpirical fstar (fun i => eps i ω) x)
          (condLaw Pε fstar x)} ≤
      ENNReal.ofReal (α / 2) := by
  set W : Ω → ENNReal := fun ω => WassersteinDRO.Duality.wassersteinDistance p
    (trueEmpirical fstar (fun i => eps i ω) x) (condLaw Pε fstar x) with hW
  have hp0 : 0 < p := by linarith
  have ha0 : 0 < a := by linarith [hA1.1]
  have hnr : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hdyr : (1 : ℝ) ≤ dy := by exact_mod_cast hdy
  set L := Real.log (2 * c₁ * α⁻¹) with hLdef
  have hk2 : kappa2 c₁ c₂ a p dy n α = if L / c₂ ≤ (n : ℝ) then
      (L / (c₂ * n)) ^ min (p / (dy : ℝ)) (1 / 2) else (L / (c₂ * n)) ^ (p / a) := rfl
  -- general bound: every level set has measure at most c₁
  have hgen : ∀ κ : ℝ, 0 < κ → P {ω | ENNReal.ofReal κ ≤ W ω} ≤ ENNReal.ofReal c₁ := by
    intro κ hκ
    refine le_trans (hL2 κ hκ) (ENNReal.ofReal_le_ofReal ?_)
    split_ifs
    · apply mul_le_of_le_one_right hc₁.le
      rw [Real.exp_le_one_iff]
      have : 0 ≤ κ ^ max ((dy : ℝ) / p) 2 := Real.rpow_nonneg hκ.le _
      have : 0 ≤ c₂ * n * κ ^ max ((dy : ℝ) / p) 2 := by positivity
      linarith
    · apply mul_le_of_le_one_right hc₁.le
      rw [Real.exp_le_one_iff]
      have : 0 ≤ κ ^ (a / p) := Real.rpow_nonneg hκ.le _
      have : 0 ≤ c₂ * n * κ ^ (a / p) := by positivity
      linarith
  -- value of the Lemma 2 bound at the chosen radius
  have hexp : c₁ * Real.exp (-c₂ * n * (L / (c₂ * n))) = α / 2 := by
    have e : -c₂ * n * (L / (c₂ * n)) = -L := by field_simp
    rw [e, Real.exp_neg, hLdef, Real.exp_log (by positivity)]
    field_simp
  by_cases hL : 0 < L
  · have hxx : 0 < L / (c₂ * n) := by positivity
    by_cases hbr : L / c₂ ≤ (n : ℝ)
    · set m := min (p / (dy : ℝ)) (1 / 2) with hm
      set M := max ((dy : ℝ) / p) 2 with hM
      have hmM : m * M = 1 := by
        rcases le_total (p / (dy : ℝ)) (1 / 2) with h | h
        · have h2 : 2 ≤ (dy : ℝ) / p := by
            rw [div_le_iff₀ (by positivity)] at h
            rw [le_div_iff₀ hp0]; linarith
          rw [hm, hM, min_eq_left h, max_eq_left h2]
          field_simp
        · have h2 : (dy : ℝ) / p ≤ 2 := by
            rw [le_div_iff₀ (by positivity)] at h
            rw [div_le_iff₀ hp0]; linarith
          rw [hm, hM, min_eq_right h, max_eq_right h2]
          norm_num
      have hm0 : 0 < m := lt_min (by positivity) (by norm_num)
      have hκ : 0 < (L / (c₂ * n)) ^ m := Real.rpow_pos_of_pos hxx m
      have hx1 : L / (c₂ * n) ≤ 1 := by
        rw [div_le_one (by positivity)]
        rw [div_le_iff₀ hc₂] at hbr; linarith
      have hκ1 : (L / (c₂ * n)) ^ m ≤ 1 := Real.rpow_le_one hxx.le hx1 hm0.le
      have hpow : ((L / (c₂ * n)) ^ m) ^ M = L / (c₂ * n) := by
        rw [← Real.rpow_mul hxx.le, hmM, Real.rpow_one]
      rw [hk2, if_pos hbr]
      calc P {ω | ENNReal.ofReal ((L / (c₂ * n)) ^ m) < W ω}
          ≤ P {ω | ENNReal.ofReal ((L / (c₂ * n)) ^ m) ≤ W ω} :=
            measure_mono (fun ω hω => by simp only [Set.mem_setOf_eq] at hω ⊢; exact le_of_lt hω)
        _ ≤ _ := hL2 _ hκ
        _ = ENNReal.ofReal (α / 2) := by rw [if_pos hκ1, hpow, hexp]
    · push_neg at hbr
      have hx1 : 1 < L / (c₂ * n) := by
        rw [one_lt_div (by positivity)]
        rw [lt_div_iff₀ hc₂] at hbr; linarith
      have hκ : 0 < (L / (c₂ * n)) ^ (p / a) := Real.rpow_pos_of_pos hxx _
      have hκ1 : 1 < (L / (c₂ * n)) ^ (p / a) := Real.one_lt_rpow hx1 (by positivity)
      have hpow : ((L / (c₂ * n)) ^ (p / a)) ^ (a / p) = L / (c₂ * n) := by
        rw [← Real.rpow_mul hxx.le]
        have : p / a * (a / p) = 1 := by field_simp
        rw [this, Real.rpow_one]
      rw [hk2, if_neg (not_le.mpr hbr)]
      calc P {ω | ENNReal.ofReal ((L / (c₂ * n)) ^ (p / a)) < W ω}
          ≤ P {ω | ENNReal.ofReal ((L / (c₂ * n)) ^ (p / a)) ≤ W ω} :=
            measure_mono (fun ω hω => by simp only [Set.mem_setOf_eq] at hω ⊢; exact le_of_lt hω)
        _ ≤ _ := hL2 _ hκ
        _ = ENNReal.ofReal (α / 2) := by rw [if_neg (not_le.mpr hκ1), hpow, hexp]
  · -- degenerate case: c₁ ≤ α / 2
    push_neg at hL
    have hc₁α : c₁ ≤ α / 2 := by
      have h1 : 2 * c₁ * α⁻¹ ≤ 1 := by
        by_contra hc
        push_neg at hc
        exact absurd (Real.log_pos hc) (not_lt.mpr hL)
      rw [mul_inv_le_iff₀ hα0] at h1
      linarith
    set s : ℕ → Set Ω := fun k => {ω | ENNReal.ofReal (1 / ((k : ℝ) + 1)) ≤ W ω} with hs
    have hmono : Monotone s := by
      intro k l hkl ω hω
      refine le_trans (ENNReal.ofReal_le_ofReal ?_) hω
      apply one_div_le_one_div_of_le (by positivity)
      have : (k : ℝ) ≤ l := by exact_mod_cast hkl
      linarith
    have hcover : {ω | ENNReal.ofReal (kappa2 c₁ c₂ a p dy n α) < W ω} ⊆ ⋃ k, s k := by
      intro ω hω
      have hpos : W ω ≠ 0 := ne_of_gt (lt_of_le_of_lt bot_le hω)
      obtain ⟨k, hk⟩ := ENNReal.exists_inv_nat_lt hpos
      refine Set.mem_iUnion.mpr ⟨k, le_trans ?_ hk.le⟩
      rw [ENNReal.ofReal_div_of_pos (by positivity), ENNReal.ofReal_one, one_div]
      apply ENNReal.inv_le_inv.mpr
      rw [ENNReal.ofReal_add (by positivity) zero_le_one, ENNReal.ofReal_natCast, ENNReal.ofReal_one]
      exact le_self_add
    calc P {ω | ENNReal.ofReal (kappa2 c₁ c₂ a p dy n α) < W ω}
        ≤ P (⋃ k, s k) := measure_mono hcover
      _ = ⨆ k, P (s k) := hmono.measure_iUnion
      _ ≤ ENNReal.ofReal c₁ := iSup_le (fun k => hgen _ (by positivity))
      _ ≤ ENNReal.ofReal (α / 2) := ENNReal.ofReal_le_ofReal hc₁α
