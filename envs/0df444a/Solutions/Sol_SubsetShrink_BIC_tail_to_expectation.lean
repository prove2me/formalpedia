-- Prove2me | solution 1 for SubsetShrink.BIC.tail_to_expectation
-- status  : ACCEPTED   (prove)
-- author  : @mihalyimark
-- created : 2026-10-18T20:12:53.572569+00:00
-- url     : https://prove2.me/submissions/a7ddce89-1a1a-410a-9843-8ce8314dee6d

import Mathlib

open MeasureTheory ProbabilityTheory

theorem solution {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (W : Ω → ℝ) (hW : Measurable W) (κ : ℝ) (hκ : 0 < κ)
    (h : ∀ δ0 : ℝ, 0 < δ0 → δ0 < 1 →
      1 - δ0 / 2 ≤ (μ {ω | W ω ≤ κ * Real.log (1 / δ0)}).toReal) :
    (∀ w : ℝ, 0 ≤ w → 2 * (μ {ω | w < W ω}).toReal ≤ Real.exp (-w / κ)) ∧
    ∫⁻ ω, ENNReal.ofReal (W ω) ∂μ ≤ ENNReal.ofReal (κ / 2) := by
  -- Core estimate: from the hypothesis at level `δ0` we get a tail bound at level `w`
  -- whenever `κ * log (1 / δ0) = w`.
  have key : ∀ (w δ0 : ℝ), 0 < δ0 → δ0 < 1 →
      κ * Real.log (1 / δ0) = w →
      2 * (μ {ω | w < W ω}).toReal ≤ δ0 := by
    intro w δ0 h0 h1 hkey
    have hδ := h δ0 h0 h1
    rw [hkey] at hδ
    -- hδ : 1 - δ0 / 2 ≤ (μ {ω | W ω ≤ w}).toReal
    have hs : MeasurableSet {ω | W ω ≤ w} := measurableSet_le hW measurable_const
    have ht_eq : {ω | w < W ω} = {ω | W ω ≤ w}ᶜ := by
      ext ω; simp [not_le]
    have hsum : (μ {ω | W ω ≤ w}).toReal + (μ {ω | w < W ω}).toReal = 1 := by
      have hcompl : μ {ω | W ω ≤ w} + μ {ω | w < W ω} = 1 := by
        have hc := measure_add_measure_compl (μ := μ) hs
        rw [measure_univ, ← ht_eq] at hc
        exact hc
      calc (μ {ω | W ω ≤ w}).toReal + (μ {ω | w < W ω}).toReal
          = (μ {ω | W ω ≤ w} + μ {ω | w < W ω}).toReal :=
            (ENNReal.toReal_add (measure_ne_top μ _) (measure_ne_top μ _)).symm
        _ = (1 : ENNReal).toReal := by rw [hcompl]
        _ = 1 := ENNReal.toReal_one
    linarith
  have partA : ∀ w : ℝ, 0 ≤ w → 2 * (μ {ω | w < W ω}).toReal ≤ Real.exp (-w / κ) := by
    intro w hw
    rcases eq_or_lt_of_le hw with hzero | hpos
    · -- w = 0 : approximate `{0 < W}` from below by the countable family `{1/(n+1) < W}`
      rw [← hzero]
      set s : ℕ → Set Ω := fun n => {ω | (1 : ℝ) / ((n : ℝ) + 1) < W ω} with hs_def
      have hUnion : (⋃ n, s n) = {ω | 0 < W ω} := by
        ext ω
        constructor
        · intro hω
          rcases Set.mem_iUnion.mp hω with ⟨n, hn⟩
          simp only [s, Set.mem_ofPred_eq] at hn ⊢
          exact lt_trans (by positivity) hn
        · intro hω
          simp only [Set.mem_ofPred_eq] at hω
          obtain ⟨n, hn⟩ := exists_nat_one_div_lt hω
          exact Set.mem_iUnion.mpr ⟨n, by simpa [s] using hn⟩
      have hmono : Monotone s := by
        intro m n hmn ω hω
        simp only [s, Set.mem_ofPred_eq] at hω ⊢
        have hle : (1 : ℝ) / ((n : ℝ) + 1) ≤ 1 / ((m : ℝ) + 1) := by
          apply one_div_le_one_div_of_le
          · positivity
          · have : (m : ℝ) ≤ (n : ℝ) := by exact_mod_cast hmn
            linarith
        exact lt_of_le_of_lt hle hω
      have hbound : (⨆ n, μ (s n)) ≤ ENNReal.ofReal (1 / 2) := by
        apply iSup_le
        intro n
        have hwn : 0 < (1 : ℝ) / ((n : ℝ) + 1) := by positivity
        have hlt : -(1 / ((n : ℝ) + 1) / κ) < 0 := by
          have := div_pos hwn hκ; linarith
        have hδ0 : 0 < Real.exp (-(1 / ((n : ℝ) + 1) / κ)) := Real.exp_pos _
        have hδ1 : Real.exp (-(1 / ((n : ℝ) + 1) / κ)) < 1 := Real.exp_lt_one_iff.mpr hlt
        have hkey : κ * Real.log (1 / Real.exp (-(1 / ((n : ℝ) + 1) / κ)))
            = 1 / ((n : ℝ) + 1) := by
          have hinv : (Real.exp (-(1 / ((n : ℝ) + 1) / κ)))⁻¹
              = Real.exp ((1 / ((n : ℝ) + 1)) / κ) := by
            rw [← Real.exp_neg]; congr 1; ring
          rw [one_div, hinv, Real.log_exp]
          field_simp
        have hk := key (1 / ((n : ℝ) + 1)) (Real.exp (-(1 / ((n : ℝ) + 1) / κ)))
          hδ0 hδ1 hkey
        have hreal : (μ (s n)).toReal ≤ 1 / 2 := by
          have h2 : Real.exp (-(1 / ((n : ℝ) + 1) / κ)) ≤ 1 :=
            Real.exp_le_one_iff.mpr (le_of_lt hlt)
          linarith
        calc μ (s n) = ENNReal.ofReal ((μ (s n)).toReal) :=
              (ENNReal.ofReal_toReal (measure_ne_top μ _)).symm
          _ ≤ ENNReal.ofReal (1 / 2) := ENNReal.ofReal_le_ofReal hreal
      rw [← hUnion, hmono.measure_iUnion]
      have hfin' : (⨆ n, μ (s n)) ≠ ⊤ := ne_top_of_le_ne_top (by simp) hbound
      have hto : (⨆ n, μ (s n)).toReal ≤ 1 / 2 := by
        have := (ENNReal.toReal_le_toReal hfin' (by simp)).mpr hbound
        simpa using this
      have : 2 * (⨆ n, μ (s n)).toReal ≤ 1 := by linarith
      simpa using this
    · -- w > 0 : use the hypothesis at δ0 = exp (-(w/κ))
      have hδ0 : 0 < Real.exp (-(w / κ)) := Real.exp_pos _
      have hlt : -(w / κ) < 0 := by have := div_pos hpos hκ; linarith
      have hδ1 : Real.exp (-(w / κ)) < 1 := Real.exp_lt_one_iff.mpr hlt
      have hkey : κ * Real.log (1 / Real.exp (-(w / κ))) = w := by
        have hinv : (Real.exp (-(w / κ)))⁻¹ = Real.exp (w / κ) := by
          rw [← Real.exp_neg]; congr 1; ring
        rw [one_div, hinv, Real.log_exp]
        field_simp
      have hδ := key w (Real.exp (-(w / κ))) hδ0 hδ1 hkey
      simpa only [neg_div] using hδ
  refine ⟨partA, ?_⟩
  -- Layer-cake representation of the lower integral.
  have hmax : Measurable (fun ω => max (W ω) 0) := hW.max measurable_const
  have hcongr : ∫⁻ ω, ENNReal.ofReal (W ω) ∂μ
      = ∫⁻ ω, ENNReal.ofReal (max (W ω) 0) ∂μ := by
    apply lintegral_congr
    intro ω
    rcases le_total 0 (W ω) with hh | hh
    · simp only [max_eq_left hh]
    · simp only [max_eq_right hh, ENNReal.ofReal_of_nonpos hh, ENNReal.ofReal_zero]
  rw [hcongr]
  rw [MeasureTheory.lintegral_eq_lintegral_meas_lt μ
    (ae_of_all μ (fun ω => le_max_right (W ω) 0)) hmax.aemeasurable]
  -- On `Ioi 0` the integrand `max (W a) 0` may be replaced by `W a`.
  have hcongr2 : ∫⁻ t in Set.Ioi (0 : ℝ), μ {a | t < max (W a) 0}
      = ∫⁻ t in Set.Ioi (0 : ℝ), μ {a | t < W a} := by
    apply setLIntegral_congr_fun measurableSet_Ioi
    intro t ht
    have ht0 : 0 < t := ht
    have hset : {a | t < max (W a) 0} = {a | t < W a} := by
      ext a
      simp only [Set.mem_ofPred_eq, lt_max_iff]
      constructor
      · rintro (hh | hh)
        · exact hh
        · exact absurd hh (not_lt.mpr (le_of_lt ht0))
      · exact Or.inl
    exact congrArg μ hset
  rw [hcongr2]
  -- Reduce to integrating the explicit exponential bound.
  have hb : ∫⁻ t in Set.Ioi (0 : ℝ), μ {a | t < W a}
      ≤ ∫⁻ t in Set.Ioi (0 : ℝ), ENNReal.ofReal (Real.exp (-t / κ) / 2) := by
    apply setLIntegral_mono' measurableSet_Ioi
    intro t ht
    have ht0 : 0 ≤ t := le_of_lt ht
    have h1 := partA t ht0
    have h2 : (μ {a | t < W a}).toReal ≤ Real.exp (-t / κ) / 2 := by linarith
    calc μ {a | t < W a} = ENNReal.ofReal ((μ {a | t < W a}).toReal) :=
          (ENNReal.ofReal_toReal (measure_ne_top μ _)).symm
      _ ≤ ENNReal.ofReal (Real.exp (-t / κ) / 2) := ENNReal.ofReal_le_ofReal h2
  -- Integrability and the value of the real integral.
  have hfin : Integrable (fun t : ℝ => Real.exp (-t / κ) / 2)
      (volume.restrict (Set.Ioi (0 : ℝ))) := by
    have ha : (-(1 / κ) : ℝ) < 0 := by have := one_div_pos.mpr hκ; linarith
    have h1 : Integrable (fun t : ℝ => Real.exp ((-(1 / κ)) * t))
        (volume.restrict (Set.Ioi (0 : ℝ))) := integrableOn_exp_mul_Ioi ha 0
    refine (h1.div_const 2).congr ?_
    filter_upwards with t
    rw [show (-(1 / κ)) * t = -t / κ by ring]
  have hnn : 0 ≤ᵐ[volume.restrict (Set.Ioi (0 : ℝ))]
      (fun t : ℝ => Real.exp (-t / κ) / 2) :=
    ae_of_all _ (fun t => by positivity)
  have hval : ∫ t in Set.Ioi (0 : ℝ), Real.exp (-t / κ) ∂volume = κ := by
    have h1 : (fun t : ℝ => Real.exp (-t / κ)) = (fun t : ℝ => Real.exp ((-(1 / κ)) * t)) := by
      funext t; rw [show (-(1 / κ)) * t = -t / κ by ring]
    rw [h1, integral_exp_mul_Ioi (show (-(1 / κ) : ℝ) < 0 by
      have := one_div_pos.mpr hκ; linarith) 0]
    rw [mul_zero, Real.exp_zero, neg_div_neg_eq, one_div_one_div]
  calc ∫⁻ t in Set.Ioi (0 : ℝ), μ {a | t < W a}
      ≤ ∫⁻ t in Set.Ioi (0 : ℝ), ENNReal.ofReal (Real.exp (-t / κ) / 2) := hb
    _ = ENNReal.ofReal (∫ t in Set.Ioi (0 : ℝ), Real.exp (-t / κ) / 2) :=
        (MeasureTheory.ofReal_integral_eq_lintegral_ofReal (μ := volume.restrict (Set.Ioi (0 : ℝ)))
          hfin hnn).symm
    _ = ENNReal.ofReal (κ / 2) := by
        congr 1
        rw [integral_div, hval]
