-- Prove2me | solution 1 for WhittEfficiency.MMs.proposition_3_1
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-22T01:32:53.939773+00:00
-- url     : https://prove2.me/submissions/17c8f91c-066e-4976-b68e-9823d8841854

import Mathlib
import Definitions.Def_QueueingFundamentals_BirthDeath_Balance
import Definitions.Def_WhittEfficiency_MMs_WaitLaw

open MeasureTheory ProbabilityTheory


namespace WhittEfficiency.MMs

lemma h15_cut (s : ℕ) (hs : 1 ≤ s) (lam : ℝ) (p : ℕ → ℝ)
    (hp : QueueingFundamentals.BirthDeath.IsBalanced
      (fun _ => lam) (QueueingFundamentals.BirthDeath.mmcDeath 1 s) p) :
    ∀ n : ℕ, lam * p n = QueueingFundamentals.BirthDeath.mmcDeath 1 s (n + 1) * p (n + 1) := by
  intro n
  induction n with
  | zero =>
    have h := hp.2
    have hm : QueueingFundamentals.BirthDeath.mmcDeath 1 s 1 = 1 := by
      simp only [QueueingFundamentals.BirthDeath.mmcDeath, mul_one]
      have : min 1 s = 1 := min_eq_left hs
      rw [this]; simp
    simpa [hm] using h
  | succ n ih =>
    have h := hp.1 (n + 1) (by omega)
    simp only [Nat.add_sub_cancel] at h
    linarith

lemma h15_tail (s : ℕ) (hs : 1 ≤ s) (lam : ℝ) (p : ℕ → ℝ)
    (hp : QueueingFundamentals.BirthDeath.IsBalanced
      (fun _ => lam) (QueueingFundamentals.BirthDeath.mmcDeath 1 s) p) :
    ∀ j : ℕ, p (s + j) = p s * (lam / s) ^ j := by
  intro j
  induction j with
  | zero => simp
  | succ j ih =>
    have h := h15_cut s hs lam p hp (s + j)
    have hm : QueueingFundamentals.BirthDeath.mmcDeath 1 s (s + j + 1) = s := by
      simp only [QueueingFundamentals.BirthDeath.mmcDeath, mul_one]
      have : min (s + j + 1) s = s := min_eq_right (by omega)
      rw [this]
    rw [hm] at h
    have hs0 : (s : ℝ) ≠ 0 := by positivity
    rw [← add_assoc, pow_succ, ← mul_assoc, ← ih]
    field_simp
    linarith

lemma h15_pos (s : ℕ) (hs : 1 ≤ s) (lam : ℝ) (hlam : 0 < lam) (p : ℕ → ℝ)
    (hp : QueueingFundamentals.BirthDeath.IsSteadyState
      (fun _ => lam) (QueueingFundamentals.BirthDeath.mmcDeath 1 s) p) :
    0 < p s := by
  obtain ⟨hnn, hsum, hbal⟩ := hp
  have hcut := h15_cut s hs lam p hbal
  have hmpos : ∀ n : ℕ, 0 < QueueingFundamentals.BirthDeath.mmcDeath 1 s (n + 1) := by
    intro n
    simp only [QueueingFundamentals.BirthDeath.mmcDeath, mul_one]
    have : 0 < min (n + 1) s := lt_min (by omega) (by omega)
    exact_mod_cast this
  have h0 : 0 < p 0 := by
    rcases (hnn 0).lt_or_eq with h | h
    · exact h
    · exfalso
      have hall : ∀ n, p n = 0 := by
        intro n
        induction n with
        | zero => exact h.symm
        | succ n ih =>
          have := hcut n
          rw [ih] at this
          have := hmpos n
          have h2 := hcut n
          rw [ih, mul_zero] at h2
          rcases mul_eq_zero.mp h2.symm with h3 | h3
          · linarith
          · exact h3
      have : HasSum p 0 := by
        have : p = fun _ => 0 := funext hall
        rw [this]; exact hasSum_zero
      have := hsum.unique this
      norm_num at this
  have hall : ∀ n, 0 < p n := by
    intro n
    induction n with
    | zero => exact h0
    | succ n ih =>
      have h2 := hcut n
      have hm := hmpos n
      have : 0 < lam * p n := mul_pos hlam ih
      rw [h2] at this
      exact pos_of_mul_pos_right this hm.le
  exact hall s


lemma h15_density (s : ℕ) (hs : 1 ≤ s) (lam : ℝ) (hlam : 0 < lam) (hρ : lam < s)
    (p : ℕ → ℝ) (hp0 : 0 < p s)
    (htail : ∀ j : ℕ, p (s + j) = p s * (lam / s) ^ j) (x : ℝ) (hx : 0 < x) :
    ∑' j : ℕ, ENNReal.ofReal (p (s + j)) * gammaPDF ((j : ℝ) + 1) s x =
      ENNReal.ofReal (p s * s / (s - lam)) * exponentialPDF ((s : ℝ) - lam) x := by
  have hs0 : (0 : ℝ) < s := by exact_mod_cast hs
  set f : ℕ → ℝ := fun j => p s * s * Real.exp (-(s * x)) * ((lam * x) ^ j / (j.factorial : ℝ)) with hf
  have hterm : ∀ j : ℕ, ENNReal.ofReal (p (s + j)) * gammaPDF ((j : ℝ) + 1) s x
      = ENNReal.ofReal (f j) := by
    intro j
    rw [gammaPDF_of_nonneg hx.le, ← ENNReal.ofReal_mul (by rw [htail]; positivity)]
    congr 1
    rw [htail, Real.Gamma_nat_eq_factorial, add_sub_cancel_right, Real.rpow_natCast,
      Real.rpow_add_one hs0.ne', Real.rpow_natCast, hf]
    simp only
    field_simp
    rw [← mul_pow, ← mul_pow, div_mul_cancel₀ _ hs0.ne']
  have hnn : ∀ j, 0 ≤ f j := fun j => by simp only [hf]; positivity
  have hsum : HasSum f (p s * s * Real.exp (-(s * x)) * Real.exp (lam * x)) :=
    by
    have h := (NormedSpace.expSeries_div_hasSum_exp (lam * x)).mul_left
      (p s * s * Real.exp (-(s * x)))
    rw [← Real.exp_eq_exp_ℝ] at h
    exact h
  simp_rw [hterm]
  rw [← ENNReal.ofReal_tsum_of_nonneg hnn hsum.summable, hsum.tsum_eq,
    exponentialPDF_eq, if_pos hx.le, ← ENNReal.ofReal_mul (by
      have : 0 < (s:ℝ) - lam := by linarith
      positivity)]
  congr 1
  have : 0 < (s:ℝ) - lam := by linarith
  rw [mul_assoc (p s * s) (Real.exp _), ← Real.exp_add]
  have e : -(s * x) + lam * x = -((s - lam) * x) := by ring
  rw [e]
  field_simp


lemma h15_restrict (s : ℕ) (hs : 1 ≤ s) (lam : ℝ) (hlam : 0 < lam) (hρ : lam < s)
    (p : ℕ → ℝ) (hp0 : 0 < p s)
    (htail : ∀ j : ℕ, p (s + j) = p s * (lam / s) ^ j) :
    (waitLaw s p).restrict (Set.Ioi (0 : ℝ)) =
      ENNReal.ofReal (p s * s / (s - lam)) • expMeasure ((s : ℝ) - lam) := by
  have hr : 0 < (s : ℝ) - lam := by linarith
  ext A hA
  have hB : MeasurableSet (A ∩ Set.Ioi (0 : ℝ)) := hA.inter measurableSet_Ioi
  have hconull : expMeasure ((s : ℝ) - lam) (Set.Ioi (0 : ℝ))ᶜ = 0 := by
    rw [Set.compl_Ioi]
    have := lintegral_exponentialPDF_eq_antiDeriv hr 0
    simp only [le_refl, if_true, mul_zero, neg_zero, Real.exp_zero, sub_self,
      ENNReal.ofReal_zero] at this
    simpa [expMeasure, gammaMeasure, withDensity_apply _ measurableSet_Iic, exponentialPDF,
      exponentialPDFReal, gammaPDF] using this
  rw [Measure.restrict_apply hA, Measure.smul_apply, smul_eq_mul,
    ← measure_inter_conull hconull (s := A)]
  unfold waitLaw
  rw [Measure.add_apply, Measure.smul_apply, Measure.dirac_apply' _ hB, Measure.sum_apply _ hB]
  have h0 : Set.indicator (A ∩ Set.Ioi (0 : ℝ)) (1 : ℝ → ENNReal) (0 : ℝ) = 0 := by simp
  rw [h0, smul_zero, zero_add]
  simp only [Measure.smul_apply, smul_eq_mul, gammaMeasure, withDensity_apply _ hB]
  conv_rhs => rw [expMeasure, gammaMeasure, withDensity_apply _ hB]
  simp_rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  rw [← lintegral_tsum]
  · refine setLIntegral_congr_fun hB ?_
    intro x hx
    have := h15_density s hs lam hlam hρ p hp0 htail x hx.2
    exact this
  · intro j
    exact (measurable_gammaPDFReal _ _).ennreal_ofReal.const_mul _ |>.aemeasurable


lemma h15_main (s : ℕ) (hs : 1 ≤ s) (lam : ℝ) (hlam : 0 < lam) (hρ : lam < s)
    (p : ℕ → ℝ)
    (hp : QueueingFundamentals.BirthDeath.IsSteadyState
      (fun _ => lam) (QueueingFundamentals.BirthDeath.mmcDeath 1 s) p) :
    0 < (waitLaw s p).real (Set.Ioi (0 : ℝ)) ∧
      (waitLaw s p).restrict (Set.Ioi (0 : ℝ)) =
        (waitLaw s p) (Set.Ioi (0 : ℝ)) •
          expMeasure ((s : ℝ) * (1 - lam / (s : ℝ))) := by
  have hs0 : (0 : ℝ) < s := by exact_mod_cast hs
  have hr : 0 < (s : ℝ) - lam := by linarith
  have hp0 := h15_pos s hs lam hlam p hp
  have htail := h15_tail s hs lam p hp.2.2
  have hres := h15_restrict s hs lam hlam hρ p hp0 htail
  have hrate : (s : ℝ) * (1 - lam / (s : ℝ)) = (s : ℝ) - lam := by field_simp
  have hprob : IsProbabilityMeasure (expMeasure ((s : ℝ) - lam)) := isProbabilityMeasure_expMeasure hr
  have hmass : (waitLaw s p) (Set.Ioi (0 : ℝ)) = ENNReal.ofReal (p s * s / (s - lam)) := by
    have := congrArg (fun m => m Set.univ) hres
    simp only [Measure.restrict_apply MeasurableSet.univ, Set.univ_inter, Measure.smul_apply,
      smul_eq_mul, measure_univ, mul_one] at this
    exact this
  refine ⟨?_, ?_⟩
  · rw [measureReal_def, hmass, ENNReal.toReal_ofReal (by positivity)]
    positivity
  · rw [hrate, hmass]; exact hres

lemma h15_exp_mean (r : ℝ) (hr : 0 < r) : ∫ w, w ∂(expMeasure r) = 1 / r := by
  have hf : Measurable (exponentialPDF r) := (measurable_exponentialPDFReal r).ennreal_ofReal
  have h1 : ∫ w, w ∂(expMeasure r) = ∫ x, (exponentialPDF r x).toReal • x := by
    unfold expMeasure gammaMeasure
    exact integral_withDensity_eq_integral_toReal_smul (f := gammaPDF 1 r) hf
      (Filter.Eventually.of_forall fun x => ENNReal.ofReal_lt_top) _
  rw [h1]
  have h2 : (fun x : ℝ => (exponentialPDF r x).toReal • x) =
      Set.indicator (Set.Ici 0) (fun x => r * (x * Real.exp (-(r * x)))) := by
    funext x
    simp only [exponentialPDF, exponentialPDFReal, gammaPDFReal, smul_eq_mul]
    by_cases hx : 0 ≤ x
    · simp [hx, Real.exp_nonneg, hr.le]
      ring
    · simp [hx]
  rw [h2, integral_indicator measurableSet_Ici, integral_Ici_eq_integral_Ioi, integral_const_mul]
  have := Real.integral_rpow_mul_exp_neg_mul_Ioi (a := 2) (r := r) (by norm_num) hr
  have e : (2 : ℝ) - 1 = 1 := by norm_num
  rw [e] at this
  simp only [Real.rpow_one] at this
  rw [this]
  have : Real.Gamma 2 = 1 := by
    have := Real.Gamma_nat_eq_factorial 1
    simpa using this
  rw [this]
  norm_num
  field_simp


lemma h15_prop_core (s : ℕ) (hs : 1 ≤ s) (lam : ℝ) (hlam : 0 < lam) (hρ : lam < s)
    (p : ℕ → ℝ)
    (hp : QueueingFundamentals.BirthDeath.IsSteadyState
      (fun _ => lam) (QueueingFundamentals.BirthDeath.mmcDeath 1 s) p)
    (γ : ℝ) (h1 : (1 - lam / (s : ℝ)) * Real.sqrt s = γ) :
    0 < (waitLaw s p).real (Set.Ioi (0 : ℝ)) ∧
      (∀ x : ℝ, 0 ≤ x →
        (waitLaw s p).real (Set.Ioi x) /
          (waitLaw s p).real (Set.Ioi (0 : ℝ)) =
            Real.exp (-(γ * Real.sqrt s * x))) ∧
      (∫ w in Set.Ioi (0 : ℝ), w ∂(waitLaw s p)) /
        (waitLaw s p).real (Set.Ioi (0 : ℝ)) = 1 / (γ * Real.sqrt s) := by
  obtain ⟨hpos, hres⟩ := h15_main s hs lam hlam hρ p hp
  have hs0 : (0 : ℝ) < s := by exact_mod_cast hs
  have hr : 0 < (s : ℝ) * (1 - lam / (s : ℝ)) := by
    have : (s : ℝ) * (1 - lam / (s : ℝ)) = s - lam := by field_simp
    rw [this]; linarith
  have hγ : γ * Real.sqrt s = (s : ℝ) * (1 - lam / (s : ℝ)) := by
    rw [← h1, mul_assoc, Real.mul_self_sqrt hs0.le]; ring
  have hprob := isProbabilityMeasure_expMeasure hr
  set c := (waitLaw s p) (Set.Ioi (0 : ℝ)) with hc
  have hcreal : (waitLaw s p).real (Set.Ioi (0 : ℝ)) = c.toReal := rfl
  refine ⟨hpos, ?_, ?_⟩
  · intro x hx
    have hsub : Set.Ioi x ⊆ Set.Ioi (0 : ℝ) := Set.Ioi_subset_Ioi hx
    have h2 : (waitLaw s p) (Set.Ioi x) = c * expMeasure ((s : ℝ) * (1 - lam / (s : ℝ))) (Set.Ioi x) := by
      have := congrArg (fun m => m (Set.Ioi x)) hres
      simp only [Measure.restrict_apply measurableSet_Ioi, Measure.smul_apply, smul_eq_mul,
        Set.inter_eq_left.mpr hsub] at this
      exact this
    have h3 : (expMeasure ((s : ℝ) * (1 - lam / (s : ℝ)))).real (Set.Ioi x) =
        Real.exp (-((s : ℝ) * (1 - lam / (s : ℝ)) * x)) := by
      have h4 := cdf_expMeasure_eq hr x
      rw [if_pos hx, ProbabilityTheory.cdf_eq_real] at h4
      rw [← Set.compl_Iic, probReal_compl_eq_one_sub measurableSet_Iic, h4]
      ring
    have h5 : (waitLaw s p).real (Set.Ioi x) = c.toReal *
        Real.exp (-((s : ℝ) * (1 - lam / (s : ℝ)) * x)) := by
      rw [← h3, measureReal_def, h2, ENNReal.toReal_mul]; rfl
    rw [h5, hcreal, hγ]
    have : c.toReal ≠ 0 := by rw [← hcreal]; exact hpos.ne'
    field_simp
  · have hint : ∫ w in Set.Ioi (0 : ℝ), w ∂(waitLaw s p) = c.toReal * (1 / ((s : ℝ) * (1 - lam / (s : ℝ)))) := by
      rw [hres, integral_smul_measure, h15_exp_mean _ hr, smul_eq_mul]
    rw [hint, hcreal, hγ]
    have : c.toReal ≠ 0 := by rw [← hcreal]; exact hpos.ne'
    field_simp

end WhittEfficiency.MMs

open WhittEfficiency.MMs


theorem solution
    (s : ℕ) (hs : 1 ≤ s) (lam : ℝ) (hlam : 0 < lam) (hρ : lam < s)
    (p : ℕ → ℝ)
    (hp : QueueingFundamentals.BirthDeath.IsSteadyState
      (fun _ => lam) (QueueingFundamentals.BirthDeath.mmcDeath 1 s) p)
    (γ : ℝ) (h1 : (1 - lam / (s : ℝ)) * Real.sqrt s = γ) :
    0 < (waitLaw s p).real (Set.Ioi (0 : ℝ)) ∧
      (∀ x : ℝ, 0 ≤ x →
        (waitLaw s p).real (Set.Ioi x) /
          (waitLaw s p).real (Set.Ioi (0 : ℝ)) =
            Real.exp (-(γ * Real.sqrt s * x))) ∧
      (∫ w in Set.Ioi (0 : ℝ), w ∂(waitLaw s p)) /
        (waitLaw s p).real (Set.Ioi (0 : ℝ)) = 1 / (γ * Real.sqrt s) := by
  exact h15_prop_core s hs lam hlam hρ p hp γ h1
