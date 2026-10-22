-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Support21.P03.proposition_3_4
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T10:03:50.117786+00:00
-- url     : https://prove2.me/submissions/658069b8-7e0f-49e4-8491-e3e57d9b8d9e

import Definitions.Def_QAlgorithms_Papers_Independent_Support21_P03
noncomputable section

open MeasureTheory Filter Set

open scoped ENNReal Topology BigOperators

open QAlgorithms.Papers.Independent.Support21.P03

variable {K : TimeKind} {M : Type*} [MeasurableSpace M]

lemma g68c_prob (D : NonsingularSystem K M) (s : K.Carrier) : IsProbabilityMeasure (pushedReference D s) :=
  Measure.isProbabilityMeasure_map (D.flow s).measurable.aemeasurable

lemma g68c_inv (D : NonsingularSystem K M) (t : K.Carrier) (x : M) : D.flow (-t) (D.flow t x) = x := by
  rw [← D.flow_add, neg_add_cancel, D.flow_zero]

lemma g68c_inv' (D : NonsingularSystem K M) (t : K.Carrier) (x : M) : D.flow t (D.flow (-t) x) = x := by
  rw [← D.flow_add, add_neg_cancel, D.flow_zero]

lemma g68c_meas_ell (D : NonsingularSystem K M) (t : K.Carrier) : Measurable (logDensity D t) :=
  Real.measurable_log.comp (ENNReal.measurable_toReal.comp (Measure.measurable_rnDeriv _ _))

lemma g68c_meas_c (D : NonsingularSystem K M) (t : K.Carrier) : Measurable (entropyCocycle D t) :=
  (g68c_meas_ell D t).comp (D.flow t).measurable

/-- theta maps omega_{-s} to omega_s. -/
lemma g68c_map_theta (D : NonsingularSystem K M) (theta : M ≃ᵐ M)
    (hTRI : IsTimeReversal D theta) (s : K.Carrier) :
    (pushedReference D (-s)).map theta = pushedReference D s := by
  obtain ⟨_, hcomm, hpres⟩ := hTRI
  unfold pushedReference
  rw [Measure.map_map theta.measurable (D.flow (-s)).measurable]
  have : (theta ∘ D.flow (-s)) = (D.flow s) ∘ theta := by
    funext x; simp only [Function.comp_apply]; rw [hcomm (-s) x, neg_neg]
  rw [this, ← Measure.map_map (D.flow s).measurable theta.measurable, hpres]

/-- rho_t ∘ theta = rho_{-t}, a.e. -/
lemma g68c_key (D : NonsingularSystem K M) (theta : M ≃ᵐ M)
    (hTRI : IsTimeReversal D theta) (t : K.Carrier) :
    ∀ᵐ y ∂(D.omega : Measure M),
      (pushedReference D t).rnDeriv (D.omega : Measure M) (theta y) =
        (pushedReference D (-t)).rnDeriv (D.omega : Measure M) y := by
  haveI := g68c_prob D (-t)
  have h := theta.measurableEmbedding.rnDeriv_map (pushedReference D (-t)) (D.omega : Measure M)
  rw [g68c_map_theta D theta hTRI t, hTRI.2.2] at h
  exact h

/-- omega_{-t} = e^{-c^t} omega. -/
lemma g68c_back (D : NonsingularSystem K M) (t : K.Carrier) :
    (D.omega : Measure M).withDensity (fun x => ENNReal.ofReal (Real.exp (-(entropyCocycle D t x)))) =
      pushedReference D (-t) := by
  haveI := g68c_prob D t
  set ω : Measure M := (D.omega : Measure M)
  set F : M → ℝ≥0∞ := fun x => ENNReal.ofReal (Real.exp (-(entropyCocycle D t x)))
  have hF : Measurable F :=
    ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp (g68c_meas_c D t).neg)
  have hω : ω = (pushedReference D t).map (D.flow (-t)) := by
    rw [pushedReference, Measure.map_map (D.flow (-t)).measurable (D.flow t).measurable]
    have : D.flow (-t) ∘ D.flow t = id := funext fun x => g68c_inv D t x
    rw [this, Measure.map_id]
  ext A hA
  rw [withDensity_apply _ hA, pushedReference, Measure.map_apply (D.flow (-t)).measurable hA]
  have e1 : ∫⁻ x in A, F x ∂ω = ∫⁻ x, A.indicator F x ∂ω := (lintegral_indicator hA _).symm
  have hAF : Measurable (A.indicator F) := hF.indicator hA
  rw [e1]
  conv_lhs => rw [hω]
  rw [lintegral_map hAF (D.flow (-t)).measurable,
    ← MeasureTheory.lintegral_rnDeriv_mul (μ := pushedReference D t) (ν := ω) (D.equivalent t).1
      (f := fun y => A.indicator F (D.flow (-t) y)) (hAF.comp (D.flow (-t)).measurable).aemeasurable]
  rw [← lintegral_indicator_one ((D.flow (-t)).measurable hA)]
  apply lintegral_congr_ae
  have hpos : ∀ᵐ y ∂ω, 0 < (pushedReference D t).rnDeriv ω y :=
    (D.equivalent t).2.ae_le (Measure.rnDeriv_pos (D.equivalent t).1)
  filter_upwards [hpos, Measure.rnDeriv_lt_top (pushedReference D t) ω] with y hp hl
  by_cases hy : D.flow (-t) y ∈ A
  · simp only [Set.indicator, Set.mem_preimage, hy, if_true, Pi.one_apply]
    simp only [F, entropyCocycle, logDensity, referenceRNReal, g68c_inv']
    set r := (pushedReference D t).rnDeriv ω y
    have hr : 0 < r.toReal := ENNReal.toReal_pos hp.ne' hl.ne
    rw [Real.exp_neg, Real.exp_log hr, ENNReal.ofReal_inv_of_pos hr, ENNReal.ofReal_toReal hl.ne,
      ENNReal.mul_inv_cancel hp.ne' hl.ne]
  · simp [Set.indicator, hy]

section G68H
variable {X : Type*} [MeasurableSpace X]

lemma g68h_pos (ω : Measure X) [IsProbabilityMeasure ω] (ℓ : X → ℝ) (hm : Measurable ℓ) (α : ℝ) :
    0 < ∫⁻ x, ENNReal.ofReal (Real.exp (α * ℓ x)) ∂ω := by
  rw [pos_iff_ne_zero, Ne, lintegral_eq_zero_iff (by fun_prop)]
  intro h
  have : ∀ᵐ x ∂ω, False := by
    filter_upwards [h] with x hx
    simp only [Pi.zero_apply, ENNReal.ofReal_eq_zero] at hx
    exact (Real.exp_pos _).not_ge hx
  exact IsProbabilityMeasure.ne_zero ω (by simpa using this)

lemma g68h_holder (ω : Measure X) (ℓ : X → ℝ) (hm : Measurable ℓ) (a b w : ℝ) (hw0 : 0 < w) (hw1 : w < 1) :
    ∫⁻ x, ENNReal.ofReal (Real.exp ((w * a + (1 - w) * b) * ℓ x)) ∂ω ≤
      (∫⁻ x, ENNReal.ofReal (Real.exp (a * ℓ x)) ∂ω) ^ w *
        (∫⁻ x, ENNReal.ofReal (Real.exp (b * ℓ x)) ∂ω) ^ (1 - w) := by
  have h1w : 0 < 1 - w := by linarith
  have hpq : (1 / w).HolderConjugate (1 / (1 - w)) :=
    ⟨by simp only [one_div, inv_inv, inv_one]; ring, by positivity, by positivity⟩
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq ω hpq
    (f := fun x => ENNReal.ofReal (Real.exp (w * a * ℓ x)))
    (g := fun x => ENNReal.ofReal (Real.exp ((1 - w) * b * ℓ x))) (by fun_prop) (by fun_prop)
  have e1 : ∀ x, (fun x => ENNReal.ofReal (Real.exp (w * a * ℓ x))) x ^ (1 / w) =
      ENNReal.ofReal (Real.exp (a * ℓ x)) := by
    intro x
    rw [ENNReal.ofReal_rpow_of_pos (Real.exp_pos _), ← Real.exp_mul]
    congr 2; field_simp
  have e2 : ∀ x, (fun x => ENNReal.ofReal (Real.exp ((1 - w) * b * ℓ x))) x ^ (1 / (1 - w)) =
      ENNReal.ofReal (Real.exp (b * ℓ x)) := by
    intro x
    have : (1 - w) ≠ 0 := by linarith
    rw [ENNReal.ofReal_rpow_of_pos (Real.exp_pos _), ← Real.exp_mul]
    congr 2; field_simp
  simp only [e1, e2, one_div_one_div] at h
  refine le_trans (le_of_eq ?_) h
  refine lintegral_congr fun x => ?_
  simp only [Pi.mul_apply]
  rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
  congr 2; ring

lemma g68h_real (ω : Measure X) [IsProbabilityMeasure ω] (ℓ : X → ℝ) (hm : Measurable ℓ) (a r : ℝ)
    (h : ENNReal.log (∫⁻ x, ENNReal.ofReal (Real.exp (a * ℓ x)) ∂ω) ≤ (r : EReal)) :
    ∃ A : ℝ, 0 < A ∧ ∫⁻ x, ENNReal.ofReal (Real.exp (a * ℓ x)) ∂ω = ENNReal.ofReal A ∧ Real.log A ≤ r := by
  set I := ∫⁻ x, ENNReal.ofReal (Real.exp (a * ℓ x)) ∂ω
  have hI0 : 0 < I := g68h_pos ω ℓ hm a
  have hIt : I ≠ ⊤ := by
    intro hI; rw [hI, ENNReal.log_top] at h; exact absurd h (by simp)
  refine ⟨I.toReal, ENNReal.toReal_pos hI0.ne' hIt, (ENNReal.ofReal_toReal hIt).symm, ?_⟩
  rw [← ENNReal.ofReal_toReal hIt, ENNReal.log_ofReal_of_pos (ENNReal.toReal_pos hI0.ne' hIt)] at h
  exact EReal.coe_le_coe_iff.mp h

lemma g68h_convex (ω : Measure X) [IsProbabilityMeasure ω] (ℓ : X → ℝ) (hm : Measurable ℓ) :
    ExtendedConvex (fun α => ENNReal.log (∫⁻ x, ENNReal.ofReal (Real.exp (α * ℓ x)) ∂ω)) := by
  intro a b r s w hr hs hw0 hw1
  rcases hw0.eq_or_lt with h0 | h0
  · subst h0; simpa using hs
  rcases hw1.eq_or_lt with h1 | h1
  · subst h1; simpa using hr
  obtain ⟨A, hA, hIA, hAr⟩ := g68h_real ω ℓ hm a r hr
  obtain ⟨B, hB, hIB, hBs⟩ := g68h_real ω ℓ hm b s hs
  have hH := g68h_holder ω ℓ hm a b w h0 h1
  rw [hIA, hIB, ENNReal.ofReal_rpow_of_pos hA, ENNReal.ofReal_rpow_of_pos hB,
    ← ENNReal.ofReal_mul (Real.rpow_pos_of_pos hA _).le] at hH
  have hP : 0 < A ^ w * B ^ (1 - w) := mul_pos (Real.rpow_pos_of_pos hA _) (Real.rpow_pos_of_pos hB _)
  refine (ENNReal.log_le_log hH).trans ?_
  rw [ENNReal.log_ofReal_of_pos hP, EReal.coe_le_coe_iff, Real.log_mul (Real.rpow_pos_of_pos hA _).ne'
    (Real.rpow_pos_of_pos hB _).ne', Real.log_rpow hA, Real.log_rpow hB]
  have : 0 < 1 - w := by linarith
  nlinarith

end G68H

lemma g68h_jensen {X : Type*} [MeasurableSpace X] (ω : Measure X) [IsProbabilityMeasure ω] (g : X → ℝ)
    (hg : Integrable g ω) :
    ENNReal.ofReal (Real.exp (∫ x, g x ∂ω)) ≤ ∫⁻ x, ENNReal.ofReal (Real.exp (g x)) ∂ω := by
  by_cases hI : ∫⁻ x, ENNReal.ofReal (Real.exp (g x)) ∂ω = ⊤
  · rw [hI]; exact le_top
  have hint : Integrable (fun x => Real.exp (g x)) ω := by
    have := integrable_toReal_of_lintegral_ne_top
      (hg.aemeasurable.exp.ennreal_ofReal : AEMeasurable (fun x => ENNReal.ofReal (Real.exp (g x))) ω) hI
    simpa [ENNReal.toReal_ofReal (Real.exp_pos _).le] using this
  rw [← ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ fun x => (Real.exp_pos _).le)]
  refine ENNReal.ofReal_le_ofReal ?_
  set c := ∫ x, g x ∂ω
  have hlow : ∀ x, Real.exp c * (1 + (g x - c)) ≤ Real.exp (g x) := by
    intro x
    have := Real.add_one_le_exp (g x - c)
    calc Real.exp c * (1 + (g x - c)) ≤ Real.exp c * Real.exp (g x - c) :=
          mul_le_mul_of_nonneg_left (by linarith) (Real.exp_pos _).le
      _ = Real.exp (g x) := by rw [← Real.exp_add]; congr 1; ring
  have h2 : Integrable (fun x => Real.exp c * (1 + (g x - c))) ω :=
    ((integrable_const 1).add (hg.sub (integrable_const c))).const_mul _
  have hsub : Integrable (fun x => g x - c) ω := hg.sub (integrable_const c)
  calc Real.exp c = ∫ x, Real.exp c * (1 + (g x - c)) ∂ω := by
        rw [integral_const_mul, integral_add (integrable_const 1) hsub,
          integral_sub hg (integrable_const c)]
        simp [c]
    _ ≤ ∫ x, Real.exp (g x) ∂ω := integral_mono h2 hint hlow

variable {K : TimeKind} {M : Type*} [MeasurableSpace M]

lemma g68h_I1 (D : NonsingularSystem K M) (t : K.Carrier) :
    ∫⁻ x, ENNReal.ofReal (Real.exp (1 * logDensity D t x)) ∂(D.omega : Measure M) = 1 := by
  haveI := g68c_prob D t
  have hρpos : ∀ᵐ x ∂(D.omega : Measure M), 0 < (pushedReference D t).rnDeriv (D.omega : Measure M) x :=
    (D.equivalent t).2.ae_le (Measure.rnDeriv_pos (D.equivalent t).1)
  rw [lintegral_congr_ae (g := (pushedReference D t).rnDeriv (D.omega : Measure M))]
  · rw [Measure.lintegral_rnDeriv (μ := pushedReference D t) (D.equivalent t).1]; simp
  · filter_upwards [hρpos, Measure.rnDeriv_lt_top (pushedReference D t) (D.omega : Measure M)] with x hp hl
    simp only [one_mul, logDensity, referenceRNReal]
    rw [Real.exp_log (ENNReal.toReal_pos hp.ne' hl.ne), ENNReal.ofReal_toReal hl.ne]

lemma g68h_min (D : NonsingularSystem K M) (t : K.Carrier) (alpha : ℝ) (e0 : finiteES D t 0 = 0) :
    min ((alpha : EReal) * signedEntropy (D.omega : Measure M) (pushedReference D t))
      (((1 - alpha : ℝ) : EReal) * signedEntropy (pushedReference D t) (D.omega : Measure M))
        ≤ finiteES D t alpha := by
  haveI := g68c_prob D t
  set ω : Measure M := (D.omega : Measure M)
  set ωt := pushedReference D t
  rcases le_or_gt 0 alpha with hα | hα
  · refine (min_le_left _ _).trans ?_
    by_cases hk : InformationTheory.klDiv ω ωt = ⊤
    · rcases hα.eq_or_lt with h0 | hpos
      · subst h0; simp [e0]
      · simp [signedEntropy, hk, EReal.coe_mul_bot_of_pos hpos]
    obtain ⟨hac, hint⟩ := InformationTheory.klDiv_ne_top_iff.mp hk
    have hllr : llr ω ωt =ᵐ[ω] fun x => -logDensity D t x := by
      filter_upwards [Measure.inv_rnDeriv' hac] with x hx
      simp only [llr, logDensity, referenceRNReal, ← hx, Pi.inv_apply, ENNReal.toReal_inv, Real.log_inv]
      rfl
    have hℓ : Integrable (fun x => alpha * logDensity D t x) ω :=
      (hint.neg.congr (hllr.mono fun x hx => by simp [hx])).const_mul alpha
    have hJ := g68h_jensen ω _ hℓ
    have hk0 : 0 ≤ ∫ x, llr ω ωt x ∂ω := by
      simpa using InformationTheory.integral_llr_add_sub_measure_univ_nonneg hac hint
    rw [signedEntropy, InformationTheory.klDiv_of_ac_of_integrable hac hint]
    simp only [probReal_univ, add_sub_cancel_right]
    rw [EReal.coe_ennreal_ofReal, max_eq_left hk0, ← EReal.coe_neg, ← EReal.coe_mul]
    have : ∫ x, alpha * logDensity D t x ∂ω = alpha * -∫ x, llr ω ωt x ∂ω := by
      rw [integral_const_mul, integral_congr_ae hllr, integral_neg, neg_neg]
    rw [this] at hJ
    have := ENNReal.log_le_log hJ
    rwa [ENNReal.log_ofReal_of_pos (Real.exp_pos _), Real.log_exp] at this
  · refine (min_le_right _ _).trans ?_
    have h1α : 0 < 1 - alpha := by linarith
    by_cases hk : InformationTheory.klDiv ωt ω = ⊤
    · rw [signedEntropy, hk, EReal.coe_ennreal_top, EReal.neg_top, EReal.coe_mul_bot_of_pos h1α]
      exact bot_le
    obtain ⟨hac, hint⟩ := InformationTheory.klDiv_ne_top_iff.mp hk
    have hk0 : 0 ≤ ∫ x, llr ωt ω x ∂ωt := by
      simpa using InformationTheory.integral_llr_add_sub_measure_univ_nonneg hac hint
    have hℓ : Integrable (fun x => (alpha - 1) * logDensity D t x) ωt := hint.const_mul (alpha - 1)
    have hJ := g68h_jensen ωt _ hℓ
    have hchange : ∫⁻ x, ENNReal.ofReal (Real.exp ((alpha - 1) * logDensity D t x)) ∂ωt =
        ∫⁻ x, ENNReal.ofReal (Real.exp (alpha * logDensity D t x)) ∂ω := by
      rw [← MeasureTheory.lintegral_rnDeriv_mul (μ := ωt) (ν := ω) (D.equivalent t).1
        (f := fun x => ENNReal.ofReal (Real.exp ((alpha - 1) * logDensity D t x)))
        (ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp
          ((g68c_meas_ell D t).const_mul _))).aemeasurable]
      refine lintegral_congr_ae ?_
      have hρpos : ∀ᵐ x ∂ω, 0 < ωt.rnDeriv ω x :=
        (D.equivalent t).2.ae_le (Measure.rnDeriv_pos (D.equivalent t).1)
      filter_upwards [hρpos, Measure.rnDeriv_lt_top ωt ω] with x hp hl
      have hr := ENNReal.toReal_pos hp.ne' hl.ne
      simp only [logDensity, referenceRNReal]
      nth_rewrite 1 [← ENNReal.ofReal_toReal hl.ne]
      rw [← ENNReal.ofReal_mul hr.le]
      congr 1
      nth_rw 1 [← Real.exp_log hr]
      rw [← Real.exp_add]; congr 1; ring
    rw [hchange] at hJ
    rw [signedEntropy, InformationTheory.klDiv_of_ac_of_integrable hac hint]
    simp only [probReal_univ, add_sub_cancel_right]
    rw [EReal.coe_ennreal_ofReal, max_eq_left hk0, ← EReal.coe_neg, ← EReal.coe_mul]
    have : ∫ x, (alpha - 1) * logDensity D t x ∂ωt = (1 - alpha) * -∫ x, llr ωt ω x ∂ωt := by
      rw [integral_const_mul]
      show (alpha - 1) * ∫ x, logDensity D t x ∂ωt = (1 - alpha) * -∫ x, logDensity D t x ∂ωt
      ring
    rw [this] at hJ
    have := ENNReal.log_le_log hJ
    rwa [ENNReal.log_ofReal_of_pos (Real.exp_pos _), Real.log_exp] at this
/-- Proposition 3.4, PDF p.10: all three clauses, including the minimum
of the two signed-entropy bounds and real analyticity on the open unit interval. -/
theorem solution (D : NonsingularSystem K M) (t : K.Carrier) :
    ExtendedConvex (finiteES D t) ∧
    finiteES D t 0 = 0 ∧ finiteES D t 1 = 0 ∧
    (∀ alpha, (⊥ : EReal) < finiteES D t alpha) ∧
    (∀ alpha ∈ Icc (0 : ℝ) 1, finiteES D t alpha ≤ 0) ∧
    (∀ alpha, alpha ∉ Icc (0 : ℝ) 1 → 0 ≤ finiteES D t alpha) ∧
    (∀ alpha : ℝ, min ((alpha : EReal) * signedEntropy (D.omega : Measure M) (pushedReference D t))
      (((1 - alpha : ℝ) : EReal) * signedEntropy (pushedReference D t) (D.omega : Measure M))
        ≤ finiteES D t alpha) ∧
    AnalyticOnNhd ℝ (fun alpha => (finiteES D t alpha).toReal) (Ioo (0 : ℝ) 1) := by
  haveI := g68c_prob D t
  have hm := g68c_meas_ell D t
  have hfe : finiteES D t = fun α => ENNReal.log
      (∫⁻ x, ENNReal.ofReal (Real.exp (α * logDensity D t x)) ∂(D.omega : Measure M)) := rfl
  have hconv : ExtendedConvex (finiteES D t) := by
    rw [hfe]; exact g68h_convex _ _ hm
  have e0 : finiteES D t 0 = 0 := by simp [finiteES]
  have e1 : finiteES D t 1 = 0 := by rw [hfe]; simp only; rw [g68h_I1, ENNReal.log_one]
  have ebot : ∀ α, (⊥ : EReal) < finiteES D t α := by
    intro α
    rw [hfe, bot_lt_iff_ne_bot, Ne, ENNReal.log_eq_bot_iff]
    exact (g68h_pos _ _ hm α).ne'
  have e0' : finiteES D t 0 ≤ ((0 : ℝ) : EReal) := by rw [e0]; simp
  have e1' : finiteES D t 1 ≤ ((0 : ℝ) : EReal) := by rw [e1]; simp
  refine ⟨hconv, e0, e1, ebot, ?_, ?_, fun α => g68h_min D t α e0, ?_⟩
  · rintro α ⟨h0, h1⟩
    have := hconv 1 0 0 0 α e1' e0' h0 h1
    simpa using this
  · intro α hα
    by_cases htop : finiteES D t α = ⊤
    · rw [htop]; exact le_top
    have hr : finiteES D t α = ((finiteES D t α).toReal : EReal) :=
      (EReal.coe_toReal htop (ebot α).ne').symm
    set r := (finiteES D t α).toReal
    rw [hr]
    apply EReal.coe_nonneg.mpr
    simp only [Set.mem_Icc, not_and_or, not_le] at hα
    rcases hα with hneg | hgt
    · have hne : 1 - α ≠ 0 := by linarith
      set w := 1 / (1 - α)
      have hw0 : 0 < w := div_pos one_pos (by linarith)
      have hw1 : w ≤ 1 := by rw [div_le_one (by linarith)]; linarith
      have := hconv α 1 r 0 w hr.le e1' hw0.le hw1
      rw [show w * α + (1 - w) * 1 = 0 by simp only [w]; field_simp; try ring, e0] at this
      have h' : (0 : ℝ) ≤ w * r + (1 - w) * 0 := by exact_mod_cast this
      nlinarith
    · set w := 1 / α
      have hw0 : 0 < w := by positivity
      have hw1 : w ≤ 1 := by rw [div_le_one (by linarith)]; linarith
      have := hconv α 0 r 0 w hr.le e0' hw0.le hw1
      rw [show w * α + (1 - w) * 0 = 1 by simp only [w]; field_simp; try ring, e1] at this
      have h' : (0 : ℝ) ≤ w * r + (1 - w) * 0 := by exact_mod_cast this
      nlinarith
  · -- analyticity
    set ω : Measure M := (D.omega : Measure M)
    have hexp1 : Integrable (fun x => Real.exp (logDensity D t x)) ω := by
      have h := g68h_I1 D t
      simp only [one_mul] at h
      have := integrable_toReal_of_lintegral_ne_top
        (by fun_prop : AEMeasurable (fun x => ENNReal.ofReal (Real.exp (logDensity D t x))) ω)
        (by rw [h]; exact ENNReal.one_ne_top)
      simpa [ENNReal.toReal_ofReal (Real.exp_pos _).le] using this
    have hI : ∀ α ∈ Icc (0 : ℝ) 1, Integrable (fun x => Real.exp (α * logDensity D t x)) ω := by
      rintro α ⟨h0, h1⟩
      refine Integrable.mono' ((integrable_const 1).add hexp1) (by fun_prop) (ae_of_all _ fun x => ?_)
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      simp only [Pi.add_apply]
      rcases le_total 0 (logDensity D t x) with h | h
      · have : α * logDensity D t x ≤ logDensity D t x := by nlinarith
        linarith [Real.exp_le_exp.mpr this, Real.exp_pos 0]
      · have : α * logDensity D t x ≤ 0 := by nlinarith
        linarith [Real.exp_le_exp.mpr this, Real.exp_pos (logDensity D t x), Real.exp_zero]
    have hint : Ioo (0 : ℝ) 1 ⊆ interior (ProbabilityTheory.integrableExpSet (logDensity D t) ω) := by
      rw [← isOpen_Ioo.interior_eq]
      exact interior_mono fun α hα => hI α (Ioo_subset_Icc_self hα)
    have hA : AnalyticOnNhd ℝ (fun α => Real.log (ProbabilityTheory.mgf (logDensity D t) ω α)) (Ioo 0 1) := by
      intro α hα
      exact (ProbabilityTheory.analyticAt_mgf (hint hα)).log
        (integral_exp_pos (hI α (Ioo_subset_Icc_self hα)))
    refine hA.congr isOpen_Ioo fun α hα => ?_
    have hIα := hI α (Ioo_subset_Icc_self hα)
    simp only [finiteES, ProbabilityTheory.mgf]
    rw [← ofReal_integral_eq_lintegral_ofReal hIα (ae_of_all _ fun x => (Real.exp_pos _).le),
      ENNReal.log_ofReal_of_pos (integral_exp_pos hIα), EReal.toReal_coe]
