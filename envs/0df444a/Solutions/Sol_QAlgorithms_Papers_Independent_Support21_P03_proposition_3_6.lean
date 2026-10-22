-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Support21.P03.proposition_3_6
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T09:40:01.757595+00:00
-- url     : https://prove2.me/submissions/3cc762c8-599c-4de3-a794-88f10a5950f5

import Definitions.Def_QAlgorithms_Papers_Independent_Support21_P03
noncomputable section

open MeasureTheory Filter Set
open ProbabilityTheory (mgf complexMGF integrableExpSet eqOn_complexMGF_of_mgf' integrableExpSet_eq_of_mgf')

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

lemma g68d_int {R : Measure ℝ} {u : ℝ} (h : ∫⁻ s, ENNReal.ofReal (Real.exp (u * s)) ∂(R) < ∞) :
    Integrable (fun s => Real.exp (u * s)) R := by
  have := integrable_toReal_of_lintegral_ne_top
    (by fun_prop : AEMeasurable (fun s => ENNReal.ofReal (Real.exp (u * s))) R) h.ne
  simpa [ENNReal.toReal_ofReal (Real.exp_pos _).le] using this

/-- Two finite measures on ℝ whose (lintegral) exponential moments agree for all real exponents,
and are finite at some τ ≠ 0, are equal. -/
lemma g68d_ext (R Q : Measure ℝ) [IsFiniteMeasure R] [IsFiniteMeasure Q] (τ : ℝ) (hτ : τ ≠ 0)
    (h0 : ∫⁻ s, ENNReal.ofReal (Real.exp (τ * s)) ∂(R) < ∞)
    (heq : ∀ u, ∫⁻ s, ENNReal.ofReal (Real.exp (u * s)) ∂(R) = ∫⁻ s, ENNReal.ofReal (Real.exp (u * s)) ∂(Q)) :
    R = Q := by
  -- equal mgf
  have hmgf : mgf id R = mgf id Q := by
    funext u
    simp only [mgf, id]
    rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun s => (Real.exp_pos _).le) (by fun_prop),
      integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun s => (Real.exp_pos _).le) (by fun_prop), heq]
  have hzero : R = 0 ↔ Q = 0 := by
    have := heq 0
    simp only [zero_mul, Real.exp_zero, ENNReal.ofReal_one, lintegral_one] at this
    rw [← Measure.measure_univ_eq_zero, ← Measure.measure_univ_eq_zero, this]
  -- integrability on the open interval between 0 and τ
  have hI : Set.Ioo (min 0 τ) (max 0 τ) ⊆ integrableExpSet id R := by
    intro u hu
    simp only [integrableExpSet, Set.mem_ofPred_eq, id]
    refine Integrable.mono' ((integrable_const 1).add (g68d_int h0)) (by fun_prop)
      (ae_of_all _ fun s => ?_)
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    have : u * s ≤ max 0 (τ * s) := by
      rcases le_total 0 s with hs | hs
      · rcases le_total 0 τ with ht | ht
        · simp only [min_eq_left ht, max_eq_right ht] at hu
          exact le_max_of_le_right (mul_le_mul_of_nonneg_right hu.2.le hs)
        · simp only [min_eq_right ht, max_eq_left ht] at hu
          exact le_max_of_le_left (mul_nonpos_of_nonpos_of_nonneg hu.2.le hs)
      · rcases le_total 0 τ with ht | ht
        · simp only [min_eq_left ht, max_eq_right ht] at hu
          exact le_max_of_le_left (mul_nonpos_of_nonneg_of_nonpos hu.1.le hs)
        · simp only [min_eq_right ht, max_eq_left ht] at hu
          exact le_max_of_le_right (mul_le_mul_of_nonpos_right hu.1.le hs)
    simp only [Pi.add_apply]
    rcases le_total 0 (τ * s) with h | h
    · rw [max_eq_right h] at this
      linarith [Real.exp_le_exp.mpr this, Real.exp_pos 0]
    · rw [max_eq_left h] at this
      linarith [Real.exp_le_exp.mpr this, Real.exp_pos (τ * s), Real.exp_zero]
  set η := τ / 2
  have hη : η ∈ interior (integrableExpSet id R) := by
    refine interior_mono hI ?_
    rw [isOpen_Ioo.interior_eq]
    rcases lt_or_gt_of_ne hτ with h | h
    · simp only [min_eq_right h.le, max_eq_left h.le, Set.mem_Ioo, η]; constructor <;> linarith
    · simp only [min_eq_left h.le, max_eq_right h.le, Set.mem_Ioo, η]; constructor <;> linarith
  have hstrip := eqOn_complexMGF_of_mgf' hmgf hzero
  -- tilted measures
  set w : ℝ → NNReal := fun s => (Real.exp (η * s)).toNNReal with hw
  have hwm : Measurable w := by fun_prop
  have hRη : Integrable (fun s => Real.exp (η * s)) R := by
    have h1 : η ∈ integrableExpSet id R := interior_subset hη
    exact h1
  have hQη : Integrable (fun s => Real.exp (η * s)) Q := by
    have : η ∈ integrableExpSet id Q := by
      rw [← integrableExpSet_eq_of_mgf' hmgf hzero]; exact interior_subset hη
    exact this
  haveI : IsFiniteMeasure (R.withDensity fun s => (w s : ℝ≥0∞)) := by
    refine ⟨?_⟩
    rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
    exact hRη.lintegral_lt_top
  haveI : IsFiniteMeasure (Q.withDensity fun s => (w s : ℝ≥0∞)) := by
    refine ⟨?_⟩
    rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
    exact hQη.lintegral_lt_top
  have hchar : ∀ (μ : Measure ℝ) (y : ℝ), charFun (μ.withDensity fun s => (w s : ℝ≥0∞)) y =
      complexMGF id μ (η + y * Complex.I) := by
    intro μ y
    rw [charFun_apply_real, integral_withDensity_eq_integral_smul hwm, complexMGF]
    refine integral_congr_ae (ae_of_all _ fun s => ?_)
    simp only [hw, id, NNReal.smul_def, Real.coe_toNNReal _ (Real.exp_pos _).le, Complex.real_smul,
      Complex.ofReal_exp]
    rw [← Complex.exp_add]; congr 1; push_cast; ring
  have hRQ' : (R.withDensity fun s => (w s : ℝ≥0∞)) = (Q.withDensity fun s => (w s : ℝ≥0∞)) := by
    apply Measure.ext_of_charFun
    funext y
    rw [hchar, hchar]
    exact hstrip (by simpa using hη)
  ext A hA
  have key : ∀ μ : Measure ℝ, μ A = ∫⁻ s in A, ENNReal.ofReal (Real.exp (-η * s)) ∂(μ.withDensity fun s => (w s : ℝ≥0∞)) := by
    intro μ
    rw [setLIntegral_withDensity_eq_setLIntegral_mul _ (by fun_prop) (by fun_prop) hA]
    rw [← setLIntegral_one]
    refine setLIntegral_congr_fun hA fun s _ => ?_
    simp only [Pi.mul_apply, hw, ENNReal.ofNNReal_toNNReal]
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
    simp
  rw [key R, key Q, hRQ']

lemma g68d_es (P : Measure ℝ) [IsProbabilityMeasure P] (τ : ℝ) (hτ : τ ≠ 0)
    (h1 : ∫⁻ s, ENNReal.ofReal (Real.exp (-1 * τ * s)) ∂(P) < ∞) :
    ESIdentity P τ ↔ ∀ α : ℝ, ∫⁻ s, ENNReal.ofReal (Real.exp (-α * τ * s)) ∂(P) =
      ∫⁻ s, ENNReal.ofReal (Real.exp (-(1 - α) * τ * s)) ∂(P) := by
  set g : ℝ → ℝ≥0∞ := fun s => ENNReal.ofReal (Real.exp (-τ * s)) with hgdef
  have hg : Measurable g := by fun_prop
  set R := reflectedLaw P
  set Q := P.withDensity g
  have hφR : ∀ u, ∫⁻ s, ENNReal.ofReal (Real.exp (u * s)) ∂(R) =
      ∫⁻ s, ENNReal.ofReal (Real.exp (-(u / τ) * τ * s)) ∂(P) := by
    intro u
    simp only [R, reflectedLaw]
    rw [lintegral_map (by fun_prop) measurable_neg]
    refine lintegral_congr fun s => ?_
    congr 2; field_simp
  have hφQ : ∀ u, ∫⁻ s, ENNReal.ofReal (Real.exp (u * s)) ∂(Q) =
      ∫⁻ s, ENNReal.ofReal (Real.exp (-(1 - u / τ) * τ * s)) ∂(P) := by
    intro u
    simp only [Q]
    rw [lintegral_withDensity_eq_lintegral_mul _ hg (by fun_prop)]
    refine lintegral_congr fun s => ?_
    simp only [Pi.mul_apply, hgdef]
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
    congr 2; field_simp; ring
  haveI : IsProbabilityMeasure R := Measure.isProbabilityMeasure_map measurable_neg.aemeasurable
  constructor
  · rintro ⟨hRP, -, hrn⟩ α
    have hRQ : R = Q := by
      rw [← Measure.withDensity_rnDeriv_eq R P hRP]
      exact withDensity_congr_ae hrn
    have := hφR (α * τ)
    rw [hRQ, hφQ] at this
    rw [show α * τ / τ = α by field_simp] at this
    exact this.symm
  · intro hsym
    haveI : IsFiniteMeasure Q := by
      refine ⟨?_⟩
      rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
      simpa [hgdef, neg_mul] using h1
    have hRQ : R = Q := by
      refine g68d_ext R Q τ hτ ?_ fun u => ?_
      · rw [hφR, show τ / τ = 1 by field_simp]
        exact h1
      · rw [hφR, hφQ, hsym]
    change R ≪ P ∧ P ≪ R ∧ ∀ᵐ s ∂(P), R.rnDeriv P s = ENNReal.ofReal (Real.exp (-τ * s))
    rw [hRQ]
    refine ⟨?_, ?_, ?_⟩
    · exact withDensity_absolutelyContinuous _ _
    · exact withDensity_absolutelyContinuous' hg.aemeasurable
        (ae_of_all _ fun s => by simp [hgdef, Real.exp_pos])
    · exact Measure.rnDeriv_withDensity _ hg

/-- Proposition 3.6, PDF p.11: the symmetry uses e_{-t} on both sides. -/
theorem solution (D : NonsingularSystem K M) (t : K.Carrier)
    (ht : timeValue K t ≠ 0) :
    ESIdentity (entropyLaw D t) (timeValue K t) ↔
      ∀ alpha : ℝ, finiteES D (-t) alpha = finiteES D (-t) (1 - alpha) := by
  have hSig : Measurable (meanEntropy D t) := (g68c_meas_c D t).div_const _
  haveI : IsProbabilityMeasure (entropyLaw D t) := Measure.isProbabilityMeasure_map hSig.aemeasurable
  have hF : Measurable (fun x => ENNReal.ofReal (Real.exp (-(entropyCocycle D t x)))) :=
    ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp (g68c_meas_c D t).neg)
  have hρ : ∀ᵐ x ∂(D.omega : Measure M), (pushedReference D (-t)).rnDeriv (D.omega : Measure M) x =
      ENNReal.ofReal (Real.exp (-(entropyCocycle D t x))) := by
    rw [← g68c_back D t]
    exact Measure.rnDeriv_withDensity _ hF
  have hL : ∀ α : ℝ, ∫⁻ x, ENNReal.ofReal (Real.exp (α * logDensity D (-t) x)) ∂(D.omega : Measure M) =
      ∫⁻ s, ENNReal.ofReal (Real.exp (-α * timeValue K t * s)) ∂(entropyLaw D t) := by
    intro α
    rw [entropyLaw, lintegral_map (by fun_prop) hSig]
    refine lintegral_congr_ae ?_
    filter_upwards [hρ] with x hx
    simp only [logDensity, referenceRNReal, hx, ENNReal.toReal_ofReal (Real.exp_pos _).le, Real.log_exp,
      meanEntropy]
    congr 2; field_simp
  have h1 : ∫⁻ s, ENNReal.ofReal (Real.exp (-1 * timeValue K t * s)) ∂(entropyLaw D t) < ∞ := by
    rw [entropyLaw, lintegral_map (by fun_prop) hSig]
    have : ∫⁻ x, ENNReal.ofReal (Real.exp (-1 * timeValue K t * meanEntropy D t x)) ∂(D.omega : Measure M) =
        (pushedReference D (-t)) Set.univ := by
      rw [← g68c_back D t, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
      refine lintegral_congr fun x => ?_
      simp only [meanEntropy]; congr 2; field_simp
    rw [this]; haveI := g68c_prob D (-t); exact measure_lt_top _ _
  rw [g68d_es (entropyLaw D t) (timeValue K t) ht h1]
  refine forall_congr' fun α => ?_
  simp only [finiteES, ENNReal.log_eq_iff, hL]
