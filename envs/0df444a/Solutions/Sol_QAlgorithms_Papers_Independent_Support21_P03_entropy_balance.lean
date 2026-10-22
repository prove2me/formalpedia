-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Support21.P03.entropy_balance
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T09:49:48.320813+00:00
-- url     : https://prove2.me/submissions/e4d81e4d-08f9-4da7-a36b-8b44fbd72527

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


lemma g68e_tv (K : TimeKind) (t : K.Carrier) : timeValue K (-t) = -timeValue K t := by
  cases K
  · exact Int.cast_neg (R := ℝ) (t : ℤ)
  · rfl

lemma g68e_neg (D : NonsingularSystem K M) (t : K.Carrier) :
    ∀ᵐ x ∂(D.omega : Measure M), logDensity D (-t) x = -entropyCocycle D t x := by
  have hF : Measurable (fun x => ENNReal.ofReal (Real.exp (-(entropyCocycle D t x)))) :=
    ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp (g68c_meas_c D t).neg)
  have hρ : ∀ᵐ x ∂(D.omega : Measure M), (pushedReference D (-t)).rnDeriv (D.omega : Measure M) x =
      ENNReal.ofReal (Real.exp (-(entropyCocycle D t x))) := by
    rw [← g68c_back D t]
    exact Measure.rnDeriv_withDensity _ hF
  filter_upwards [hρ] with x hx
  simp only [logDensity, referenceRNReal, hx, ENNReal.toReal_ofReal (Real.exp_pos _).le, Real.log_exp]

lemma g68e_p32 (D : NonsingularSystem K M) (theta : M ≃ᵐ M)
    (hTRI : IsTimeReversal D theta) (t : K.Carrier) :
    ∀ᵐ x ∂(D.omega : Measure M), entropyCocycle D t (theta x) = entropyCocycle D (-t) x := by
  have hc : ∀ x, D.flow t (theta x) = theta (D.flow (-t) x) := by
    intro x; rw [hTRI.2.1 (-t) x, neg_neg]
  have hq : Measure.QuasiMeasurePreserving (D.flow (-t)) (D.omega : Measure M) (D.omega : Measure M) :=
    ⟨(D.flow (-t)).measurable, (D.equivalent (-t)).1⟩
  filter_upwards [hq.ae (g68c_key D theta hTRI t)] with x hx
  simp only [entropyCocycle, logDensity, referenceRNReal]
  rw [hc, hx]

/-- change of variables: ∫ ofReal(s c^t) dω = ∫ ofReal(s r log r) dω. -/
lemma g68e_cv (D : NonsingularSystem K M) (t : K.Carrier) (s : ℝ) :
    ∫⁻ x, ENNReal.ofReal (s * entropyCocycle D t x) ∂(D.omega : Measure M) =
      ∫⁻ y, ENNReal.ofReal (s * (((pushedReference D t).rnDeriv (D.omega : Measure M) y).toReal *
        Real.log (((pushedReference D t).rnDeriv (D.omega : Measure M) y).toReal))) ∂(D.omega : Measure M) := by
  haveI := g68c_prob D t
  have hm : Measurable (fun y => ENNReal.ofReal (s * logDensity D t y)) :=
    ENNReal.measurable_ofReal.comp ((g68c_meas_ell D t).const_mul s)
  have e1 : ∫⁻ x, ENNReal.ofReal (s * entropyCocycle D t x) ∂(D.omega : Measure M) =
      ∫⁻ y, ENNReal.ofReal (s * logDensity D t y) ∂(pushedReference D t) := by
    rw [pushedReference, lintegral_map hm (D.flow t).measurable]; rfl
  rw [e1, ← MeasureTheory.lintegral_rnDeriv_mul (μ := pushedReference D t) (ν := (D.omega : Measure M))
    (D.equivalent t).1 hm.aemeasurable]
  refine lintegral_congr_ae ?_
  filter_upwards [Measure.rnDeriv_lt_top (pushedReference D t) (D.omega : Measure M)] with y hl
  simp only [logDensity, referenceRNReal]
  set ρ := (pushedReference D t).rnDeriv (D.omega : Measure M) y
  rw [← ENNReal.ofReal_toReal hl.ne, ← ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hl.ne]
  congr 1; ring

/-- KL + B = D with B ≤ 1 finite. -/
lemma g68e_kl (D : NonsingularSystem K M) (t : K.Carrier) :
    InformationTheory.klDiv (pushedReference D t) (D.omega : Measure M) +
      (∫⁻ y, ENNReal.ofReal (-1 * (((pushedReference D t).rnDeriv (D.omega : Measure M) y).toReal *
        Real.log (((pushedReference D t).rnDeriv (D.omega : Measure M) y).toReal))) ∂(D.omega : Measure M)) =
      (∫⁻ y, ENNReal.ofReal (1 * (((pushedReference D t).rnDeriv (D.omega : Measure M) y).toReal *
        Real.log (((pushedReference D t).rnDeriv (D.omega : Measure M) y).toReal))) ∂(D.omega : Measure M)) ∧
      (∫⁻ y, ENNReal.ofReal (-1 * (((pushedReference D t).rnDeriv (D.omega : Measure M) y).toReal *
        Real.log (((pushedReference D t).rnDeriv (D.omega : Measure M) y).toReal))) ∂(D.omega : Measure M)) ≠ ⊤ := by
  haveI := g68c_prob D t
  set ω : Measure M := (D.omega : Measure M)
  set ρ := (pushedReference D t).rnDeriv ω
  have hρm : Measurable ρ := Measure.measurable_rnDeriv _ _
  set Dp := ∫⁻ y, ENNReal.ofReal (1 * ((ρ y).toReal * Real.log (ρ y).toReal)) ∂ω
  set Bn := ∫⁻ y, ENNReal.ofReal (-1 * ((ρ y).toReal * Real.log (ρ y).toReal)) ∂ω
  have hB : Bn ≤ 1 := by
    calc Bn ≤ ∫⁻ _y, 1 ∂ω := by
          refine lintegral_mono fun y => ?_
          rw [← ENNReal.ofReal_one]
          refine ENNReal.ofReal_le_ofReal ?_
          have h1 := Real.self_sub_one_le_mul_log (ENNReal.toReal_nonneg (a := ρ y))
          have h2 : 0 ≤ (ρ y).toReal := ENNReal.toReal_nonneg
          linarith
      _ = 1 := by simp
  have hBt : Bn ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top hB
  refine ⟨?_, hBt⟩
  have hKL : InformationTheory.klDiv (pushedReference D t) ω = ∫⁻ y, ENNReal.ofReal (InformationTheory.klFun (ρ y).toReal) ∂ω :=
    InformationTheory.klDiv_eq_lintegral_klFun_of_ac (D.equivalent t).1
  have hmass : ∫⁻ y, ENNReal.ofReal (ρ y).toReal ∂ω = 1 := by
    rw [lintegral_congr_ae (g := ρ)]
    · show ∫⁻ a, (pushedReference D t).rnDeriv ω a ∂ω = 1
      rw [Measure.lintegral_rnDeriv (μ := pushedReference D t) (D.equivalent t).1]; simp
    · filter_upwards [Measure.rnDeriv_lt_top (pushedReference D t) ω] with y hl
      exact ENNReal.ofReal_toReal hl.ne
  have hpt : ∀ y, ENNReal.ofReal (InformationTheory.klFun (ρ y).toReal) +
      ENNReal.ofReal (-1 * ((ρ y).toReal * Real.log (ρ y).toReal)) + ENNReal.ofReal (ρ y).toReal =
      ENNReal.ofReal (1 * ((ρ y).toReal * Real.log (ρ y).toReal)) + 1 := by
    intro y
    set r := (ρ y).toReal
    have hr : 0 ≤ r := ENNReal.toReal_nonneg
    have hk : 0 ≤ InformationTheory.klFun r := InformationTheory.klFun_nonneg hr
    rw [InformationTheory.klFun_apply] at hk ⊢
    rcases le_total 0 (r * Real.log r) with h | h
    · rw [ENNReal.ofReal_of_nonpos (p := -1 * (r * Real.log r)) (by linarith), add_zero, ← ENNReal.ofReal_add hk hr,
        ← ENNReal.ofReal_one, ← ENNReal.ofReal_add (by linarith) zero_le_one]
      congr 1; ring
    · rw [ENNReal.ofReal_of_nonpos (p := 1 * (r * Real.log r)) (by linarith), zero_add,
        ← ENNReal.ofReal_add hk (by linarith), ← ENNReal.ofReal_add (by linarith) hr, ← ENNReal.ofReal_one]
      congr 1; ring
  have m1 : Measurable (fun y => ENNReal.ofReal (InformationTheory.klFun (ρ y).toReal)) := by fun_prop
  have m2 : Measurable (fun y => ENNReal.ofReal (-1 * ((ρ y).toReal * Real.log (ρ y).toReal))) := by fun_prop
  have m12 : Measurable (fun y => ENNReal.ofReal (InformationTheory.klFun (ρ y).toReal) +
      ENNReal.ofReal (-1 * ((ρ y).toReal * Real.log (ρ y).toReal))) := by fun_prop
  have m4 : Measurable (fun y => ENNReal.ofReal (1 * ((ρ y).toReal * Real.log (ρ y).toReal))) := by fun_prop
  have e2 := lintegral_add_left (μ := ω) m1 (fun y => ENNReal.ofReal (-1 * ((ρ y).toReal * Real.log (ρ y).toReal)))
  have e := lintegral_add_left (μ := ω) m12 (fun y => ENNReal.ofReal (ρ y).toReal)
  have e3 := lintegral_add_left (μ := ω) m4 (fun _ => (1 : ℝ≥0∞))
  have hint : ∫⁻ y, ENNReal.ofReal (InformationTheory.klFun (ρ y).toReal) ∂ω + Bn + 1 = Dp + 1 := by
    nth_rw 1 [← hmass]
    simp only [Bn, Dp]
    rw [← e2, ← e, lintegral_congr hpt, e3]
    simp
  have hKB : InformationTheory.klDiv (pushedReference D t) ω + Bn = Dp := by
    rw [hKL]; exact (ENNReal.add_left_inj ENNReal.one_ne_top).mp hint
  exact hKB

lemma g68e_kl' (D : NonsingularSystem K M) (t : K.Carrier) :
    InformationTheory.klDiv (pushedReference D t) (D.omega : Measure M) +
      ∫⁻ x, ENNReal.ofReal (-entropyCocycle D t x) ∂(D.omega : Measure M) =
      ∫⁻ x, ENNReal.ofReal (entropyCocycle D t x) ∂(D.omega : Measure M) ∧
      ∫⁻ x, ENNReal.ofReal (-entropyCocycle D t x) ∂(D.omega : Measure M) ≠ ⊤ := by
  have h1 := g68e_cv D t 1
  have h2 := g68e_cv D t (-1)
  simp only [one_mul, neg_one_mul] at h1 h2
  obtain ⟨a, b⟩ := g68e_kl D t
  simp only [one_mul, neg_one_mul] at a b
  rw [h1, h2]; exact ⟨a, b⟩

lemma g68e_ereal (k b : ℝ≥0∞) (hb : b ≠ ⊤) : ((k + b : ℝ≥0∞) : EReal) - (b : EReal) = (k : EReal) := by
  rw [EReal.coe_ennreal_add, ← EReal.coe_ennreal_toReal hb, EReal.add_sub_cancel_right]

lemma g68e_ereal2 (x b : ℝ≥0∞) (hb : b ≠ ⊤) : (b : EReal) - ((x + b : ℝ≥0∞) : EReal) = -(x : EReal) := by
  rw [EReal.coe_ennreal_add, ← EReal.coe_ennreal_toReal hb]
  by_cases hx : x = ⊤
  · simp [hx]
  · rw [← EReal.coe_ennreal_toReal hx, ← EReal.coe_add, ← EReal.coe_sub, ← EReal.coe_neg,
      EReal.coe_eq_coe_iff]
    ring

open QAlgorithms.Papers.Independent.Next46.P01 (extendedExpectation) in
/-- Entropy balance, §3.2, PDF p.9: extended entropy, nonnegative mean,
transport under time reversal, and all nonzero-time identities. -/
theorem solution (D : NonsingularSystem K M) :
    (∀ t, signedEntropy (pushedReference D t) (D.omega : Measure M) =
      -QAlgorithms.Papers.Independent.Next46.P01.extendedExpectation (D.omega : Measure M) (entropyCocycle D t)) ∧
    (∀ t, timeValue K t ≠ 0 →
      signedEntropy (pushedReference D t) (D.omega : Measure M) =
        -((timeValue K t : ℝ) : EReal) *
          QAlgorithms.Papers.Independent.Next46.P01.extendedExpectation (D.omega : Measure M) (meanEntropy D t)) ∧
    (∀ t, 0 < timeValue K t →
      0 ≤ QAlgorithms.Papers.Independent.Next46.P01.extendedExpectation (D.omega : Measure M) (meanEntropy D t)) ∧
    (∀ t, timeValue K t ≠ 0 → ∀ᵐ x ∂(D.omega : Measure M),
      meanEntropy D t x = meanEntropy D (-t) (D.flow t x)) ∧
    (∀ theta : M ≃ᵐ M, IsTimeReversal D theta →
      ∀ t, timeValue K t ≠ 0 → ∀ᵐ x ∂(D.omega : Measure M),
        meanEntropy D t (theta x) = -meanEntropy D (-t) x ∧
        meanEntropy D t (theta x) = -meanEntropy D t (D.flow (-t) x)) := by
  have hE : ∀ t, extendedExpectation (D.omega : Measure M) (entropyCocycle D t) =
      ((InformationTheory.klDiv (pushedReference D t) (D.omega : Measure M) : ℝ≥0∞) : EReal) := by
    intro t
    obtain ⟨h1, h2⟩ := g68e_kl' D t
    unfold extendedExpectation
    rw [← h1, g68e_ereal _ _ h2]
  have hEm : ∀ t, timeValue K t ≠ 0 → extendedExpectation (D.omega : Measure M) (meanEntropy D t) =
      ((1 / timeValue K t : ℝ) : EReal) *
        ((InformationTheory.klDiv (pushedReference D t) (D.omega : Measure M) : ℝ≥0∞) : EReal) := by
    intro t ht
    obtain ⟨h1, h2⟩ := g68e_kl' D t
    have mc := g68c_meas_c D t
    unfold extendedExpectation meanEntropy
    rcases lt_or_gt_of_ne ht with hneg | hpos
    · have hc : 0 ≤ -1 / timeValue K t := by
        rw [neg_div]; exact neg_nonneg.mpr (one_div_neg.mpr hneg).le
      have a1 : ∫⁻ x, ENNReal.ofReal (entropyCocycle D t x / timeValue K t) ∂(D.omega : Measure M) =
          ENNReal.ofReal (-1 / timeValue K t) *
            ∫⁻ x, ENNReal.ofReal (-entropyCocycle D t x) ∂(D.omega : Measure M) := by
        rw [← lintegral_const_mul (f := fun x => ENNReal.ofReal (-entropyCocycle D t x)) _
          (ENNReal.measurable_ofReal.comp mc.neg)]
        refine lintegral_congr fun x => ?_
        rw [← ENNReal.ofReal_mul hc]; congr 1; field_simp
      have a2 : ∫⁻ x, ENNReal.ofReal (-(entropyCocycle D t x / timeValue K t)) ∂(D.omega : Measure M) =
          ENNReal.ofReal (-1 / timeValue K t) *
            ∫⁻ x, ENNReal.ofReal (entropyCocycle D t x) ∂(D.omega : Measure M) := by
        rw [← lintegral_const_mul (f := fun x => ENNReal.ofReal (entropyCocycle D t x)) _
          (ENNReal.measurable_ofReal.comp mc)]
        refine lintegral_congr fun x => ?_
        rw [← ENNReal.ofReal_mul hc]; congr 1; field_simp
      rw [a1, a2, ← h1, mul_add, g68e_ereal2 _ _ (ENNReal.mul_ne_top ENNReal.ofReal_ne_top h2),
        EReal.coe_ennreal_mul, EReal.coe_ennreal_ofReal, max_eq_left hc, ← EReal.neg_mul, ← EReal.coe_neg]
      congr 2; ring
    · have hc : 0 ≤ 1 / timeValue K t := (one_div_pos.mpr hpos).le
      have a1 : ∫⁻ x, ENNReal.ofReal (entropyCocycle D t x / timeValue K t) ∂(D.omega : Measure M) =
          ENNReal.ofReal (1 / timeValue K t) *
            ∫⁻ x, ENNReal.ofReal (entropyCocycle D t x) ∂(D.omega : Measure M) := by
        rw [← lintegral_const_mul (f := fun x => ENNReal.ofReal (entropyCocycle D t x)) _
          (ENNReal.measurable_ofReal.comp mc)]
        refine lintegral_congr fun x => ?_
        rw [← ENNReal.ofReal_mul hc]; congr 1; field_simp
      have a2 : ∫⁻ x, ENNReal.ofReal (-(entropyCocycle D t x / timeValue K t)) ∂(D.omega : Measure M) =
          ENNReal.ofReal (1 / timeValue K t) *
            ∫⁻ x, ENNReal.ofReal (-entropyCocycle D t x) ∂(D.omega : Measure M) := by
        rw [← lintegral_const_mul (f := fun x => ENNReal.ofReal (-entropyCocycle D t x)) _
          (ENNReal.measurable_ofReal.comp mc.neg)]
        refine lintegral_congr fun x => ?_
        rw [← ENNReal.ofReal_mul hc]; congr 1; field_simp
      rw [a1, a2, ← h1, mul_add, g68e_ereal _ _ (ENNReal.mul_ne_top ENNReal.ofReal_ne_top h2),
        EReal.coe_ennreal_mul, EReal.coe_ennreal_ofReal, max_eq_left hc]
  have P4 : ∀ t, ∀ᵐ x ∂(D.omega : Measure M), meanEntropy D t x = meanEntropy D (-t) (D.flow t x) := by
    intro t
    filter_upwards [g68e_neg D t] with x hx
    simp only [meanEntropy]
    rw [show entropyCocycle D (-t) (D.flow t x) = logDensity D (-t) x by
      simp only [entropyCocycle]; rw [g68c_inv]]
    rw [hx, g68e_tv, neg_div_neg_eq]
  refine ⟨fun t => ?_, fun t ht => ?_, fun t ht => ?_, fun t _ => P4 t, fun theta hTRI t _ => ?_⟩
  · rw [hE]; rfl
  · rw [hEm t ht, EReal.neg_mul, ← mul_assoc, ← EReal.coe_mul, mul_one_div_cancel ht, EReal.coe_one, one_mul]
    rfl
  · rw [hEm t ht.ne']
    exact EReal.mul_nonneg (EReal.coe_nonneg.mpr (one_div_pos.mpr ht).le) (EReal.coe_ennreal_nonneg _)
  · have h2 := P4 (-t)
    rw [neg_neg] at h2
    filter_upwards [g68e_p32 D theta hTRI t, h2] with x h1 h2
    have e1 : meanEntropy D t (theta x) = -meanEntropy D (-t) x := by
      simp only [meanEntropy]; rw [h1, g68e_tv, div_neg, neg_neg]
    exact ⟨e1, by rw [e1, h2]⟩
