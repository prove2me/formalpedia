-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Support21.P03.proposition_3_3
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T09:32:58.988088+00:00
-- url     : https://prove2.me/submissions/56f623fd-9495-418d-9c78-bbcfcecabb5f

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

/-- Proposition 3.3, PDF p.10: finite-time Evans--Searles theorem.
Time zero is excluded because (3.5) has no source convention there. -/
theorem solution (D : NonsingularSystem K M) (theta : M ≃ᵐ M)
    (hTRI : IsTimeReversal D theta) (t : K.Carrier) (ht : timeValue K t ≠ 0) :
    ESIdentity (entropyLaw D t) (timeValue K t) := by
  have hSig : Measurable (meanEntropy D t) := (g68c_meas_c D t).div_const _
  set g : ℝ → ℝ≥0∞ := fun s => ENNReal.ofReal (Real.exp (-timeValue K t * s)) with hgdef
  have hg : Measurable g :=
    ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp (measurable_const.mul measurable_id))
  have hF : Measurable (fun x => ENNReal.ofReal (Real.exp (-(entropyCocycle D t x)))) :=
    ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp (g68c_meas_c D t).neg)
  have hρ : ∀ᵐ x ∂(D.omega : Measure M), (pushedReference D (-t)).rnDeriv (D.omega : Measure M) x =
      ENNReal.ofReal (Real.exp (-(entropyCocycle D t x))) := by
    rw [← g68c_back D t]
    exact Measure.rnDeriv_withDensity _ hF
  have hsym : (fun x => meanEntropy D t (theta (D.flow t x))) =ᵐ[(D.omega : Measure M)]
      (fun x => -meanEntropy D t x) := by
    filter_upwards [g68c_key D theta hTRI t, hρ] with x h1 h2
    have hc : D.flow t (theta (D.flow t x)) = theta x := by
      have := hTRI.2.1 (-t) (D.flow t x)
      rw [neg_neg, g68c_inv] at this
      exact this.symm
    show logDensity D t (D.flow t (theta (D.flow t x))) / timeValue K t =
      -(logDensity D t (D.flow t x) / timeValue K t)
    rw [hc]
    unfold logDensity referenceRNReal
    rw [h1, h2, ENNReal.toReal_ofReal (Real.exp_pos _).le, Real.log_exp]
    unfold entropyCocycle logDensity referenceRNReal
    ring
  have hψ : Measurable (fun x => theta (D.flow t x)) := theta.measurable.comp (D.flow t).measurable
  have hmψ : (D.omega : Measure M).map (fun x => theta (D.flow t x)) = pushedReference D (-t) := by
    rw [show (fun x => theta (D.flow t x)) = theta ∘ D.flow t from rfl,
      ← Measure.map_map theta.measurable (D.flow t).measurable]
    have := g68c_map_theta D theta hTRI (-t)
    rw [neg_neg] at this
    exact this
  have hlaw : reflectedLaw (entropyLaw D t) = (entropyLaw D t).withDensity g := by
    unfold reflectedLaw entropyLaw
    rw [Measure.map_map measurable_neg hSig]
    rw [show ((fun s : ℝ => -s) ∘ meanEntropy D t) = fun x => -meanEntropy D t x from rfl]
    rw [← Measure.map_congr hsym]
    rw [show (fun x => meanEntropy D t (theta (D.flow t x))) =
      meanEntropy D t ∘ (fun x => theta (D.flow t x)) from rfl, ← Measure.map_map hSig hψ]
    rw [hmψ, ← g68c_back D t]
    ext B hB
    rw [Measure.map_apply hSig hB, withDensity_apply _ (hSig hB), withDensity_apply _ hB,
      setLIntegral_map hB hg hSig]
    refine setLIntegral_congr_fun (hSig hB) fun x _ => ?_
    simp only [hgdef, meanEntropy]
    congr 2
    field_simp
  haveI : IsProbabilityMeasure (entropyLaw D t) := Measure.isProbabilityMeasure_map hSig.aemeasurable
  refine ⟨?_, ?_, ?_⟩
  · rw [hlaw]; exact withDensity_absolutelyContinuous _ _
  · rw [hlaw]
    exact withDensity_absolutelyContinuous' hg.aemeasurable
      (ae_of_all _ fun s => by simp [hgdef, Real.exp_pos])
  · rw [hlaw]; exact Measure.rnDeriv_withDensity _ hg
