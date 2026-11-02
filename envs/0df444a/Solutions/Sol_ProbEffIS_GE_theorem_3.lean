-- Prove2me | solution 1 for ProbEffIS.GE.theorem_3
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-02T01:50:14.548241+00:00
-- url     : https://prove2.me/submissions/0fe9501e-0943-4807-b3b8-30402aa42e05

import Mathlib
import Definitions.Def_ProbEffIS_GE_Defs

open MeasureTheory Filter Topology ProbabilityTheory

namespace ProbEffIS.GE

/-- Chebyshev's inequality for the mean of `n` i.i.d. samples. -/
lemma cheb_sampleMean {Ω : Type*} [MeasurableSpace Ω] (Q : Measure Ω) [IsProbabilityMeasure Q]
    (n : ℕ) (hn : 1 ≤ n) (Z : Ω → ℝ) (hZ : MemLp Z 2 Q) (t : ℝ) (ht : 0 < t) :
    Measure.pi (fun _ : Fin n => Q) {ω | t ≤ |sampleMean n Z ω - ∫ x, Z x ∂Q|} ≤
      ENNReal.ofReal (variance Z Q / (n * t ^ 2)) := by
  set P := Measure.pi (fun _ : Fin n => Q)
  have hY : ∀ i : Fin n, MemLp (fun ω : Fin n → Ω => Z (ω i)) 2 P := fun i =>
    hZ.comp_measurePreserving (measurePreserving_eval (fun _ : Fin n => Q) i)
  have hsumL : MemLp (∑ i : Fin n, fun ω : Fin n → Ω => Z (ω i)) 2 P := memLp_finsetSum' _ (fun i _ => hY i)
  have hfun : (fun ω => sampleMean n Z ω) = fun ω => (n : ℝ)⁻¹ * (∑ i : Fin n, fun ω : Fin n → Ω => Z (ω i)) ω := by
    funext ω; simp [sampleMean, Finset.sum_apply]
  have hX : MemLp (fun ω => sampleMean n Z ω) 2 P := by
    rw [hfun]; exact hsumL.const_mul _
  have hint : ∀ i : Fin n, ∫ ω, Z (ω i) ∂P = ∫ x, Z x ∂Q := fun i => by
    have hm := (measurePreserving_eval (fun _ : Fin n => Q) i)
    conv_rhs => rw [← hm.map_eq]
    rw [integral_map (measurable_pi_apply i).aemeasurable (by rw [hm.map_eq]; exact hZ.1)]
  have hmean : ∫ ω, sampleMean n Z ω ∂P = ∫ x, Z x ∂Q := by
    simp only [sampleMean]
    rw [integral_const_mul, integral_finsetSum _ (fun i _ => (hY i).integrable one_le_two)]
    simp only [hint, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
    field_simp
  have hvar : variance (fun ω => sampleMean n Z ω) P = variance Z Q / n := by
    rw [hfun]
    have h1 : variance (fun ω => (n : ℝ)⁻¹ * (∑ i : Fin n, fun ω : Fin n → Ω => Z (ω i)) ω) P
        = ((n : ℝ)⁻¹) ^ 2 * variance (∑ i : Fin n, fun ω : Fin n → Ω => Z (ω i)) P := by
      have := variance_const_mul (μ := P) ((n : ℝ)⁻¹) (∑ i : Fin n, fun ω : Fin n → Ω => Z (ω i))
      simpa [Pi.mul_def] using this
    rw [h1, variance_sum_pi (μ := fun _ : Fin n => Q) (X := fun _ => Z) (fun _ => hZ)]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
    field_simp
  have hc := meas_ge_le_variance_div_sq hX ht
  rw [hmean, hvar] at hc
  convert hc using 2
  field_simp

lemma minRelDisc_nonneg {Ω : Type*} [MeasurableSpace Ω] (Q : Measure Ω) (n : ℕ) (Z : Ω → ℝ)
    (p ε : ℝ) : 0 ≤ minRelDisc Q n Z p ε :=
  Real.sInf_nonneg (fun _ h => h.1.le)

lemma minRelDisc_le {Ω : Type*} [MeasurableSpace Ω] (Q : Measure Ω) (n : ℕ) (Z : Ω → ℝ)
    (p ε δ₀ : ℝ) (hδ₀ : 0 ≤ δ₀)
    (h : ∀ δ, δ₀ < δ → Measure.pi (fun _ : Fin n => Q)
      {ω | δ * p < |sampleMean n Z ω - p|} ≤ ENNReal.ofReal ε) :
    minRelDisc Q n Z p ε ≤ δ₀ := by
  refine le_of_forall_gt_imp_ge_of_dense fun c hc => ?_
  exact csInf_le ⟨0, fun _ h => h.1.le⟩ ⟨by linarith, h c hc⟩



lemma lrOutput_integral {Ω : Type*} [MeasurableSpace Ω] (P Q : Measure Ω) [IsFiniteMeasure P]
    [IsFiniteMeasure Q] (A : Set Ω) (hA : MeasurableSet A) (hac : P.restrict A ≪ Q) :
    ∫ ω, lrOutput P Q A ω ∂Q = (P A).toReal := by
  have h1 : lrOutput P Q A =ᵐ[Q] fun ω => ((P.restrict A).rnDeriv Q ω).toReal := by
    filter_upwards [Measure.rnDeriv_restrict P Q hA] with ω hω
    rw [hω, lrOutput]
    by_cases h : ω ∈ A <;> simp [h]
  rw [integral_congr_ae h1, Measure.integral_toReal_rnDeriv hac]
  simp [measureReal_def]

lemma lrOutput_nonneg {Ω : Type*} [MeasurableSpace Ω] (P Q : Measure Ω) (A : Set Ω) (ω : Ω) :
    0 ≤ lrOutput P Q A ω := by
  unfold lrOutput
  by_cases h : ω ∈ A <;> simp [h]

end ProbEffIS.GE

open ProbEffIS.GE in
theorem solution {Ω : Type*} [MeasurableSpace Ω]
    (P Q : ℝ → Measure Ω) [∀ γ, IsProbabilityMeasure (P γ)]
    (hQ : ∀ᶠ γ in atTop, IsProbabilityMeasure (Q γ))
    (A₁ A₂ : ℝ → Set Ω)
    (hA₁ : ∀ γ, MeasurableSet (A₁ γ))
    (hA₂ : ∀ γ, MeasurableSet (A₂ γ))
    (hdisj : ∀ γ, Disjoint (A₁ γ) (A₂ γ))
    (hac : ∀ γ, (P γ).restrict (A₁ γ ∪ A₂ γ) ≪ Q γ)
    (hp : Tendsto (eventProb P (fun γ => A₁ γ ∪ A₂ γ)) atTop (𝓝 0))
    (c1 : Tendsto
      (fun γ => eventProb P A₁ γ / eventProb P (fun t => A₁ t ∪ A₂ t) γ)
      atTop (𝓝 1))
    (n : ℝ → ℕ) (hn : ∀ γ, 1 ≤ n γ)
    (hnsub : IsSubexpIn (fun γ => (n γ : ℝ))
      (fun γ => -Real.log (eventProb P (fun t => A₁ t ∪ A₂ t) γ)))
    (hL2 : ∀ᶠ γ in atTop, MemLp (eventOutput P Q A₁ γ) 2 (Q γ))
    (c2 : Tendsto
      (fun γ => variance (eventOutput P Q A₁ γ) (Q γ) /
        ((n γ : ℝ) * (eventProb P A₁ γ) ^ 2)) atTop (𝓝 0))
    (c3 : Tendsto
      (fun γ => (n γ : ℝ) * eventProb Q A₂ γ) atTop (𝓝 0)) :
    (∀ ε : ℝ, 0 < ε →
      (∀ᶠ γ in atTop,
        minRelDisc (Q γ) (n γ)
          (eventOutput P Q (fun t => A₁ t ∪ A₂ t) γ)
          (eventProb P (fun t => A₁ t ∪ A₂ t) γ) ε ≤
        Real.sqrt (variance (eventOutput P Q A₁ γ) (Q γ) /
          ((n γ : ℝ) * (eventProb P A₁ γ) ^ 2 *
            (ε - (n γ : ℝ) * eventProb Q A₂ γ))) +
          eventProb P A₂ γ / eventProb P (fun t => A₁ t ∪ A₂ t) γ) ∧
      Tendsto (fun γ =>
        Real.sqrt (variance (eventOutput P Q A₁ γ) (Q γ) /
          ((n γ : ℝ) * (eventProb P A₁ γ) ^ 2 *
            (ε - (n γ : ℝ) * eventProb Q A₂ γ))) +
          eventProb P A₂ γ / eventProb P (fun t => A₁ t ∪ A₂ t) γ)
        atTop (𝓝 0)) ∧
    StronglyProbEfficient Q
      (eventOutput P Q (fun t => A₁ t ∪ A₂ t))
      (eventProb P (fun t => A₁ t ∪ A₂ t)) := by
  -- abbreviations
  set p : ℝ → ℝ := eventProb P (fun t => A₁ t ∪ A₂ t) with hp_def
  set p₁ : ℝ → ℝ := eventProb P A₁ with hp₁_def
  set p₂ : ℝ → ℝ := eventProb P A₂ with hp₂_def
  set q₂ : ℝ → ℝ := eventProb Q A₂ with hq₂_def
  set V : ℝ → ℝ := fun γ => variance (eventOutput P Q A₁ γ) (Q γ) with hV_def
  have hpsum : ∀ γ, p γ = p₁ γ + p₂ γ := fun γ => by
    simp only [hp_def, hp₁_def, hp₂_def, eventProb]
    rw [measure_union (hdisj γ) (hA₂ γ), ENNReal.toReal_add (measure_ne_top _ _)
      (measure_ne_top _ _)]
  have hp0 : ∀ γ, 0 ≤ p γ := fun γ => ENNReal.toReal_nonneg
  have hp₁0 : ∀ γ, 0 ≤ p₁ γ := fun γ => ENNReal.toReal_nonneg
  have hp₂0 : ∀ γ, 0 ≤ p₂ γ := fun γ => ENNReal.toReal_nonneg
  have hev1 : ∀ᶠ γ in atTop, (1 / 2 : ℝ) < p₁ γ / p γ :=
    c1.eventually (lt_mem_nhds (by norm_num))
  have hppos : ∀ᶠ γ in atTop, 0 < p γ := by
    filter_upwards [hev1] with γ h
    rcases (hp0 γ).lt_or_eq with h' | h'
    · exact h'
    · rw [← h'] at h; simp at h; linarith
  have hp₁pos : ∀ᶠ γ in atTop, 0 < p₁ γ := by
    filter_upwards [hev1, hppos] with γ h hpp
    by_contra hc; push Not at hc
    have : p₁ γ / p γ ≤ 0 := div_nonpos_of_nonpos_of_nonneg hc hpp.le
    linarith
  -- p₂ / p → 0
  have hp₂p : Tendsto (fun γ => p₂ γ / p γ) atTop (𝓝 0) := by
    have : Tendsto (fun γ => 1 - p₁ γ / p γ) atTop (𝓝 0) := by
      simpa using (tendsto_const_nhds (x := (1:ℝ))).sub c1
    refine this.congr' ?_
    filter_upwards [hppos] with γ hpp
    rw [hpsum γ] at hpp ⊢
    field_simp
    ring
  -- the bound
  have part1 : ∀ ε : ℝ, 0 < ε → ∀ᶠ γ in atTop,
      minRelDisc (Q γ) (n γ) (eventOutput P Q (fun t => A₁ t ∪ A₂ t) γ) (p γ) ε ≤
        Real.sqrt (V γ / ((n γ : ℝ) * (p₁ γ) ^ 2 * (ε - (n γ : ℝ) * q₂ γ))) + p₂ γ / p γ := by
    intro ε hε
    have hq : ∀ᶠ γ in atTop, (n γ : ℝ) * q₂ γ < ε := c3.eventually (gt_mem_nhds hε)
    filter_upwards [hQ, hq, hppos, hp₁pos, hL2] with γ hQγ hqγ hpp hp₁p hL2γ
    apply minRelDisc_le _ _ _ _ _ _ (add_nonneg (Real.sqrt_nonneg _) (div_nonneg (hp₂0 γ) (hp0 γ)))
    intro δ hδ
    set Z := eventOutput P Q (fun t => A₁ t ∪ A₂ t) γ
    set Z₁ := eventOutput P Q A₁ γ
    set Z₂ := eventOutput P Q A₂ γ
    have hZ : ∀ x, Z x = Z₁ x + Z₂ x := fun x => by
      simp only [Z, Z₁, Z₂, eventOutput, lrOutput]
      exact congrFun (Set.indicator_union_of_disjoint (hdisj γ) _) x
    have hmeanZ : ∀ ω, sampleMean (n γ) Z ω = sampleMean (n γ) Z₁ ω + sampleMean (n γ) Z₂ ω := by
      intro ω; simp only [sampleMean, hZ, Finset.sum_add_distrib]; ring
    have hmean₂0 : ∀ ω, 0 ≤ sampleMean (n γ) Z₂ ω := fun ω => by
      unfold sampleMean
      exact mul_nonneg (by positivity) (Finset.sum_nonneg fun i _ => lrOutput_nonneg _ _ _ _)
    have hunb₁ : ∫ x, Z₁ x ∂(Q γ) = p₁ γ := by
      have hac₁ : (P γ).restrict (A₁ γ) ≪ Q γ :=
        (Measure.restrict_mono Set.subset_union_left le_rfl).absolutelyContinuous.trans (hac γ)
      exact lrOutput_integral _ _ _ (hA₁ γ) hac₁
    set s := Real.sqrt (V γ / ((n γ : ℝ) * (p₁ γ) ^ 2 * (ε - (n γ : ℝ) * q₂ γ)))
    set t := δ - p₂ γ / p γ
    have hts : s < t := by simp only [t]; linarith
    have hs0 : 0 ≤ s := Real.sqrt_nonneg _
    have ht0 : 0 < t := lt_of_le_of_lt hs0 hts
    have hp₁le : p₁ γ ≤ p γ := by rw [hpsum γ]; linarith [hp₂0 γ]
    -- event inclusion
    have hsub : {ω : Fin (n γ) → Ω | δ * p γ < |sampleMean (n γ) Z ω - p γ|} ⊆
        {ω | t * p₁ γ ≤ |sampleMean (n γ) Z₁ ω - ∫ x, Z₁ x ∂(Q γ)|} ∪
        ⋃ i : Fin (n γ), {ω | ω i ∈ A₂ γ} := by
      intro ω hω
      simp only [Set.mem_ofPred_eq] at hω
      by_contra hcon
      simp only [Set.mem_union, Set.mem_ofPred_eq, Set.mem_iUnion, not_or, not_exists, not_le] at hcon
      obtain ⟨h1, h2⟩ := hcon
      have hZ₂0 : sampleMean (n γ) Z₂ ω = 0 := by
        unfold sampleMean
        rw [Finset.sum_eq_zero fun i _ => ?_, mul_zero]
        simp [Z₂, eventOutput, lrOutput, h2 i]
      rw [hunb₁] at h1
      rw [hmeanZ, hZ₂0, add_zero, hpsum γ] at hω
      have : |sampleMean (n γ) Z₁ ω - (p₁ γ + p₂ γ)| ≤ |sampleMean (n γ) Z₁ ω - p₁ γ| + p₂ γ := by
        have := abs_sub (sampleMean (n γ) Z₁ ω - p₁ γ) (p₂ γ)
        rw [abs_of_nonneg (hp₂0 γ)] at this
        calc _ = |sampleMean (n γ) Z₁ ω - p₁ γ - p₂ γ| := by ring_nf
          _ ≤ _ := this
      have hδeq : δ * (p₁ γ + p₂ γ) = t * (p₁ γ + p₂ γ) + p₂ γ := by
        simp only [t]; rw [← hpsum γ]; field_simp; ring
      have : t * p₁ γ ≤ t * (p₁ γ + p₂ γ) := by nlinarith [hp₂0 γ]
      linarith
    refine (measure_mono hsub).trans ((measure_union_le _ _).trans ?_)
    have hcheb := cheb_sampleMean (Q γ) (n γ) (hn γ) Z₁ hL2γ (t * p₁ γ) (by positivity)
    have hunion : Measure.pi (fun _ : Fin (n γ) => Q γ) (⋃ i : Fin (n γ), {ω | ω i ∈ A₂ γ}) ≤
        ENNReal.ofReal ((n γ : ℝ) * q₂ γ) := by
      refine (measure_iUnion_le _).trans ?_
      have hi : ∀ i : Fin (n γ), Measure.pi (fun _ : Fin (n γ) => Q γ) {ω | ω i ∈ A₂ γ} = Q γ (A₂ γ) :=
        fun i => (measurePreserving_eval (fun _ : Fin (n γ) => Q γ) i).measure_preimage
          (hA₂ γ).nullMeasurableSet
      simp only [hi, tsum_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      rw [ENNReal.ofReal_mul (by positivity), hq₂_def, eventProb, ENNReal.ofReal_toReal (measure_ne_top _ _)]
      simp
    have hnq0 : 0 ≤ (n γ : ℝ) * q₂ γ := mul_nonneg (by positivity) ENNReal.toReal_nonneg
    calc _ ≤ ENNReal.ofReal (V γ / (n γ * (t * p₁ γ) ^ 2)) + ENNReal.ofReal ((n γ : ℝ) * q₂ γ) :=
          add_le_add hcheb hunion
      _ ≤ ENNReal.ofReal (ε - (n γ : ℝ) * q₂ γ) + ENNReal.ofReal ((n γ : ℝ) * q₂ γ) := by
          gcongr
          have hV0 : 0 ≤ V γ := variance_nonneg _ _
          have hn0 : (0:ℝ) < n γ := by exact_mod_cast hn γ
          have hd : 0 < (n γ : ℝ) * (p₁ γ) ^ 2 * (ε - (n γ : ℝ) * q₂ γ) := by
            have : 0 < ε - (n γ : ℝ) * q₂ γ := by linarith
            positivity
          have hs2 : s ^ 2 = V γ / ((n γ : ℝ) * (p₁ γ) ^ 2 * (ε - (n γ : ℝ) * q₂ γ)) :=
            Real.sq_sqrt (div_nonneg hV0 hd.le)
          have ht2 : s ^ 2 ≤ t ^ 2 := by nlinarith
          rw [hs2, div_le_iff₀ hd] at ht2
          rw [div_le_iff₀ (by positivity)]
          nlinarith [sq_nonneg (p₁ γ), sq_nonneg t]
      _ = ENNReal.ofReal ε := by
          rw [← ENNReal.ofReal_add (by linarith) hnq0]; ring_nf
  have part2 : ∀ ε : ℝ, 0 < ε → Tendsto (fun γ =>
      Real.sqrt (V γ / ((n γ : ℝ) * (p₁ γ) ^ 2 * (ε - (n γ : ℝ) * q₂ γ))) + p₂ γ / p γ)
      atTop (𝓝 0) := by
    intro ε hε
    have h1 : Tendsto (fun γ => V γ / ((n γ : ℝ) * (p₁ γ) ^ 2) / (ε - (n γ : ℝ) * q₂ γ))
        atTop (𝓝 0) := by
      have := c2.div ((tendsto_const_nhds (x := ε)).sub c3) (by simpa using hε.ne')
      simp only [sub_zero, zero_div] at this
      exact this
    have h2 : Tendsto (fun γ => Real.sqrt (V γ / ((n γ : ℝ) * (p₁ γ) ^ 2 * (ε - (n γ : ℝ) * q₂ γ))))
        atTop (𝓝 0) := by
      have := (Real.continuous_sqrt.tendsto 0).comp h1
      simp only [Real.sqrt_zero] at this
      refine this.congr fun γ => ?_
      simp [div_div]
    simpa using h2.add hp₂p
  refine ⟨fun ε hε => ⟨part1 ε hε, part2 ε hε⟩, hp, n, hn, hnsub, fun ε hε => ?_⟩
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds (part2 ε hε)
    (Eventually.of_forall fun γ => minRelDisc_nonneg _ _ _ _ _) (part1 ε hε)
