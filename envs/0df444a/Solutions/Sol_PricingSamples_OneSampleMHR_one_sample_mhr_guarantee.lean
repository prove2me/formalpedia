-- Prove2me | solution 1 for PricingSamples.OneSampleMHR.one_sample_mhr_guarantee
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-11T02:06:33.346624+00:00
-- url     : https://prove2.me/submissions/c8fb8d4c-0a63-48ca-859b-f6a8eaba186c

import Mathlib
import Definitions.Def_PricingSamples_OneSampleMHR_Setting

set_option autoImplicit false

-- ===== from d95b66c5.lean
/-! d95b66c5 library, layer 0 (measure plumbing). CHECKPOINT file: see d95b66c5.progress.md. -/

namespace PricingSamples.OneSampleMHR.Lib

open MeasureTheory PricingSamples.OneSampleMHR

lemma ccdf_nonneg (μ : Measure ℝ) (p : ℝ) : 0 ≤ ccdf μ p := ENNReal.toReal_nonneg

lemma ccdf_antitone (μ : Measure ℝ) [IsFiniteMeasure μ] : Antitone (ccdf μ) := by
  intro x y hxy
  exact ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono (Set.Ioi_subset_Ioi hxy))

lemma ccdf_le_one (μ : Measure ℝ) [IsProbabilityMeasure μ] (p : ℝ) : ccdf μ p ≤ 1 := by
  unfold ccdf
  have h : μ (Set.Ioi p) ≤ 1 := prob_le_one
  have h2 : (μ (Set.Ioi p)).toReal ≤ (1 : ENNReal).toReal :=
    ENNReal.toReal_mono ENNReal.one_ne_top h
  simpa using h2

lemma noAtoms_of_ac (μ : Measure ℝ) (hac : μ ≪ volume) (x : ℝ) : μ {x} = 0 :=
  hac (Real.volume_singleton)

/-- `F̄ = 1 - cdf` for a probability measure. -/
lemma ccdf_eq_one_sub_cdf (μ : Measure ℝ) [IsProbabilityMeasure μ] (p : ℝ) :
    ccdf μ p = 1 - ProbabilityTheory.cdf μ p := by
  unfold ccdf
  rw [ProbabilityTheory.cdf_eq_real, ← Set.compl_Iic, measureReal_def,
    prob_compl_eq_one_sub measurableSet_Iic, ENNReal.toReal_sub_of_le prob_le_one ENNReal.one_ne_top]
  simp

lemma ccdf_zero (μ : Measure ℝ) (hF : InFAlpha 1 μ) : ccdf μ 0 = 1 := by
  obtain ⟨⟨hP, hneg, -, -⟩, ⟨hac, -⟩⟩ := hF
  have hIic : μ (Set.Iic 0) = 0 := by
    rw [← Set.Iio_insert, Set.insert_eq]
    exact measure_union_null (noAtoms_of_ac μ hac 0) hneg
  unfold ccdf
  rw [← Set.compl_Iic, prob_compl_eq_one_sub measurableSet_Iic, hIic]
  simp

/-- With no atoms, the ccdf is continuous. -/
lemma ccdf_continuous (μ : Measure ℝ) [IsProbabilityMeasure μ] (hac : μ ≪ volume) :
    Continuous (ccdf μ) := by
  have hcdf : Continuous (fun x => ProbabilityTheory.cdf μ x) := by
    rw [continuous_iff_continuousAt]
    intro x
    have hmono : Monotone (ProbabilityTheory.cdf μ) := (ProbabilityTheory.cdf μ).mono
    rw [hmono.continuousAt_iff_leftLim_eq_rightLim, (ProbabilityTheory.cdf μ).rightLim_eq x]
    have hs := (ProbabilityTheory.cdf μ).measure_singleton x
    rw [ProbabilityTheory.measure_cdf, noAtoms_of_ac μ hac x] at hs
    have hle : Function.leftLim (ProbabilityTheory.cdf μ) x ≤ ProbabilityTheory.cdf μ x :=
      hmono.leftLim_le le_rfl
    have := (ENNReal.ofReal_eq_zero.mp hs.symm)
    linarith
  have : ccdf μ = fun x => 1 - ProbabilityTheory.cdf μ x := funext (ccdf_eq_one_sub_cdf μ)
  rw [this]
  exact continuous_const.sub hcdf

/-! Layer 1: Markov bound, tail decay, optimal price attained. -/

lemma ae_nonneg_of_InG (μ : Measure ℝ) (hG : InG μ) : 0 ≤ᵐ[μ] fun v : ℝ => v := by
  obtain ⟨-, hneg, -, -⟩ := hG
  rw [Filter.EventuallyLE, ae_iff]
  have : {a : ℝ | ¬ (0 : ℝ → ℝ) a ≤ a} = Set.Iio 0 := by
    ext x; simp [not_le]
  rw [this]; exact hneg

lemma mul_ccdf_le_tail (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hint : Integrable (fun v : ℝ => v) μ) (p : ℝ) :
    p * ccdf μ p ≤ ∫ v in Set.Ioi p, v ∂μ := by
  have h1 : ∫ v in Set.Ioi p, p ∂μ ≤ ∫ v in Set.Ioi p, v ∂μ :=
    setIntegral_mono_on (integrableOn_const (measure_ne_top _ _)) hint.integrableOn
      measurableSet_Ioi (fun x hx => le_of_lt hx)
  rw [setIntegral_const, smul_eq_mul, measureReal_def] at h1
  unfold ccdf; linarith

lemma tail_le_mono (μ : Measure ℝ) (hint : Integrable (fun v : ℝ => v) μ) {N p : ℝ}
    (hN : 0 ≤ N) (hNp : N ≤ p) :
    ∫ v in Set.Ioi p, v ∂μ ≤ ∫ v in Set.Ioi N, v ∂μ := by
  apply setIntegral_mono_set hint.integrableOn
  · exact ae_restrict_of_forall_mem measurableSet_Ioi (fun x hx => le_trans hN (le_of_lt hx))
  · exact (Set.Ioi_subset_Ioi hNp).eventuallyLE

lemma tail_small (μ : Measure ℝ) (hint : Integrable (fun v : ℝ => v) μ) {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, ∫ v in Set.Ioi (N : ℝ), v ∂μ < ε := by
  have hT := tendsto_setIntegral_of_antitone (μ := μ) (f := fun v : ℝ => v)
    (s := fun n : ℕ => Set.Ioi (n : ℝ)) (fun _ => measurableSet_Ioi)
    (fun m n hmn => Set.Ioi_subset_Ioi (by exact_mod_cast hmn)) ⟨0, hint.integrableOn⟩
  have hI : (⋂ n : ℕ, Set.Ioi (n : ℝ)) = ∅ := by
    ext x
    simp only [Set.mem_iInter, Set.mem_Ioi, Set.mem_empty_iff_false, iff_false, not_forall, not_lt]
    obtain ⟨n, hn⟩ := exists_nat_ge x
    exact ⟨n, hn⟩
  rw [hI, Measure.restrict_empty, integral_zero_measure] at hT
  exact (hT.eventually (gt_mem_nhds hε)).exists

/-- An optimal price exists and is positive. -/
lemma exists_optPrice (μ : Measure ℝ) (hF : InFAlpha 1 μ) :
    ∃ r, 0 < r ∧ IsOptPrice μ r := by
  have hF' := hF
  obtain ⟨⟨hP, hneg, hint, hpos⟩, ⟨hac, -⟩⟩ := hF'
  have hc := ccdf_continuous μ hac
  set f : ℝ → ℝ := fun p => p * ccdf μ p with hf
  have hfc : Continuous f := continuous_id.mul hc
  -- a point with positive revenue
  have h0 : ccdf μ 0 = 1 := ccdf_zero μ hF
  have hev : ∀ᶠ p in nhds (0 : ℝ), (1 : ℝ) / 2 < ccdf μ p :=
    hc.continuousAt.eventually (lt_mem_nhds (by rw [h0]; norm_num))
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.mp hev
  set p0 : ℝ := δ / 2
  have hp0 : 0 < p0 := by positivity
  have hfp0 : 0 < f p0 := by
    have : (1 : ℝ) / 2 < ccdf μ p0 := hball (by
      rw [Real.dist_eq, sub_zero, abs_of_pos hp0]; simp only [p0]; linarith)
    simp only [hf]; nlinarith
  obtain ⟨N, hN⟩ := tail_small μ hint hfp0
  set M : ℝ := max (N : ℝ) p0
  obtain ⟨r, hr, hmax⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := M)).exists_isMaxOn
    ⟨p0, ⟨hp0.le, le_max_right _ _⟩⟩ hfc.continuousOn
  have hfr : f p0 ≤ f r := hmax ⟨hp0.le, le_max_right _ _⟩
  have hmaxAll : IsMaxOn f (Set.Ici 0) r := by
    intro p hp
    show f p ≤ f r
    by_cases hpM : p ≤ M
    · exact hmax ⟨hp, hpM⟩
    · replace hpM := lt_of_not_ge hpM
      have hNp : (N : ℝ) ≤ p := le_trans (le_max_left _ _) hpM.le
      have := mul_ccdf_le_tail μ hint p
      have := tail_le_mono μ hint (Nat.cast_nonneg N) hNp
      simp only [hf] at hfr ⊢
      linarith
  refine ⟨r, ?_, hr.1, hmaxAll⟩
  rcases hr.1.lt_or_eq with h | h
  · exact h
  · exfalso
    have : f r = 0 := by simp [hf, ← h]
    linarith

lemma opt_eq_of_IsOptPrice (μ : Measure ℝ) {r : ℝ} (hr : IsOptPrice μ r) :
    opt μ = r * ccdf μ r := by
  unfold opt
  apply IsGreatest.csSup_eq
  refine ⟨⟨r, hr.1, rfl⟩, ?_⟩
  rintro _ ⟨p, hp, rfl⟩
  exact hr.2 hp

/-! Layer 2: pointwise convexity bounds for `H = -log F̄` (abstract `f` = ccdf). -/

lemma H_le_chord0 (f : ℝ → ℝ) (hconv : ConvexOn ℝ {v : ℝ | 0 ≤ v ∧ 0 < f v} (fun v => -Real.log (f v)))
    (h0 : f 0 = 1) (h1 : 0 < f 1) {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    -Real.log (f x) ≤ x * -Real.log (f 1) := by
  have hm0 : (0 : ℝ) ∈ {v : ℝ | 0 ≤ v ∧ 0 < f v} := ⟨le_rfl, by rw [h0]; norm_num⟩
  have hm1 : (1 : ℝ) ∈ {v : ℝ | 0 ≤ v ∧ 0 < f v} := ⟨zero_le_one, h1⟩
  have := hconv.2 hm0 hm1 (sub_nonneg.mpr hx1) hx0 (by ring)
  simp only [smul_eq_mul, mul_zero, zero_add, mul_one, h0, Real.log_one, neg_zero] at this
  linarith

lemma H_le_chord1 (f : ℝ → ℝ) (hconv : ConvexOn ℝ {v : ℝ | 0 ≤ v ∧ 0 < f v} (fun v => -Real.log (f v)))
    (h1 : 0 < f 1) {x s : ℝ} (hx : 1 ≤ x) (hxs : x ≤ s) (hs1 : 1 < s) (hs : 0 < f s) :
    -Real.log (f x) ≤ (s - x) / (s - 1) * -Real.log (f 1) + (x - 1) / (s - 1) * -Real.log (f s) := by
  have hm1 : (1 : ℝ) ∈ {v : ℝ | 0 ≤ v ∧ 0 < f v} := ⟨zero_le_one, h1⟩
  have hms : s ∈ {v : ℝ | 0 ≤ v ∧ 0 < f v} := ⟨by linarith, hs⟩
  have hd : 0 < s - 1 := by linarith
  have ha : 0 ≤ (s - x) / (s - 1) := div_nonneg (by linarith) hd.le
  have hb : 0 ≤ (x - 1) / (s - 1) := div_nonneg (by linarith) hd.le
  have hab : (s - x) / (s - 1) + (x - 1) / (s - 1) = 1 := by field_simp; ring
  have key := hconv.2 hm1 hms ha hb hab
  have hx' : ((s - x) / (s - 1)) • (1 : ℝ) + ((x - 1) / (s - 1)) • s = x := by
    have hne : s - 1 ≠ 0 := hd.ne'
    rw [smul_eq_mul, smul_eq_mul]; field_simp; ring
  rw [hx'] at key
  simpa only [smul_eq_mul] using key

/-! Layer 3 (session 3): probability integral transform `F̄(V) ~ U[0,1]`. -/

lemma ccdf_measurable (μ : Measure ℝ) [IsFiniteMeasure μ] : Measurable (ccdf μ) :=
  (ccdf_antitone μ).measurable

lemma ccdf_tendsto_zero (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    Filter.Tendsto (ccdf μ) Filter.atTop (nhds 0) := by
  have h := ProbabilityTheory.tendsto_cdf_atTop μ
  have : ccdf μ = fun x => 1 - ProbabilityTheory.cdf μ x := funext (ccdf_eq_one_sub_cdf μ)
  rw [this]
  simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub h

/-- Level sets: `μ {F̄ ≤ q} = q` for `0 ≤ q < 1`. -/
lemma measure_ccdf_le (μ : Measure ℝ) [IsProbabilityMeasure μ] (hac : μ ≪ volume)
    (h0 : ccdf μ 0 = 1) {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) :
    μ {v | ccdf μ v ≤ q} = ENNReal.ofReal q := by
  haveI : NullSingletonClass μ := ⟨fun x => noAtoms_of_ac μ hac x⟩
  have hc := ccdf_continuous μ hac
  set A : Set ℝ := {v | ccdf μ v ≤ q} with hA
  rcases A.eq_empty_or_nonempty with hE | hne
  · rw [hE, measure_empty]
    rcases hq0.lt_or_eq with hq | hq
    · exfalso
      obtain ⟨v, hv⟩ := ((ccdf_tendsto_zero μ).eventually (ge_mem_nhds hq)).exists
      have : v ∈ A := hv
      rw [hE] at this; exact this
    · rw [← hq]; simp
  · have hbdd : BddBelow A := by
      refine ⟨0, fun v hv => ?_⟩
      by_contra hlt; push_neg at hlt
      have : ccdf μ 0 ≤ ccdf μ v := ccdf_antitone μ hlt.le
      have hv' : ccdf μ v ≤ q := hv
      linarith
    have hcl : IsClosed A := isClosed_le hc continuous_const
    set x := sInf A with hx
    have hxA : x ∈ A := hcl.csInf_mem hne hbdd
    have hAeq : A = Set.Ici x := by
      ext v; constructor
      · intro hv; exact csInf_le hbdd hv
      · intro hv; exact le_trans (ccdf_antitone μ hv) hxA
    have hFx : ccdf μ x = q := by
      refine le_antisymm hxA ?_
      by_contra hlt; push_neg at hlt
      have hev : ∀ᶠ y in nhds x, ccdf μ y < q := hc.continuousAt.eventually (gt_mem_nhds hlt)
      obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.mp hev
      have hy : ccdf μ (x - δ / 2) < q := hball (by
        rw [Real.dist_eq, abs_lt]; constructor <;> linarith)
      have : x ≤ x - δ / 2 := csInf_le hbdd (show x - δ / 2 ∈ A from hy.le)
      linarith
    rw [hAeq, ← measure_congr (Ioi_ae_eq_Ici (μ := μ) (a := x)), ← hFx]
    unfold ccdf
    rw [ENNReal.ofReal_toReal (measure_ne_top _ _)]

/-- PIT: the law of `F̄(V)` is uniform on `[0,1]`. -/
lemma map_ccdf_eq (μ : Measure ℝ) [IsProbabilityMeasure μ] (hac : μ ≪ volume)
    (h0 : ccdf μ 0 = 1) :
    μ.map (ccdf μ) = volume.restrict (Set.Icc (0 : ℝ) 1) := by
  haveI : IsFiniteMeasure (volume.restrict (Set.Icc (0 : ℝ) 1)) :=
    isFiniteMeasure_restrict.2 (by simp)
  refine Measure.ext_of_Iic _ _ (fun q => ?_)
  rw [Measure.map_apply (ccdf_measurable μ) measurableSet_Iic,
    Measure.restrict_apply measurableSet_Iic]
  rcases lt_or_ge q 0 with hq | hq
  · have h1 : ccdf μ ⁻¹' Set.Iic q = ∅ := by
      ext v; simp only [Set.mem_preimage, Set.mem_Iic, Set.mem_empty_iff_false, iff_false, not_le]
      exact lt_of_lt_of_le hq (ccdf_nonneg μ v)
    have h2 : Set.Iic q ∩ Set.Icc (0 : ℝ) 1 = ∅ := by
      ext v; simp only [Set.mem_inter_iff, Set.mem_Iic, Set.mem_Icc, Set.mem_empty_iff_false,
        iff_false, not_and, not_le]
      intro h1 h2; linarith
    rw [h1, h2, measure_empty, measure_empty]
  rcases lt_or_ge q 1 with hq1 | hq1
  · have h2 : Set.Iic q ∩ Set.Icc (0 : ℝ) 1 = Set.Icc 0 q := by
      ext v; simp only [Set.mem_inter_iff, Set.mem_Iic, Set.mem_Icc]
      constructor
      · rintro ⟨h1, h2, -⟩; exact ⟨h2, h1⟩
      · rintro ⟨h1, h2⟩; exact ⟨h2, h1, by linarith⟩
    rw [h2, Real.volume_Icc, sub_zero]
    exact measure_ccdf_le μ hac h0 hq hq1
  · have h1 : ccdf μ ⁻¹' Set.Iic q = Set.univ := by
      ext v; simp only [Set.mem_preimage, Set.mem_Iic, Set.mem_univ, iff_true]
      exact le_trans (ccdf_le_one μ v) hq1
    have h2 : Set.Iic q ∩ Set.Icc (0 : ℝ) 1 = Set.Icc 0 1 := by
      ext v; simp only [Set.mem_inter_iff, Set.mem_Iic, Set.mem_Icc]
      constructor
      · rintro ⟨-, h⟩; exact h
      · rintro ⟨h1, h2⟩; exact ⟨by linarith, h1, h2⟩
    rw [h1, h2, measure_univ, Real.volume_Icc]; simp

/-- PIT in integral form: `∫ Ψ(F̄ v) dμ = ∫_{[0,1]} Ψ`. -/
lemma integral_comp_ccdf (μ : Measure ℝ) [IsProbabilityMeasure μ] (hac : μ ≪ volume)
    (h0 : ccdf μ 0 = 1) {Ψ : ℝ → ℝ} (hΨ : Measurable Ψ) :
    ∫ v, Ψ (ccdf μ v) ∂μ = ∫ q in Set.Icc (0 : ℝ) 1, Ψ q := by
  rw [← map_ccdf_eq μ hac h0,
    integral_map (ccdf_measurable μ).aemeasurable hΨ.aestronglyMeasurable]

/-- Lower-bound transfer: a pointwise bound `γ s F̄(γ s) ≥ Ψ(F̄ s)` integrates to `postRev`. -/
lemma postRev_ge_of_pointwise (μ : Measure ℝ) (hF : InFAlpha 1 μ) {γ : ℝ} (hγ : 0 ≤ γ)
    {Ψ : ℝ → ℝ} (hΨ : Measurable Ψ) {C : ℝ} (hC : ∀ q, |Ψ q| ≤ C)
    (hpt : ∀ s, 0 ≤ s → Ψ (ccdf μ s) ≤ γ * s * ccdf μ (γ * s)) :
    ∫ q in Set.Icc (0 : ℝ) 1, Ψ q ≤ postRev γ μ := by
  have hF0 := hF
  obtain ⟨⟨hP, hneg, hint, -⟩, ⟨hac, -⟩⟩ := hF0
  have h0 := ccdf_zero μ hF
  rw [← integral_comp_ccdf μ hac h0 hΨ]
  unfold postRev
  have hnn : 0 ≤ᵐ[μ] fun v : ℝ => v := ae_nonneg_of_InG μ hF.1
  have hint2 : Integrable (fun s => γ * s * ccdf μ (γ * s)) μ := by
    refine Integrable.mono' (hint.const_mul γ) ?_ ?_
    · exact ((measurable_const.mul measurable_id).mul
        ((ccdf_measurable μ).comp (measurable_const.mul measurable_id))).aestronglyMeasurable
    · filter_upwards [hnn] with s hs
      have hs' : (0 : ℝ) ≤ s := hs
      rw [Real.norm_eq_abs, abs_of_nonneg
        (mul_nonneg (mul_nonneg hγ hs') (ccdf_nonneg μ (γ * s)))]
      have := ccdf_le_one μ (γ * s)
      have : 0 ≤ γ * s := mul_nonneg hγ hs'
      nlinarith
  have hint1 : Integrable (fun v => Ψ (ccdf μ v)) μ :=
    Integrable.of_bound ((hΨ.comp (ccdf_measurable μ)).aestronglyMeasurable) C
      (Filter.Eventually.of_forall (fun v => by rw [Real.norm_eq_abs]; exact hC _))
  refine integral_mono_ae hint1 hint2 ?_
  filter_upwards [hnn] with s hs
  exact hpt s hs

end PricingSamples.OneSampleMHR.Lib

-- ===== from d95b66c5_exp.lean
/-! d95b66c5 reflective-certificate library: certified exp LOWER bounds in scaled integer
arithmetic, cheap for kernel `decide +kernel` (k squarings, no Taylor series).
Value convention: a natural/integer `v` stands for the real `v / 2^p`. -/

namespace PricingSamples.OneSampleMHR.Cert

/-- `(1 + x/m)^m ≤ exp x` for `x ≥ -m`. -/
lemma one_add_div_pow_le_exp (x : ℝ) (m : ℕ) (hm : 0 < m) (hx : -(m : ℝ) ≤ x) :
    (1 + x / m) ^ m ≤ Real.exp x := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have h0 : 0 ≤ 1 + x / m := by
    have : -1 ≤ x / m := by rw [le_div_iff₀ hm']; linarith
    linarith
  calc (1 + x / m) ^ m ≤ (Real.exp (x / m)) ^ m := by
        have := Real.add_one_le_exp (x / m)
        exact pow_le_pow_left₀ h0 (by linarith) m
    _ = Real.exp x := by
        rw [← Real.exp_nat_mul]; congr 1; field_simp

/-- `k` rounded-down squarings at scale `2^p`. -/
def sqIter (p : ℕ) : ℕ → ℕ → ℕ
  | 0, v => v
  | k + 1, v => sqIter p k (v * v / 2 ^ p)

lemma sqIter_le (p : ℕ) : ∀ (k v : ℕ) (y : ℝ), (v : ℝ) / 2 ^ p ≤ y →
    ((sqIter p k v : ℕ) : ℝ) / 2 ^ p ≤ y ^ (2 ^ k)
  | 0, v, y, h => by simpa [sqIter] using h
  | k + 1, v, y, h => by
    have h0 : (0 : ℝ) ≤ (v : ℝ) / 2 ^ p := by positivity
    have h1 : ((v * v / 2 ^ p : ℕ) : ℝ) / 2 ^ p ≤ y ^ 2 := by
      have hc := Nat.cast_div_le (α := ℝ) (m := v * v) (n := 2 ^ p)
      calc ((v * v / 2 ^ p : ℕ) : ℝ) / 2 ^ p
          ≤ ((v * v : ℕ) : ℝ) / ((2 ^ p : ℕ) : ℝ) / 2 ^ p := by gcongr
        _ = ((v : ℝ) / 2 ^ p) ^ 2 := by push_cast; ring
        _ ≤ y ^ 2 := by gcongr
    have h2 := sqIter_le p k _ _ h1
    simp only [sqIter]
    calc _ ≤ (y ^ 2) ^ (2 ^ k) := h2
      _ = y ^ (2 ^ (k + 1)) := by rw [← pow_mul, pow_succ, mul_comm]

/-- Certified lower bound for `exp (X / 2^p)`: `(1 + X/2^(p+k))^(2^k)`, rounded down. -/
def expLo (p k : ℕ) (X : ℤ) : ℕ := sqIter p k ((2 : ℤ) ^ p + X / 2 ^ k).toNat

lemma expLo_le (p k : ℕ) (X : ℤ) (hX : -(2 : ℤ) ^ (p + k) ≤ X) :
    ((expLo p k X : ℕ) : ℝ) / 2 ^ p ≤ Real.exp ((X : ℝ) / 2 ^ p) := by
  have hk : (0 : ℤ) < 2 ^ k := by positivity
  have hb : 0 ≤ (2 : ℤ) ^ p + X / 2 ^ k := by
    have : -(2 : ℤ) ^ p ≤ X / 2 ^ k := by
      rw [Int.le_ediv_iff_mul_le hk]; rw [pow_add] at hX; linarith
    linarith
  have hfl : ((X / 2 ^ k : ℤ) : ℝ) ≤ (X : ℝ) / 2 ^ k := by
    have h := Int.ediv_mul_le X (ne_of_gt hk)
    have hk' : (0 : ℝ) < 2 ^ k := by positivity
    rw [le_div_iff₀ hk']; exact_mod_cast h
  set y : ℝ := 1 + (X : ℝ) / 2 ^ p / ((2 ^ k : ℕ) : ℝ) with hy
  have hv : ((((2 : ℤ) ^ p + X / 2 ^ k).toNat : ℕ) : ℝ) / 2 ^ p ≤ y := by
    have : ((((2 : ℤ) ^ p + X / 2 ^ k).toNat : ℕ) : ℝ) = (((2 : ℤ) ^ p + X / 2 ^ k : ℤ) : ℝ) := by
      rw [← Int.cast_natCast, Int.toNat_of_nonneg hb]
    rw [this, hy]; push_cast
    have hp : (0 : ℝ) < 2 ^ p := by positivity
    rw [div_le_iff₀ hp]
    have : (X : ℝ) / 2 ^ p / 2 ^ k * 2 ^ p = (X : ℝ) / 2 ^ k := by field_simp
    nlinarith [this]
  have h1 := sqIter_le p k _ y hv
  have hm : -((2 ^ k : ℕ) : ℝ) ≤ (X : ℝ) / 2 ^ p := by
    have hXr : -((2 : ℝ) ^ (p + k)) ≤ (X : ℝ) := by exact_mod_cast hX
    have hp : (0 : ℝ) < 2 ^ p := by positivity
    rw [le_div_iff₀ hp]; push_cast; rw [pow_add] at hXr; linarith
  have h2 := one_add_div_pow_le_exp ((X : ℝ) / 2 ^ p) (2 ^ k) (by positivity) hm
  exact h1.trans h2

/-- Reflection smoke test: `exp (-1) ≥ 0.3678` by kernel evaluation. -/
example : (0.3678 : ℝ) ≤ Real.exp (-1) := by
  have h := expLo_le 60 20 (-(2 ^ 60)) (by norm_num)
  have hn : (3678 * 2 ^ 60 / 10000 + 1 : ℕ) ≤ expLo 60 20 (-(2 ^ 60)) := by decide +kernel
  have h' : (0.3678 : ℝ) * 2 ^ 60 ≤ ((3678 * 2 ^ 60 / 10000 + 1 : ℕ) : ℝ) := by norm_num
  have hc : (0.3678 : ℝ) * 2 ^ 60 ≤ (expLo 60 20 (-(2 ^ 60)) : ℝ) := h'.trans (by exact_mod_cast hn)
  have e : (((-(2 ^ 60) : ℤ)) : ℝ) / 2 ^ 60 = -1 := by norm_num
  rw [e] at h
  have hp : (0 : ℝ) < 2 ^ 60 := by positivity
  rw [div_le_iff₀ hp] at h
  exact le_of_mul_le_mul_right (hc.trans h) hp

end PricingSamples.OneSampleMHR.Cert

-- ===== from d95b66c5_pt.lean
/-! Session 5 (d95b66c5): real-analysis pieces for the closed-form certificate route. -/

namespace PricingSamples.OneSampleMHR.Pt

open Real MeasureTheory

/-- `z ↦ z e^{-bz}` is monotone on `[0, 1/b]`. -/
lemma mul_exp_neg_mono {b y x : ℝ} (hb : 0 ≤ b) (hy : 0 ≤ y) (hyx : y ≤ x) (hx : b * x ≤ 1) :
    y * exp (-(b * y)) ≤ x * exp (-(b * x)) := by
  have h1 : exp (-(b * x)) = exp (-(b * y)) * exp (-(b * (x - y))) := by
    rw [← Real.exp_add]; ring_nf
  have h2 : 1 - b * (x - y) ≤ exp (-(b * (x - y))) := by
    have := Real.add_one_le_exp (-(b * (x - y))); linarith
  have hE : 0 < exp (-(b * y)) := exp_pos _
  rw [h1]
  have hxy : y ≤ x * (1 - b * (x - y)) := by
    nlinarith [mul_nonneg (sub_nonneg.2 hyx) (sub_nonneg.2 hx)]
  calc y * exp (-(b * y)) ≤ x * (1 - b * (x - y)) * exp (-(b * y)) :=
        mul_le_mul_of_nonneg_right hxy hE.le
    _ ≤ x * exp (-(b * (x - y))) * exp (-(b * y)) := by
        apply mul_le_mul_of_nonneg_right _ hE.le
        exact mul_le_mul_of_nonneg_left h2 (le_trans hy hyx)
    _ = x * (exp (-(b * y)) * exp (-(b * (x - y)))) := by ring

/-- `a ↦ a e^{aw}` is monotone while `bw ≥ -1`. -/
lemma mul_exp_mono_param {w a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hbw : -1 ≤ b * w) :
    a * exp (a * w) ≤ b * exp (b * w) := by
  have h1 : exp (b * w) = exp (a * w) * exp ((b - a) * w) := by
    rw [← Real.exp_add]; congr 1; ring
  have h2 : 1 + (b - a) * w ≤ exp ((b - a) * w) := by
    have := Real.add_one_le_exp ((b - a) * w); linarith
  have hE : 0 < exp (a * w) := exp_pos _
  have hb : 0 ≤ b := le_trans ha hab
  have h3 : a ≤ b * (1 + (b - a) * w) := by
    nlinarith [mul_nonneg (sub_nonneg.2 hab) (show 0 ≤ 1 + b * w by linarith)]
  rw [h1]
  calc a * exp (a * w) ≤ b * (1 + (b - a) * w) * exp (a * w) :=
        mul_le_mul_of_nonneg_right h3 hE.le
    _ ≤ b * exp ((b - a) * w) * exp (a * w) := by
        apply mul_le_mul_of_nonneg_right _ hE.le
        exact mul_le_mul_of_nonneg_left h2 hb
    _ = b * (exp (a * w) * exp ((b - a) * w)) := by ring

/-- Substitution `q = A e^{-u}`. -/
lemma integral_sub_exp {A T : ℝ} (hA : 0 < A) {h : ℝ → ℝ}
    (hh : ContinuousOn h (Set.uIcc 0 T)) :
    ∫ q in (A * exp (-T))..A, h (-log (q / A)) = A * ∫ u in (0:ℝ)..T, h u * exp (-u) := by
  have hf : ∀ x ∈ Set.uIcc (0:ℝ) T,
      HasDerivAt (fun u => A * exp (-u)) (-(A * exp (-x))) x := by
    intro x _
    have := ((hasDerivAt_neg x).exp).const_mul A
    exact this.congr_deriv (by ring)
  have hf' : ContinuousOn (fun u => -(A * exp (-u))) (Set.uIcc (0:ℝ) T) := by fun_prop
  have hmaps : Set.MapsTo (fun q => -log (q / A))
      ((fun u => A * exp (-u)) '' Set.uIcc 0 T) (Set.uIcc 0 T) := by
    rintro _ ⟨u, hu, rfl⟩
    simp only
    rw [mul_div_cancel_left₀ _ hA.ne', Real.log_exp, neg_neg]; exact hu
  have hg : ContinuousOn (fun q => h (-log (q / A)))
      ((fun u => A * exp (-u)) '' Set.uIcc 0 T) := by
    refine hh.comp ?_ hmaps
    refine ContinuousOn.neg (ContinuousOn.log (continuousOn_id.div_const A) ?_)
    rintro _ ⟨u, -, rfl⟩
    exact (div_pos (mul_pos hA (exp_pos _)) hA).ne'
  have key : (∫ x in (0:ℝ)..T, h (-log (A * exp (-x) / A)) * -(A * exp (-x)))
      = ∫ x in (A * exp (-0))..(A * exp (-T)), h (-log (x / A)) :=
    intervalIntegral.integral_comp_mul_deriv' hf hf' hg
  rw [neg_zero, exp_zero, mul_one] at key
  have hL : (∫ x in (0:ℝ)..T, h (-log (A * exp (-x) / A)) * -(A * exp (-x)))
      = -(A * ∫ u in (0:ℝ)..T, h u * exp (-u)) := by
    rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_neg]
    refine intervalIntegral.integral_congr (fun x _ => ?_)
    rw [mul_div_cancel_left₀ _ hA.ne', Real.log_exp, neg_neg]; ring
  rw [hL] at key
  have hs := intervalIntegral.integral_symm (μ := volume) (f := fun q => h (-log (q / A))) (A * exp (-T)) A
  linarith

/-- Integral form of the `E` term: `E a = ∫_0^1 γ v a e^{a(1-(1+γ)v)} dv`. Monotone for `a ≤ 1/γ`. -/
noncomputable def Eint (γ a : ℝ) : ℝ :=
  ∫ v in (0:ℝ)..1, γ * v * (a * exp (a * (1 - (1 + γ) * v)))

lemma Eint_mono {γ a b : ℝ} (hγ : 0 ≤ γ) (ha : 0 ≤ a) (hab : a ≤ b) (hb : b * γ ≤ 1) :
    Eint γ a ≤ Eint γ b := by
  unfold Eint
  apply intervalIntegral.integral_mono_on zero_le_one
  · exact (by fun_prop : Continuous fun v : ℝ => γ * v * (a * exp (a * (1 - (1 + γ) * v)))).intervalIntegrable _ _
  · exact (by fun_prop : Continuous fun v : ℝ => γ * v * (b * exp (b * (1 - (1 + γ) * v)))).intervalIntegrable _ _
  intro v hv
  have hv0 : 0 ≤ γ * v := mul_nonneg hγ hv.1
  apply mul_le_mul_of_nonneg_left _ hv0
  apply mul_exp_mono_param ha hab
  have hb0 : 0 ≤ b := le_trans ha hab
  nlinarith [hv.2, mul_nonneg hb0 (sub_nonneg.2 hv.2), mul_nonneg (mul_nonneg hb0 hγ) (sub_nonneg.2 hv.2)]

/-- FTC: `∫_0^T (p+su)e^{-ku} du`. -/
lemma integral_lin_exp (p s k T : ℝ) (hk : k ≠ 0) :
    ∫ u in (0:ℝ)..T, (p + s * u) * exp (-k * u)
      = (k * p + s) / k ^ 2 - exp (-k * T) * (k * (p + s * T) + s) / k ^ 2 := by
  have hd : ∀ x ∈ Set.uIcc (0:ℝ) T,
      HasDerivAt (fun u => -1 * (exp (-k * u) * (k * (p + s * u) + s) / k ^ 2))
        ((p + s * x) * exp (-k * x)) x := by
    intro x _
    have h1 := ((hasDerivAt_id' x).const_mul (-k)).exp
    have h2 := ((((hasDerivAt_id' x).const_mul s).const_add p).const_mul k).add_const s
    have h3 := ((h1.mul h2).div_const (k ^ 2)).const_mul (-1)
    exact h3.congr_deriv (by field_simp; ring)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd
    ((by fun_prop : Continuous fun u : ℝ => (p + s * u) * exp (-k * u)).intervalIntegrable _ _)]
  simp only [mul_zero, exp_zero, add_zero, one_mul]
  ring

/-- Closed form of the `G1` term. -/
lemma G1_eq (γ a s T : ℝ) (hk : a * γ * s + 1 ≠ 0) :
    ∫ u in (0:ℝ)..T, γ * (1 + s * u) * exp (a * (1 - γ * (1 + s * u))) * exp (-u)
      = γ * exp (a * (1 - γ)) * (((a * γ * s + 1) * 1 + s) / (a * γ * s + 1) ^ 2
        - exp (-(a * γ * s + 1) * T) * ((a * γ * s + 1) * (1 + s * T) + s) / (a * γ * s + 1) ^ 2) := by
  have hpt : ∀ u : ℝ, γ * (1 + s * u) * exp (a * (1 - γ * (1 + s * u))) * exp (-u)
      = γ * exp (a * (1 - γ)) * ((1 + s * u) * exp (-(a * γ * s + 1) * u)) := by
    intro u
    have he : exp (a * (1 - γ * (1 + s * u))) * exp (-u)
        = exp (a * (1 - γ)) * exp (-(a * γ * s + 1) * u) := by
      rw [← exp_add, ← exp_add]; congr 1; ring
    calc γ * (1 + s * u) * exp (a * (1 - γ * (1 + s * u))) * exp (-u)
        = γ * (1 + s * u) * (exp (a * (1 - γ * (1 + s * u))) * exp (-u)) := by ring
      _ = _ := by rw [he]; ring
  simp_rw [hpt]
  rw [intervalIntegral.integral_const_mul, integral_lin_exp 1 s _ T hk]

/-- Closed form of `Eint`. -/
lemma Eint_eq (γ a : ℝ) (hB : (1 + γ) * a ≠ 0) :
    Eint γ a = γ * a * exp a * (((1 + γ) * a * 0 + 1) / ((1 + γ) * a) ^ 2
      - exp (-((1 + γ) * a) * 1) * ((1 + γ) * a * (0 + 1 * 1) + 1) / ((1 + γ) * a) ^ 2) := by
  unfold Eint
  have hpt : ∀ v : ℝ, γ * v * (a * exp (a * (1 - (1 + γ) * v)))
      = γ * a * exp a * ((0 + 1 * v) * exp (-((1 + γ) * a) * v)) := by
    intro v
    have he : exp (a * (1 - (1 + γ) * v)) = exp a * exp (-((1 + γ) * a) * v) := by
      rw [← exp_add]; congr 1; ring
    rw [he]; ring
  simp_rw [hpt]
  rw [intervalIntegral.integral_const_mul, integral_lin_exp 0 1 _ 1 hB]

/-! Pointwise bounds (abstract ccdf `f`). -/

lemma H_le_chord0 (f : ℝ → ℝ) (hconv : ConvexOn ℝ {v : ℝ | 0 ≤ v ∧ 0 < f v} (fun v => -Real.log (f v)))
    (h0 : f 0 = 1) (h1 : 0 < f 1) {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    -Real.log (f x) ≤ x * -Real.log (f 1) := by
  have hm0 : (0 : ℝ) ∈ {v : ℝ | 0 ≤ v ∧ 0 < f v} := ⟨le_rfl, by rw [h0]; norm_num⟩
  have hm1 : (1 : ℝ) ∈ {v : ℝ | 0 ≤ v ∧ 0 < f v} := ⟨zero_le_one, h1⟩
  have := hconv.2 hm0 hm1 (sub_nonneg.mpr hx1) hx0 (by ring)
  simp only [smul_eq_mul, mul_zero, zero_add, mul_one, h0, Real.log_one, neg_zero] at this
  linarith

/-- Region `γx ≤ 1`: `γ y e^{-aγy} ≤ γ x f(γx)` for `0 ≤ y ≤ x`. -/
lemma pt_mid (f : ℝ → ℝ) (hconv : ConvexOn ℝ {v : ℝ | 0 ≤ v ∧ 0 < f v} (fun v => -Real.log (f v)))
    (h0 : f 0 = 1) (h1 : 0 < f 1) (hanti : ∀ u v : ℝ, u ≤ v → f v ≤ f u)
    {a γ x y : ℝ} (ha : a = -Real.log (f 1)) (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hγ0 : 0 < γ)
    (hγx : γ * x ≤ 1) (hy0 : 0 ≤ y) (hyx : y ≤ x) :
    γ * y * exp (-(a * (γ * y))) ≤ γ * x * f (γ * x) := by
  have hx0 : 0 ≤ γ * x := mul_nonneg hγ0.le (le_trans hy0 hyx)
  have hf : 0 < f (γ * x) := lt_of_lt_of_le h1 (hanti _ _ hγx)
  have hc := H_le_chord0 f hconv h0 h1 hx0 hγx
  rw [← ha] at hc
  have he : exp (-(a * (γ * x))) ≤ f (γ * x) := by
    calc exp (-(a * (γ * x))) ≤ exp (Real.log (f (γ * x))) := exp_le_exp.2 (by linarith)
      _ = f (γ * x) := exp_log hf
  have hm := mul_exp_neg_mono (b := a) ha0 (mul_nonneg hγ0.le hy0)
    (mul_le_mul_of_nonneg_left hyx hγ0.le)
    (by nlinarith [mul_le_mul ha1 hγx hx0 zero_le_one])
  calc γ * y * exp (-(a * (γ * y))) ≤ γ * x * exp (-(a * (γ * x))) := hm
    _ ≤ γ * x * f (γ * x) := mul_le_mul_of_nonneg_left he hx0

/-- The `[A,1]` piece integrates to `e^{-a} · Eint γ a`. -/
lemma E_piece {γ a : ℝ} (hγ : 0 < γ) (ha : 0 < a) :
    ∫ q in (exp (-a))..1, γ * (-Real.log q / a) * exp (-(γ * -Real.log q))
      = exp (-a) * Eint γ a := by
  have h := integral_sub_exp (A := 1) (T := a) one_pos
    (h := fun u => γ * (u / a) * exp (-(γ * u))) (by fun_prop)
  simp only [one_mul, div_one] at h
  rw [h]
  have hk : (1 + γ) ≠ 0 := by linarith
  have hB : (1 + γ) * a ≠ 0 := mul_ne_zero hk ha.ne'
  have hpt : ∀ u : ℝ, γ * (u / a) * exp (-(γ * u)) * exp (-u)
      = γ / a * ((0 + 1 * u) * exp (-(1 + γ) * u)) := by
    intro u
    have he : exp (-(γ * u)) * exp (-u) = exp (-(1 + γ) * u) := by rw [← exp_add]; congr 1; ring
    calc γ * (u / a) * exp (-(γ * u)) * exp (-u) = γ * (u / a) * (exp (-(γ * u)) * exp (-u)) := by ring
      _ = _ := by rw [he]; ring
  simp_rw [hpt]
  rw [intervalIntegral.integral_const_mul, integral_lin_exp 0 1 _ a hk, Eint_eq γ a hB]
  have e1 : exp (-((1 + γ) * a) * 1) = exp (-(1 + γ) * a) := by congr 1; ring
  rw [e1, Real.exp_neg a]
  have hane : a ≠ 0 := ha.ne'
  have hX : exp a ≠ 0 := (exp_pos a).ne'
  generalize exp (-(1 + γ) * a) = E
  generalize exp a = X at hX ⊢
  field_simp
  ring

/-- The `(A e^{-T}, A)` piece integrates to `A · A · G1` (closed form). -/
lemma G1_piece {γ A a0 s0 T : ℝ} (hA : 0 < A) (hk : a0 * γ * s0 + 1 ≠ 0) :
    ∫ q in (A * exp (-T))..A,
        A * (γ * (1 + s0 * -Real.log (q / A)) * exp (a0 * (1 - γ * (1 + s0 * -Real.log (q / A)))))
      = A * (A * (γ * exp (a0 * (1 - γ)) * (((a0 * γ * s0 + 1) * 1 + s0) / (a0 * γ * s0 + 1) ^ 2
        - exp (-(a0 * γ * s0 + 1) * T) * ((a0 * γ * s0 + 1) * (1 + s0 * T) + s0)
          / (a0 * γ * s0 + 1) ^ 2))) := by
  rw [intervalIntegral.integral_const_mul,
    integral_sub_exp hA (h := fun u => γ * (1 + s0 * u) * exp (a0 * (1 - γ * (1 + s0 * u))))
      (by fun_prop), G1_eq γ a0 s0 T hk]

/-- Constant piece. -/
lemma const_piece (lo hi C : ℝ) : ∫ _ in lo..hi, C = (hi - lo) * C := by
  rw [intervalIntegral.integral_const, smul_eq_mul]

end PricingSamples.OneSampleMHR.Pt

-- ===== from d95b66c5_pt2.lean
/-! Session 6 (d95b66c5): a ≤ 1, τ ≥ c (σ ≤ 1), tail pointwise bound. Abstract scaled ccdf `f`. -/

namespace PricingSamples.OneSampleMHR.Pt2

open Real

lemma H_le_chord0 (f : ℝ → ℝ) (hconv : ConvexOn ℝ {v : ℝ | 0 ≤ v ∧ 0 < f v} (fun v => -Real.log (f v)))
    (h0 : f 0 = 1) (h1 : 0 < f 1) {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    -Real.log (f x) ≤ x * -Real.log (f 1) := by
  have hm0 : (0 : ℝ) ∈ {v : ℝ | 0 ≤ v ∧ 0 < f v} := ⟨le_rfl, by rw [h0]; norm_num⟩
  have hm1 : (1 : ℝ) ∈ {v : ℝ | 0 ≤ v ∧ 0 < f v} := ⟨zero_le_one, h1⟩
  have := hconv.2 hm0 hm1 (sub_nonneg.mpr hx1) hx0 (by ring)
  simp only [smul_eq_mul, mul_zero, zero_add, mul_one, h0, Real.log_one, neg_zero] at this
  linarith

lemma H_le_chord1 (f : ℝ → ℝ) (hconv : ConvexOn ℝ {v : ℝ | 0 ≤ v ∧ 0 < f v} (fun v => -Real.log (f v)))
    (h1 : 0 < f 1) {x s : ℝ} (hx : 1 ≤ x) (hxs : x ≤ s) (hs1 : 1 < s) (hs : 0 < f s) :
    -Real.log (f x) ≤ (s - x) / (s - 1) * -Real.log (f 1) + (x - 1) / (s - 1) * -Real.log (f s) := by
  have hm1 : (1 : ℝ) ∈ {v : ℝ | 0 ≤ v ∧ 0 < f v} := ⟨zero_le_one, h1⟩
  have hms : s ∈ {v : ℝ | 0 ≤ v ∧ 0 < f v} := ⟨by linarith, hs⟩
  have hd : 0 < s - 1 := by linarith
  have ha : 0 ≤ (s - x) / (s - 1) := div_nonneg (by linarith) hd.le
  have hb : 0 ≤ (x - 1) / (s - 1) := div_nonneg (by linarith) hd.le
  have hab : (s - x) / (s - 1) + (x - 1) / (s - 1) = 1 := by field_simp; ring
  have key := hconv.2 hm1 hms ha hb hab
  have hx' : ((s - x) / (s - 1)) • (1 : ℝ) + ((x - 1) / (s - 1)) • s = x := by
    have hne : s - 1 ≠ 0 := hd.ne'
    rw [smul_eq_mul, smul_eq_mul]; field_simp; ring
  rw [hx'] at key
  simpa only [smul_eq_mul] using key

/-- MHR + optimality of price 1: `a = -log f 1 ≤ 1`. -/
lemma a_le_one (f : ℝ → ℝ) (hconv : ConvexOn ℝ {v : ℝ | 0 ≤ v ∧ 0 < f v} (fun v => -Real.log (f v)))
    (h0 : f 0 = 1) (h1 : 0 < f 1) (hanti : ∀ u v : ℝ, u ≤ v → f v ≤ f u)
    (hopt : ∀ x : ℝ, 0 ≤ x → x * f x ≤ f 1) :
    -Real.log (f 1) ≤ 1 := by
  set a := -Real.log (f 1) with ha
  by_contra hlt
  push Not at hlt
  have hapos : 0 < a := by linarith
  set x := 1 / a with hx
  have hx0 : 0 < x := by positivity
  have hx1 : x ≤ 1 := by rw [hx, div_le_one hapos]; linarith
  have hc := H_le_chord0 f hconv h0 h1 hx0.le hx1
  rw [← ha] at hc
  have hxa : x * a = 1 := by rw [hx]; field_simp
  have hfx : 0 < f x := lt_of_lt_of_le h1 (hanti _ _ hx1)
  have he : exp (-1) ≤ f x := by
    calc exp (-1) ≤ exp (Real.log (f x)) := exp_le_exp.2 (by linarith)
      _ = f x := exp_log hfx
  have hf1 : f 1 = exp (-a) := by rw [ha, neg_neg, exp_log h1]
  have hop := hopt x hx0.le
  rw [hf1] at hop
  have h2 : x * exp (-1) ≤ exp (-a) := le_trans (mul_le_mul_of_nonneg_left he hx0.le) hop
  -- multiply by a: exp(-1) ≤ a exp(-a)
  have h3 : exp (-1) ≤ a * exp (-a) := by
    have := mul_le_mul_of_nonneg_left h2 hapos.le
    rw [← mul_assoc, mul_comm a x, hxa, one_mul] at this
    exact this
  have h4 : a < exp (a - 1) := by
    have := Real.add_one_lt_exp (show a - 1 ≠ 0 by linarith)
    linarith
  have h5 : exp (a - 1) * exp (-a) = exp (-1) := by rw [← exp_add]; congr 1; ring
  have hea : 0 < exp (-a) := exp_pos _
  nlinarith

/-- MHR + optimality of price 1: for `s > 1` with `f s > 0`, `s - 1 ≤ H s - H 1` (so σ = c/τ ≤ 1). -/
lemma tau_ge (f : ℝ → ℝ) (hconv : ConvexOn ℝ {v : ℝ | 0 ≤ v ∧ 0 < f v} (fun v => -Real.log (f v)))
    (h1 : 0 < f 1) (hanti : ∀ u v : ℝ, u ≤ v → f v ≤ f u)
    (hopt : ∀ x : ℝ, 0 ≤ x → x * f x ≤ f 1) {s : ℝ} (hs1 : 1 < s) (hs : 0 < f s) :
    s - 1 ≤ -Real.log (f s) - -Real.log (f 1) := by
  set a := -Real.log (f 1) with ha
  set b := -Real.log (f s) with hb
  set c := s - 1 with hc
  have hc0 : 0 < c := by rw [hc]; linarith
  have hτ0 : 0 ≤ b - a := by
    have := Real.log_le_log hs (hanti 1 s hs1.le)
    rw [ha, hb]; linarith
  by_contra hlt
  push Not at hlt
  set τ := b - a with hτ
  set ε := (c - τ) / (2 * (c + 1)) with hε
  have hε0 : 0 < ε := by rw [hε]; apply div_pos <;> linarith
  have hεc : ε ≤ c := by
    rw [hε, div_le_iff₀ (by linarith)]; nlinarith
  have hτε : τ * ε < c - τ := by
    have : τ * ε ≤ c * ε := mul_le_mul_of_nonneg_right hlt.le hε0.le
    have h2 : c * ε < c - τ := by
      rw [hε, mul_div_assoc']
      rw [div_lt_iff₀ (by linarith)]
      nlinarith
    linarith
  set x := 1 + ε with hx
  have hx1 : 1 ≤ x := by linarith
  have hxs : x ≤ s := by rw [hx]; linarith
  have hx0 : 0 < x := by linarith
  have hch := H_le_chord1 f hconv h1 hx1 hxs hs1 hs
  rw [← ha, ← hb] at hch
  have hch' : -Real.log (f x) ≤ a + ε * τ / c := by
    have : (s - x) / (s - 1) * a + (x - 1) / (s - 1) * b = a + ε * τ / c := by
      have hne : s - 1 ≠ 0 := by linarith
      rw [hx, hτ, hc]; field_simp; ring
    linarith
  have hfx : 0 < f x := lt_of_lt_of_le hs (hanti _ _ hxs)
  have hop := hopt x hx0.le
  have hlog : Real.log x + Real.log (f x) ≤ Real.log (f 1) := by
    rw [← Real.log_mul hx0.ne' hfx.ne']
    exact Real.log_le_log (mul_pos hx0 hfx) hop
  have hl1 : 1 - x⁻¹ ≤ Real.log x := Real.one_sub_inv_le_log_of_pos hx0
  have hl2 : 1 - x⁻¹ = ε / x := by rw [hx]; field_simp; ring
  have key : ε / x ≤ ε * τ / c := by linarith
  rw [div_le_div_iff₀ hx0 hc0] at key
  have : c ≤ τ * x := by
    have h3 : ε * c ≤ ε * (τ * x) := by linarith
    exact le_of_mul_le_mul_left h3 hε0
  rw [hx] at this
  nlinarith

/-- Tail region `γ x ≥ 1`, `x > 1`: chord through `1` and `x`. -/
lemma pt_tail (f : ℝ → ℝ) (hconv : ConvexOn ℝ {v : ℝ | 0 ≤ v ∧ 0 < f v} (fun v => -Real.log (f v)))
    (h1 : 0 < f 1) (hanti : ∀ u v : ℝ, u ≤ v → f v ≤ f u) {γ x : ℝ} (hγ1 : γ ≤ 1)
    (hx1 : 1 < x) (hγx : 1 ≤ γ * x) (hfx : 0 < f x) :
    γ * x * (exp (-(-Real.log (f 1))) *
      exp (-((γ * x - 1) / (x - 1) * (-Real.log (f x) - -Real.log (f 1)))))
      ≤ γ * x * f (γ * x) := by
  have hx0 : 0 < x := by linarith
  have hγxx : γ * x ≤ x := by nlinarith
  have hch := H_le_chord1 f hconv h1 hγx hγxx hx1 hfx
  have hfg : 0 < f (γ * x) := lt_of_lt_of_le hfx (hanti _ _ hγxx)
  have hd : 0 < x - 1 := by linarith
  have heq : (x - γ * x) / (x - 1) * -Real.log (f 1) + (γ * x - 1) / (x - 1) * -Real.log (f x)
      = -Real.log (f 1) + (γ * x - 1) / (x - 1) * (-Real.log (f x) - -Real.log (f 1)) := by
    field_simp; ring
  rw [heq] at hch
  apply mul_le_mul_of_nonneg_left _ (by linarith)
  rw [← exp_add]
  calc exp (-(-Real.log (f 1)) + -((γ * x - 1) / (x - 1) * (-Real.log (f x) - -Real.log (f 1))))
      ≤ exp (Real.log (f (γ * x))) := exp_le_exp.2 (by linarith)
    _ = f (γ * x) := exp_log hfg

/-- `z ↦ z e^{-bz}` is monotone on `[0, 1/b]`. -/
lemma mul_exp_neg_mono {b y x : ℝ} (hb : 0 ≤ b) (hy : 0 ≤ y) (hyx : y ≤ x) (hx : b * x ≤ 1) :
    y * exp (-(b * y)) ≤ x * exp (-(b * x)) := by
  have h1 : exp (-(b * x)) = exp (-(b * y)) * exp (-(b * (x - y))) := by
    rw [← Real.exp_add]; ring_nf
  have h2 : 1 - b * (x - y) ≤ exp (-(b * (x - y))) := by
    have := Real.add_one_le_exp (-(b * (x - y))); linarith
  have hE : 0 < exp (-(b * y)) := exp_pos _
  rw [h1]
  have hxy : y ≤ x * (1 - b * (x - y)) := by
    nlinarith [mul_nonneg (sub_nonneg.2 hyx) (sub_nonneg.2 hx)]
  calc y * exp (-(b * y)) ≤ x * (1 - b * (x - y)) * exp (-(b * y)) :=
        mul_le_mul_of_nonneg_right hxy hE.le
    _ ≤ x * exp (-(b * (x - y))) * exp (-(b * y)) := by
        apply mul_le_mul_of_nonneg_right _ hE.le
        exact mul_le_mul_of_nonneg_left h2 (le_trans hy hyx)
    _ = x * (exp (-(b * y)) * exp (-(b * (x - y)))) := by ring

/-- Region `γx ≤ 1`: `γ y e^{-aγy} ≤ γ x f(γx)` for `0 ≤ y ≤ x`. -/
lemma pt_mid (f : ℝ → ℝ) (hconv : ConvexOn ℝ {v : ℝ | 0 ≤ v ∧ 0 < f v} (fun v => -Real.log (f v)))
    (h0 : f 0 = 1) (h1 : 0 < f 1) (hanti : ∀ u v : ℝ, u ≤ v → f v ≤ f u)
    {a γ x y : ℝ} (ha : a = -Real.log (f 1)) (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hγ0 : 0 < γ)
    (hγx : γ * x ≤ 1) (hy0 : 0 ≤ y) (hyx : y ≤ x) :
    γ * y * exp (-(a * (γ * y))) ≤ γ * x * f (γ * x) := by
  have hx0 : 0 ≤ γ * x := mul_nonneg hγ0.le (le_trans hy0 hyx)
  have hf : 0 < f (γ * x) := lt_of_lt_of_le h1 (hanti _ _ hγx)
  have hc := H_le_chord0 f hconv h0 h1 hx0 hγx
  rw [← ha] at hc
  have he : exp (-(a * (γ * x))) ≤ f (γ * x) := by
    calc exp (-(a * (γ * x))) ≤ exp (Real.log (f (γ * x))) := exp_le_exp.2 (by linarith)
      _ = f (γ * x) := exp_log hf
  have hm := mul_exp_neg_mono (b := a) ha0 (mul_nonneg hγ0.le hy0)
    (mul_le_mul_of_nonneg_left hyx hγ0.le)
    (by nlinarith [mul_le_mul ha1 hγx hx0 zero_le_one])
  calc γ * y * exp (-(a * (γ * y))) ≤ γ * x * exp (-(a * (γ * x))) := hm
    _ ≤ γ * x * f (γ * x) := mul_le_mul_of_nonneg_left he hx0

/-! Session 6: pointwise bounds for the four pieces of Ψ. -/

lemma u_eq {f : ℝ → ℝ} {x : ℝ} (hfx : 0 < f x) (h1 : 0 < f 1) :
    -Real.log (f x / f 1) = -Real.log (f x) - -Real.log (f 1) := by
  rw [Real.log_div hfx.ne' h1.ne']; ring

lemma mid_val (f : ℝ → ℝ) (h1 : 0 < f 1) {a0 γ y : ℝ} (ha0 : a0 ≤ -Real.log (f 1))
    (hy : 0 ≤ γ * y) (hγy : γ * y ≤ 1) :
    f 1 * (γ * y * exp (a0 * (1 - γ * y))) ≤ γ * y * exp (-(-Real.log (f 1) * (γ * y))) := by
  have hf1 : f 1 = exp (-(-Real.log (f 1))) := by rw [neg_neg, exp_log h1]
  have e : f 1 * (γ * y * exp (a0 * (1 - γ * y)))
      = γ * y * exp (-(-Real.log (f 1)) + a0 * (1 - γ * y)) := by
    rw [exp_add, ← hf1]; ring
  rw [e]
  apply mul_le_mul_of_nonneg_left _ hy
  apply exp_le_exp.2
  nlinarith [mul_nonneg (sub_nonneg.2 ha0) (sub_nonneg.2 hγy)]

lemma slope_bound (f : ℝ → ℝ) (hconv : ConvexOn ℝ {v : ℝ | 0 ≤ v ∧ 0 < f v} (fun v => -Real.log (f v)))
    (h1 : 0 < f 1) {L x s0 : ℝ} (hL : 1 < L) (hfL : 0 < f L) (hx1 : 1 ≤ x) (hxL : x ≤ L)
    (hs0 : 0 ≤ s0) (hsD : s0 * (-Real.log (f L) - -Real.log (f 1)) ≤ L - 1) :
    s0 * (-Real.log (f x) - -Real.log (f 1)) ≤ x - 1 := by
  have hch := H_le_chord1 f hconv h1 hx1 hxL hL hfL
  have hd : 0 < L - 1 := by linarith
  have e : (L - x) / (L - 1) * -Real.log (f 1) + (x - 1) / (L - 1) * -Real.log (f L)
      = -Real.log (f 1) + (x - 1) * (-Real.log (f L) - -Real.log (f 1)) / (L - 1) := by
    field_simp; ring
  rw [e] at hch
  have h2 : s0 * ((x - 1) * (-Real.log (f L) - -Real.log (f 1)) / (L - 1)) ≤ x - 1 := by
    rw [mul_div_assoc', div_le_iff₀ hd]
    nlinarith [mul_le_mul_of_nonneg_left hsD (sub_nonneg.2 hx1)]
  have h3 : s0 * (-Real.log (f x) - -Real.log (f 1))
      ≤ s0 * ((x - 1) * (-Real.log (f L) - -Real.log (f 1)) / (L - 1)) :=
    mul_le_mul_of_nonneg_left (by linarith) hs0
  linarith

/-- Piece `[A,1]`. -/
lemma pw_E (f : ℝ → ℝ) (hconv : ConvexOn ℝ {v : ℝ | 0 ≤ v ∧ 0 < f v} (fun v => -Real.log (f v)))
    (h0 : f 0 = 1) (h1 : 0 < f 1) (hanti : ∀ u v : ℝ, u ≤ v → f v ≤ f u)
    (hopt : ∀ x : ℝ, 0 ≤ x → x * f x ≤ f 1) (hnn : ∀ v, 0 ≤ f v)
    {γ x : ℝ} (hγ0 : 0 < γ) (hγ1 : γ ≤ 1) (hx : 0 ≤ x) (hA : f 1 ≤ f x) (hq1 : f x ≤ 1) :
    γ * (-Real.log (f x) / -Real.log (f 1)) * exp (-(γ * -Real.log (f x))) ≤ γ * x * f (γ * x) := by
  have hfx : 0 < f x := lt_of_lt_of_le h1 hA
  have hx1 : x ≤ 1 := by
    by_contra h; push Not at h
    have := hopt x hx
    nlinarith [mul_pos (sub_pos.2 h) hfx]
  have ha1 := a_le_one f hconv h0 h1 hanti hopt
  have ha0 : 0 ≤ -Real.log (f 1) := by
    have := Real.log_nonpos h1.le (le_trans hA hq1); linarith
  have ht0 : 0 ≤ -Real.log (f x) := by
    have := Real.log_nonpos hfx.le hq1; linarith
  have hR : 0 ≤ γ * x * f (γ * x) := mul_nonneg (mul_nonneg hγ0.le hx) (hnn _)
  have hc := H_le_chord0 f hconv h0 h1 hx hx1
  rcases eq_or_lt_of_le ha0 with h | hapos
  · rw [← h, div_zero, mul_zero, zero_mul]; exact hR
  · have hy0 : 0 ≤ -Real.log (f x) / -Real.log (f 1) := div_nonneg ht0 hapos.le
    have hyx : -Real.log (f x) / -Real.log (f 1) ≤ x := by rw [div_le_iff₀ hapos]; linarith
    have hγx : γ * x ≤ 1 := by nlinarith
    have hm := pt_mid f hconv h0 h1 hanti rfl ha0 ha1 hγ0 hγx hy0 hyx
    have hane : -Real.log (f 1) ≠ 0 := hapos.ne'
    have he : -Real.log (f 1) * (γ * (-Real.log (f x) / -Real.log (f 1))) = γ * -Real.log (f x) := by
      rw [show -Real.log (f 1) * (γ * (-Real.log (f x) / -Real.log (f 1)))
        = γ * (-Real.log (f x) / -Real.log (f 1) * -Real.log (f 1)) by ring, div_mul_cancel₀ _ hane]
    rw [he] at hm
    exact hm

/-- Piece `(A e^{-T}, A)`. -/
lemma pw_G1 (f : ℝ → ℝ) (hconv : ConvexOn ℝ {v : ℝ | 0 ≤ v ∧ 0 < f v} (fun v => -Real.log (f v)))
    (h0 : f 0 = 1) (h1 : 0 < f 1) (hanti : ∀ u v : ℝ, u ≤ v → f v ≤ f u)
    (hopt : ∀ x : ℝ, 0 ≤ x → x * f x ≤ f 1) (hnn : ∀ v, 0 ≤ f v)
    {γ x a0 s0 T : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1)
    (hlo : f 1 * exp (-T) < f x) (hhi : f x < f 1) (ha0 : a0 ≤ -Real.log (f 1)) (hs0 : 0 ≤ s0)
    (hσ : 0 < f (1 / γ) → s0 * (-Real.log (f (1 / γ)) - -Real.log (f 1)) ≤ 1 / γ - 1 ∧
      T ≤ -Real.log (f (1 / γ)) - -Real.log (f 1))
    (hσ0 : f (1 / γ) = 0 → s0 = 0) :
    f 1 * (γ * (1 + s0 * -Real.log (f x / f 1)) * exp (a0 * (1 - γ * (1 + s0 * -Real.log (f x / f 1)))))
      ≤ γ * x * f (γ * x) := by
  have hfx : 0 < f x := lt_of_lt_of_le (mul_pos h1 (exp_pos _)) hlo.le
  have hx1 : 1 < x := by
    by_contra h; push Not at h; have := hanti x 1 h; linarith
  rw [u_eq hfx h1]
  have ha1 := a_le_one f hconv h0 h1 hanti hopt
  have hlogA : Real.log (f 1 * exp (-T)) < Real.log (f x) :=
    Real.log_lt_log (mul_pos h1 (exp_pos _)) hlo
  rw [Real.log_mul h1.ne' (exp_pos _).ne', Real.log_exp] at hlogA
  have hu0 : 0 ≤ -Real.log (f x) - -Real.log (f 1) := by
    have := Real.log_le_log hfx hhi.le; linarith
  have ha0' : 0 ≤ -Real.log (f 1) := by
    have := Real.log_nonpos h1.le (by have := hanti 0 1 zero_le_one; rw [h0] at this; exact this)
    linarith
  have hL1 : 1 < 1 / γ := by rw [lt_div_iff₀ hγ0]; linarith
  have hγL : γ * (1 / γ) = 1 := by field_simp
  by_cases hxL : x ≤ 1 / γ
  · have hy : 1 + s0 * (-Real.log (f x) - -Real.log (f 1)) ≤ x := by
      by_cases hfL : 0 < f (1 / γ)
      · have := slope_bound f hconv h1 hL1 hfL hx1.le hxL hs0 (hσ hfL).1
        linarith
      · have : f (1 / γ) = 0 := le_antisymm (not_lt.1 hfL) (hnn _)
        rw [hσ0 this]; linarith
    have hy0 : 0 ≤ 1 + s0 * (-Real.log (f x) - -Real.log (f 1)) :=
      add_nonneg zero_le_one (mul_nonneg hs0 hu0)
    have hγx : γ * x ≤ 1 := by nlinarith [mul_le_mul_of_nonneg_left hxL hγ0.le]
    have hm := pt_mid f hconv h0 h1 hanti rfl ha0' ha1 hγ0 hγx hy0 hy
    exact le_trans (mid_val f h1 ha0 (mul_nonneg hγ0.le hy0)
      (by nlinarith [mul_le_mul_of_nonneg_left hy hγ0.le])) hm
  · push Not at hxL
    have hfL : 0 < f (1 / γ) := lt_of_lt_of_le hfx (hanti _ _ hxL.le)
    have hT := (hσ hfL).2
    have hb : -Real.log (f (1 / γ)) ≤ -Real.log (f x) := by
      have := Real.log_le_log hfx (hanti _ _ hxL.le); linarith
    linarith

/-- Tail region `x > 1/γ`: generic bound via `m ≤ inf_s γ s e^{-U μ(s)}`. -/
lemma pw_tailgen (f : ℝ → ℝ) (hconv : ConvexOn ℝ {v : ℝ | 0 ≤ v ∧ 0 < f v} (fun v => -Real.log (f v)))
    (h1 : 0 < f 1) (hanti : ∀ u v : ℝ, u ≤ v → f v ≤ f u) {γ x U m : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1)
    (hxL : 1 / γ < x) (hfx : 0 < f x) (hU : -Real.log (f x) - -Real.log (f 1) ≤ U)
    (hm : ∀ s, 1 / γ < s → m ≤ γ * s * exp (-(U * ((γ * s - 1) / (s - 1))))) :
    f 1 * m ≤ γ * x * f (γ * x) := by
  have hγx : 1 < γ * x := by rw [div_lt_iff₀ hγ0] at hxL; linarith
  have hx1 : 1 < x := by
    by_contra h; push Not at h; nlinarith [mul_le_mul_of_nonneg_left h hγ0.le]
  have ht := pt_tail f hconv h1 hanti hγ1.le hx1 hγx.le hfx
  have hμ0 : 0 ≤ (γ * x - 1) / (x - 1) := div_nonneg (by linarith) (by linarith)
  have hmx := hm x hxL
  have h2 : exp (-(U * ((γ * x - 1) / (x - 1))))
      ≤ exp (-((γ * x - 1) / (x - 1) * (-Real.log (f x) - -Real.log (f 1)))) :=
    exp_le_exp.2 (by nlinarith [mul_le_mul_of_nonneg_left hU hμ0])
  have hf1 : f 1 = exp (-(-Real.log (f 1))) := by rw [neg_neg, exp_log h1]
  calc f 1 * m ≤ f 1 * (γ * x * exp (-(U * ((γ * x - 1) / (x - 1))))) :=
        mul_le_mul_of_nonneg_left hmx h1.le
    _ ≤ f 1 * (γ * x * exp (-((γ * x - 1) / (x - 1) * (-Real.log (f x) - -Real.log (f 1))))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h2 (by linarith)) h1.le
    _ = γ * x * (exp (-(-Real.log (f 1))) *
          exp (-((γ * x - 1) / (x - 1) * (-Real.log (f x) - -Real.log (f 1))))) := by
        rw [← hf1]; ring
    _ ≤ γ * x * f (γ * x) := ht

/-- Piece `[A e^{-Th}, A e^{-T}]` (`s0 > 0`). -/
lemma pw_gap (f : ℝ → ℝ) (hconv : ConvexOn ℝ {v : ℝ | 0 ≤ v ∧ 0 < f v} (fun v => -Real.log (f v)))
    (h0 : f 0 = 1) (h1 : 0 < f 1) (hanti : ∀ u v : ℝ, u ≤ v → f v ≤ f u)
    (hopt : ∀ x : ℝ, 0 ≤ x → x * f x ≤ f 1) (hnn : ∀ v, 0 ≤ f v)
    {γ x a0 s0 T Th m : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1)
    (hlo : f 1 * exp (-Th) ≤ f x) (hhi : f x ≤ f 1 * exp (-T)) (hT : 0 < T)
    (ha0 : a0 ≤ -Real.log (f 1)) (hs0 : 0 < s0)
    (hσ : 0 < f (1 / γ) → s0 * (-Real.log (f (1 / γ)) - -Real.log (f 1)) ≤ 1 / γ - 1)
    (hσ0 : f (1 / γ) = 0 → s0 = 0)
    (hm : ∀ s, 1 / γ < s → m ≤ γ * s * exp (-(Th * ((γ * s - 1) / (s - 1))))) :
    f 1 * min (γ * min (1 + s0 * T) (1 / γ) * exp (a0 * (1 - γ * min (1 + s0 * T) (1 / γ)))) m
      ≤ γ * x * f (γ * x) := by
  have hfx : 0 < f x := lt_of_lt_of_le (mul_pos h1 (exp_pos _)) hlo
  have hlt1 : f x < f 1 := lt_of_le_of_lt hhi
    (mul_lt_of_lt_one_right h1 (by have := Real.exp_lt_exp.2 (show -T < 0 by linarith); rwa [Real.exp_zero] at this))
  have hx1 : 1 < x := by
    by_contra h; push Not at h; have := hanti x 1 h; linarith
  have hl1 : Real.log (f x) ≤ Real.log (f 1 * exp (-T)) := Real.log_le_log hfx hhi
  have hl2 : Real.log (f 1 * exp (-Th)) ≤ Real.log (f x) := Real.log_le_log (mul_pos h1 (exp_pos _)) hlo
  rw [Real.log_mul h1.ne' (exp_pos _).ne', Real.log_exp] at hl1 hl2
  have ha1 := a_le_one f hconv h0 h1 hanti hopt
  have ha0' : 0 ≤ -Real.log (f 1) := by
    have := Real.log_nonpos h1.le (by have := hanti 0 1 zero_le_one; rw [h0] at this; exact this)
    linarith
  have hL1 : 1 < 1 / γ := by rw [lt_div_iff₀ hγ0]; linarith
  have hγL : γ * (1 / γ) = 1 := by field_simp
  by_cases hxL : x ≤ 1 / γ
  · have hfL : 0 < f (1 / γ) := by
      by_contra hc
      have := hσ0 (le_antisymm (not_lt.1 hc) (hnn _)); linarith
    have sb := slope_bound f hconv h1 hL1 hfL hx1.le hxL hs0.le (hσ hfL)
    have hsT : s0 * T ≤ s0 * (-Real.log (f x) - -Real.log (f 1)) :=
      mul_le_mul_of_nonneg_left (by linarith) hs0.le
    have hy : min (1 + s0 * T) (1 / γ) ≤ x := le_trans (min_le_left _ _) (by linarith)
    have hy0 : 0 ≤ min (1 + s0 * T) (1 / γ) :=
      le_min (by nlinarith) (by linarith)
    have hγy : γ * min (1 + s0 * T) (1 / γ) ≤ 1 := by
      exact le_trans (mul_le_mul_of_nonneg_left (min_le_right _ _) hγ0.le) hγL.le
    have hγx : γ * x ≤ 1 := by nlinarith [mul_le_mul_of_nonneg_left hxL hγ0.le]
    calc _ ≤ f 1 * (γ * min (1 + s0 * T) (1 / γ) * exp (a0 * (1 - γ * min (1 + s0 * T) (1 / γ)))) :=
          mul_le_mul_of_nonneg_left (min_le_left _ _) h1.le
      _ ≤ _ := mid_val f h1 ha0 (mul_nonneg hγ0.le hy0) hγy
      _ ≤ _ := pt_mid f hconv h0 h1 hanti rfl ha0' ha1 hγ0 hγx hy0 hy
  · push Not at hxL
    calc _ ≤ f 1 * m := mul_le_mul_of_nonneg_left (min_le_right _ _) h1.le
      _ ≤ _ := pw_tailgen f hconv h1 hanti hγ0 hγ1 hxL hfx (by linarith) hm

/-- Piece `(0, A e^{-Th})` (`s0 > 0`, `Th ≥ c/s0`), with `u ≤ U`. -/
lemma pw_tail (f : ℝ → ℝ) (hconv : ConvexOn ℝ {v : ℝ | 0 ≤ v ∧ 0 < f v} (fun v => -Real.log (f v)))
    (h1 : 0 < f 1) (hanti : ∀ u v : ℝ, u ≤ v → f v ≤ f u) (hnn : ∀ v, 0 ≤ f v)
    {γ x s0 Th U m : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1)
    (hfx : 0 < f x) (hhi : f x < f 1 * exp (-Th)) (hs0 : 0 < s0) (hTh : 1 / γ - 1 ≤ s0 * Th)
    (hσ : 0 < f (1 / γ) → s0 * (-Real.log (f (1 / γ)) - -Real.log (f 1)) ≤ 1 / γ - 1)
    (hσ0 : f (1 / γ) = 0 → s0 = 0) (hU : -Real.log (f x / f 1) ≤ U)
    (hm : ∀ s, 1 / γ < s → m ≤ γ * s * exp (-(U * ((γ * s - 1) / (s - 1))))) :
    f 1 * m ≤ γ * x * f (γ * x) := by
  rw [u_eq hfx h1] at hU
  have hfL : 0 < f (1 / γ) := by
    by_contra hc
    have := hσ0 (le_antisymm (not_lt.1 hc) (hnn _)); linarith
  have hl1 : Real.log (f x) < Real.log (f 1 * exp (-Th)) := Real.log_lt_log hfx hhi
  rw [Real.log_mul h1.ne' (exp_pos _).ne', Real.log_exp] at hl1
  have hxL : 1 / γ < x := by
    by_contra h; push Not at h
    have hb : -Real.log (f x) ≤ -Real.log (f (1 / γ)) := by
      have := Real.log_le_log hfL (hanti _ _ h); linarith
    have h3 : s0 * (-Real.log (f x) - -Real.log (f 1)) ≤ s0 * Th := by
      have := hσ hfL
      nlinarith [mul_le_mul_of_nonneg_left hb hs0.le]
    have h4 := le_of_mul_le_mul_left h3 hs0
    linarith
  exact pw_tailgen f hconv h1 hanti hγ0 hγ1 hxL hfx hU hm

/-- The step-certificate integrand (pieces in `q`; `A = f 1`, `u = -log (q/A)`). -/
noncomputable def PsiF (γ A a0 s0 T Th : ℝ) (M : ℝ → ℝ) (q : ℝ) : ℝ :=
  if A ≤ q then (if q ≤ 1 then γ * (-Real.log q / -Real.log A) * exp (-(γ * -Real.log q)) else 0)
  else if A * exp (-T) < q then
    A * (γ * (1 + s0 * -Real.log (q / A)) * exp (a0 * (1 - γ * (1 + s0 * -Real.log (q / A)))))
  else if 0 < s0 ∧ A * exp (-Th) ≤ q then
    A * min (γ * min (1 + s0 * T) (1 / γ) * exp (a0 * (1 - γ * min (1 + s0 * T) (1 / γ)))) (M Th)
  else if 0 < s0 ∧ 0 < q then A * M (-Real.log (q / A))
  else 0

/-- Pointwise: `Ψ(f x) ≤ γ x f(γ x)` for every `x ≥ 0`, given the cell constraints. -/
lemma pw_all (f : ℝ → ℝ) (hconv : ConvexOn ℝ {v : ℝ | 0 ≤ v ∧ 0 < f v} (fun v => -Real.log (f v)))
    (h0 : f 0 = 1) (h1 : 0 < f 1) (hanti : ∀ u v : ℝ, u ≤ v → f v ≤ f u)
    (hopt : ∀ x : ℝ, 0 ≤ x → x * f x ≤ f 1) (hnn : ∀ v, 0 ≤ f v)
    {γ a0 s0 T Th : ℝ} {M : ℝ → ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1) (hT : 0 < T)
    (ha0 : a0 ≤ -Real.log (f 1)) (hs0 : 0 ≤ s0)
    (hσ : 0 < f (1 / γ) → s0 * (-Real.log (f (1 / γ)) - -Real.log (f 1)) ≤ 1 / γ - 1 ∧
      T ≤ -Real.log (f (1 / γ)) - -Real.log (f 1))
    (hσ0 : f (1 / γ) = 0 → s0 = 0) (hTh : 0 < s0 → 1 / γ - 1 ≤ s0 * Th)
    (hM : ∀ u, Th ≤ u → ∀ s, 1 / γ < s → M u ≤ γ * s * exp (-(u * ((γ * s - 1) / (s - 1)))))
    {x : ℝ} (hx : 0 ≤ x) :
    PsiF γ (f 1) a0 s0 T Th M (f x) ≤ γ * x * f (γ * x) := by
  have hR : 0 ≤ γ * x * f (γ * x) := mul_nonneg (mul_nonneg hγ0.le hx) (hnn _)
  unfold PsiF
  split_ifs with hA hq hG hgap htail
  · exact pw_E f hconv h0 h1 hanti hopt hnn hγ0 hγ1.le hx hA hq
  · exact hR
  · push Not at hA
    exact pw_G1 f hconv h0 h1 hanti hopt hnn hγ0 hγ1 hG hA ha0 hs0 hσ hσ0
  · push Not at hG
    exact pw_gap f hconv h0 h1 hanti hopt hnn hγ0 hγ1 hgap.2 hG hT ha0 hgap.1
      (fun h => (hσ h).1) hσ0 (fun s hs => hM Th le_rfl s hs)
  · have hlt : f x < f 1 * exp (-Th) := by
      by_contra h; push Not at h; exact hgap ⟨htail.1, h⟩
    have hu : Th ≤ -Real.log (f x / f 1) := by
      rw [u_eq htail.2 h1]
      have := Real.log_lt_log htail.2 hlt
      rw [Real.log_mul h1.ne' (exp_pos _).ne', Real.log_exp] at this
      linarith
    exact pw_tail f hconv h1 hanti hnn hγ0 hγ1 htail.2 hlt htail.1 (hTh htail.1)
      (fun h => (hσ h).1) hσ0 le_rfl (fun s hs => hM _ hu s hs)
  · exact hR

lemma PsiF_meas {γ A a0 s0 T Th : ℝ} {M : ℝ → ℝ} (hM : Measurable M) :
    Measurable (PsiF γ A a0 s0 T Th M) := by
  unfold PsiF
  refine Measurable.ite (measurableSet_le measurable_const measurable_id) ?_ ?_
  · exact Measurable.ite (measurableSet_le measurable_id measurable_const) (by fun_prop) measurable_const
  · refine Measurable.ite (measurableSet_lt measurable_const measurable_id) (by fun_prop) ?_
    refine Measurable.ite ?_ measurable_const ?_
    · rw [Set.setOf_and]
      exact (MeasurableSet.const _).inter (measurableSet_le measurable_const measurable_id)
    · refine Measurable.ite ?_ (by fun_prop) measurable_const
      rw [Set.setOf_and]
      exact (MeasurableSet.const _).inter (measurableSet_lt measurable_const measurable_id)

lemma PsiF_bdd {γ A a0 s0 T Th CM : ℝ} {M : ℝ → ℝ} (hγ0 : 0 < γ) (hγ1 : γ ≤ 1) (hA0 : 0 < A)
    (hA1 : A ≤ 1) (ha0 : 0 ≤ a0) (ha01 : a0 ≤ 1) (hs0 : 0 ≤ s0) (hT : 0 ≤ T)
    (hsT : γ * (1 + s0 * T) ≤ 1) (hM : ∀ u, |M u| ≤ CM) (q : ℝ) :
    |PsiF γ A a0 s0 T Th M q| ≤ 3 + CM := by
  have hCM : 0 ≤ CM := le_trans (abs_nonneg _) (hM 0)
  have he1 : exp 1 < 3 := by have := Real.exp_one_lt_d9; norm_num at this ⊢; linarith
  have key : ∀ y, 1 ≤ y → γ * y ≤ 1 → |γ * y * exp (a0 * (1 - γ * y))| ≤ 3 := by
    intro y hy1 hγy
    have hγy0 : 0 ≤ γ * y := mul_nonneg hγ0.le (by linarith)
    rw [abs_of_nonneg (mul_nonneg hγy0 (exp_pos _).le)]
    have hex : exp (a0 * (1 - γ * y)) ≤ exp 1 := exp_le_exp.2 (by nlinarith)
    calc γ * y * exp (a0 * (1 - γ * y)) ≤ 1 * exp 1 :=
          mul_le_mul hγy hex (exp_pos _).le zero_le_one
      _ ≤ 3 := by linarith
  unfold PsiF
  split_ifs with hAq hq hG hgap htail
  · have hq0 : 0 < q := lt_of_lt_of_le hA0 hAq
    have ht : 0 ≤ -Real.log q := by have := Real.log_nonpos hq0.le hq; linarith
    have hta : -Real.log q ≤ -Real.log A := by have := Real.log_le_log hA0 hAq; linarith
    have hr0 : 0 ≤ -Real.log q / -Real.log A := div_nonneg ht (le_trans ht hta)
    have hr1 : -Real.log q / -Real.log A ≤ 1 := div_le_one_of_le₀ hta (le_trans ht hta)
    have hex : exp (-(γ * -Real.log q)) ≤ 1 := by
      calc exp (-(γ * -Real.log q)) ≤ exp 0 := exp_le_exp.2 (by nlinarith)
        _ = 1 := exp_zero
    rw [abs_of_nonneg (mul_nonneg (mul_nonneg hγ0.le hr0) (exp_pos _).le)]
    calc γ * (-Real.log q / -Real.log A) * exp (-(γ * -Real.log q)) ≤ 1 * 1 * 1 :=
          mul_le_mul (mul_le_mul hγ1 hr1 hr0 zero_le_one) hex (exp_pos _).le (by norm_num)
      _ ≤ 3 + CM := by linarith
  · rw [abs_zero]; linarith
  · push Not at hAq
    have hq0 : 0 < q := lt_trans (mul_pos hA0 (exp_pos _)) hG
    have hqA : q / A < 1 := by rw [div_lt_one hA0]; exact hAq
    have hu0 : 0 ≤ -Real.log (q / A) := by
      have := Real.log_nonpos (div_pos hq0 hA0).le hqA.le; linarith
    have huT : -Real.log (q / A) ≤ T := by
      have h2 : exp (-T) < q / A := by rw [lt_div_iff₀ hA0]; linarith [mul_comm A (exp (-T))]
      have := Real.log_lt_log (exp_pos _) h2
      rw [Real.log_exp] at this; linarith
    have hy1 : 1 ≤ 1 + s0 * -Real.log (q / A) := by nlinarith [mul_nonneg hs0 hu0]
    have hγy : γ * (1 + s0 * -Real.log (q / A)) ≤ 1 :=
      le_trans (mul_le_mul_of_nonneg_left (by nlinarith [mul_le_mul_of_nonneg_left huT hs0]) hγ0.le) hsT
    rw [abs_mul, abs_of_pos hA0]
    calc A * |γ * (1 + s0 * -Real.log (q / A)) * exp (a0 * (1 - γ * (1 + s0 * -Real.log (q / A))))|
        ≤ 1 * 3 := mul_le_mul hA1 (key _ hy1 hγy) (abs_nonneg _) zero_le_one
      _ ≤ 3 + CM := by linarith
  · have hy1 : 1 ≤ min (1 + s0 * T) (1 / γ) :=
      le_min (by nlinarith [mul_nonneg hs0 hT]) (by rw [le_div_iff₀ hγ0]; linarith)
    have hγy : γ * min (1 + s0 * T) (1 / γ) ≤ 1 :=
      le_trans (mul_le_mul_of_nonneg_left (min_le_left _ _) hγ0.le) hsT
    have hX := abs_le.1 (key _ hy1 hγy)
    have hm := abs_le.1 (hM Th)
    have hmin : |min (γ * min (1 + s0 * T) (1 / γ) * exp (a0 * (1 - γ * min (1 + s0 * T) (1 / γ)))) (M Th)|
        ≤ 3 + CM := by
      apply abs_le.2; constructor
      · exact le_min (by linarith) (by linarith)
      · exact le_trans (min_le_left _ _) (by linarith)
    rw [abs_mul, abs_of_pos hA0]
    calc _ ≤ 1 * (3 + CM) := mul_le_mul hA1 hmin (abs_nonneg _) zero_le_one
      _ = 3 + CM := one_mul _
  · rw [abs_mul, abs_of_pos hA0]
    calc _ ≤ 1 * CM := mul_le_mul hA1 (hM _) (abs_nonneg _) zero_le_one
      _ ≤ 3 + CM := by linarith
  · rw [abs_zero]; linarith

end PricingSamples.OneSampleMHR.Pt2

-- ===== from d95b66c5_int.lean
/-! Session 7 (d95b66c5): splitting `∫_{[0,1]} PsiF` into its four pieces. -/

namespace PricingSamples.OneSampleMHR.Int7

open Real MeasureTheory

open PricingSamples.OneSampleMHR.Pt2 (PsiF)

lemma ii_of_bdd {Ψ : ℝ → ℝ} (hm : Measurable Ψ) {C : ℝ} (hb : ∀ q, |Ψ q| ≤ C) (x y : ℝ) :
    IntervalIntegrable Ψ volume x y := by
  rw [intervalIntegrable_iff]
  exact Measure.integrableOn_of_bounded (by rw [Set.uIoc, Real.volume_Ioc]; exact ENNReal.ofReal_ne_top) hm.aestronglyMeasurable
    (ae_of_all _ fun q => by rw [Real.norm_eq_abs]; exact hb q)

/-- Four-piece split of the certificate integral. -/
lemma PsiF_split {γ A a0 s0 T Th C : ℝ} {M : ℝ → ℝ} (hm : Measurable (PsiF γ A a0 s0 T Th M))
    (hb : ∀ q, |PsiF γ A a0 s0 T Th M q| ≤ C) (hA0 : 0 < A) (hA1 : A ≤ 1) (hT : 0 < T)
    (hTTh : T ≤ Th) :
    ∫ q in Set.Icc (0 : ℝ) 1, PsiF γ A a0 s0 T Th M q =
      (∫ q in (0 : ℝ)..A * exp (-Th), if 0 < s0 then A * M (-Real.log (q / A)) else 0)
      + (∫ _ in A * exp (-Th)..A * exp (-T), if 0 < s0 then
          A * min (γ * min (1 + s0 * T) (1 / γ) * exp (a0 * (1 - γ * min (1 + s0 * T) (1 / γ)))) (M Th)
          else 0)
      + (∫ q in A * exp (-T)..A,
          A * (γ * (1 + s0 * -Real.log (q / A)) * exp (a0 * (1 - γ * (1 + s0 * -Real.log (q / A))))))
      + (∫ q in A..1, γ * (-Real.log q / -Real.log A) * exp (-(γ * -Real.log q))) := by
  set Ψ := PsiF γ A a0 s0 T Th M with hΨ
  set L := A * exp (-Th) with hL
  set B := A * exp (-T) with hB
  have hL0 : 0 ≤ L := (mul_pos hA0 (exp_pos _)).le
  have hLB : L ≤ B := mul_le_mul_of_nonneg_left (exp_le_exp.2 (by linarith)) hA0.le
  have hBA : B < A := by
    have : exp (-T) < 1 := by
      have := exp_lt_exp.2 (show -T < 0 by linarith); rwa [exp_zero] at this
    calc B = A * exp (-T) := rfl
      _ < A * 1 := mul_lt_mul_of_pos_left this hA0
      _ = A := mul_one A
  have hI := ii_of_bdd hm hb
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le zero_le_one,
    ← intervalIntegral.integral_add_adjacent_intervals (hI 0 A) (hI A 1),
    ← intervalIntegral.integral_add_adjacent_intervals (hI 0 B) (hI B A),
    ← intervalIntegral.integral_add_adjacent_intervals (hI 0 L) (hI L B)]
  have hae : ∀ᵐ x ∂(volume : Measure ℝ), x ≠ A ∧ x ≠ B ∧ x ≠ L := by
    have h3 : ({A, B, L} : Set ℝ).Countable := by simp
    filter_upwards [h3.ae_notMem volume] with x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hx
    exact hx
  have hBnn : ¬ A ≤ B := not_le.2 hBA
  congr 1
  congr 1
  congr 1
  · refine intervalIntegral.integral_congr_ae ?_
    filter_upwards [hae] with x hx hxI
    rw [Set.uIoc_of_le hL0] at hxI
    have hxL : x < L := lt_of_le_of_ne hxI.2 hx.2.2
    have h1 : ¬ A ≤ x := by intro h; linarith
    have h2 : ¬ B < x := by intro h; linarith
    have h3 : ¬ (0 < s0 ∧ L ≤ x) := fun h => by linarith [h.2]
    simp only [hΨ, PsiF, ← hL, ← hB, if_neg h1, if_neg h2, if_neg h3]
    by_cases hs : 0 < s0
    · simp [hs, hxI.1]
    · simp [hs]
  · refine intervalIntegral.integral_congr_ae ?_
    filter_upwards [hae] with x hx hxI
    rw [Set.uIoc_of_le hLB] at hxI
    have hxB : x < B := lt_of_le_of_ne hxI.2 hx.2.1
    have h1 : ¬ A ≤ x := by intro h; linarith
    have h2 : ¬ B < x := by intro h; linarith
    simp only [hΨ, PsiF, ← hL, ← hB, if_neg h1, if_neg h2]
    by_cases hs : 0 < s0
    · simp [hs, hxI.1.le, ← hL]
    · simp [hs]
  · refine intervalIntegral.integral_congr_ae ?_
    filter_upwards [hae] with x hx hxI
    rw [Set.uIoc_of_le hBA.le] at hxI
    have hxA : x < A := lt_of_le_of_ne hxI.2 hx.1
    have h1 : ¬ A ≤ x := by intro h; linarith
    simp only [hΨ, PsiF, ← hL, ← hB, if_neg h1, if_pos hxI.1]
  · refine intervalIntegral.integral_congr_ae ?_
    filter_upwards with x hxI
    rw [Set.uIoc_of_le hA1] at hxI
    simp only [hΨ, PsiF, if_pos hxI.1.le, if_pos hxI.2]

end PricingSamples.OneSampleMHR.Int7

-- ===== from d95b66c5_mt.lean
/-! Session 7 (d95b66c5): the tail function `M u = min_{s>1} γ s e^{-u(γs-1)/(s-1)}` in closed form. -/

namespace PricingSamples.OneSampleMHR.Mt

open Real

noncomputable def Sr (γ u : ℝ) : ℝ :=
  ((2 + (1 - γ) * u) + √((2 + (1 - γ) * u) ^ 2 - 4)) / 2

noncomputable def phi (γ u s : ℝ) : ℝ := γ * s * exp (-(u * ((γ * s - 1) / (s - 1))))

noncomputable def Mf (γ u : ℝ) : ℝ := phi γ u (Sr γ u)

/-- The certificate's tail function, clamped below at `c = 1/γ - 1`. -/
noncomputable def Mc (γ u : ℝ) : ℝ := Mf γ (max u (1 / γ - 1))

lemma Sr_facts {γ u : ℝ} (hγ1 : γ ≤ 1) (hu : 0 ≤ u) :
    u * (1 - γ) * Sr γ u = (Sr γ u - 1) ^ 2 ∧ (2 + (1 - γ) * u) - Sr γ u ≤ 1 ∧
      Sr γ u * ((2 + (1 - γ) * u) - Sr γ u) = 1 := by
  set x := 2 + (1 - γ) * u with hx
  have hx2 : 2 ≤ x := by have : 0 ≤ (1 - γ) * u := mul_nonneg (by linarith) hu; linarith
  have hy : 0 ≤ x ^ 2 - 4 := by nlinarith
  set r := √(x ^ 2 - 4) with hr
  have hr2 : r ^ 2 = x ^ 2 - 4 := Real.sq_sqrt hy
  have hr0 : 0 ≤ r := Real.sqrt_nonneg _
  have hxr : x - 2 ≤ r := by
    have h1 : √((x - 2) ^ 2) ≤ r := Real.sqrt_le_sqrt (by nlinarith)
    rwa [Real.sqrt_sq (by linarith)] at h1
  have hS : Sr γ u = (x + r) / 2 := rfl
  rw [hS]
  refine ⟨?_, by linarith, by linear_combination (-1 / 4 : ℝ) * hr2⟩
  have : u * (1 - γ) = x - 2 := by rw [hx]; ring
  rw [this]
  linear_combination (-1 / 4 : ℝ) * hr2

lemma Sr_gt_one {γ u : ℝ} (hγ1 : γ < 1) (hu : 0 < u) : 1 < Sr γ u := by
  have h0 : 0 < (1 - γ) * u := mul_pos (by linarith) hu
  have : 0 ≤ √((2 + (1 - γ) * u) ^ 2 - 4) := Real.sqrt_nonneg _
  unfold Sr; linarith

lemma Sr_ge_inv {γ u : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1) (hu : 1 / γ - 1 ≤ u) : 1 / γ ≤ Sr γ u := by
  have hc : 0 < 1 / γ - 1 := by rw [one_div, sub_pos]; exact one_lt_inv_iff₀.2 ⟨hγ0, hγ1⟩
  obtain ⟨_, hS', hprod⟩ := Sr_facts hγ1.le (by linarith)
  set x := 2 + (1 - γ) * u
  set S := Sr γ u
  set t := 1 / γ with ht
  have hct : (1 - γ) * t = t - 1 := by rw [ht]; field_simp
  have hq : t ^ 2 - x * t + 1 ≤ 0 := by
    have : t ^ 2 - x * t + 1 = (t - 1) * (t - 1 - u) := by
      have : x * t = 2 * t + u * ((1 - γ) * t) := by simp only [x]; ring
      rw [this, hct]; ring
    rw [this]; exact mul_nonpos_of_nonneg_of_nonpos hc.le (by linarith)
  by_contra hlt
  push Not at hlt
  have h1 : 0 < t - S := by linarith
  have h2 : 0 < t - (x - S) := by linarith
  have : t ^ 2 - x * t + 1 = (t - S) * (t - (x - S)) := by linear_combination (-1 : ℝ) * hprod
  nlinarith [mul_pos h1 h2]

/-- `s = S` minimises `φ(u, ·)` over `s > 1` (only `log t ≥ 1 - 1/t` is used). -/
lemma phi_min {γ u S s : ℝ} (hS1 : 1 < S) (hroot : u * (1 - γ) * S = (S - 1) ^ 2) (hs : 1 < s)
    (hγ0 : 0 < γ) : phi γ u S ≤ phi γ u s := by
  have hS0 : 0 < S := by linarith
  have hs0 : 0 < s := by linarith
  have hS1' : S - 1 ≠ 0 := by linarith
  have hs1' : s - 1 ≠ 0 := by linarith
  have hlog : 1 - S / s ≤ log s - log S := by
    have := Real.one_sub_inv_le_log_of_pos (div_pos hs0 hS0)
    rw [Real.log_div hs0.ne' hS0.ne', inv_div] at this; linarith
  have e : u * ((γ * s - 1) / (s - 1)) - u * ((γ * S - 1) / (S - 1))
      = u * (1 - γ) * S * (s - S) / (S * (s - 1) * (S - 1)) := by
    field_simp; ring
  have e2 : 1 - S / s - (S - 1) ^ 2 * (s - S) / (S * (s - 1) * (S - 1))
      = (s - S) ^ 2 / (s * S * (s - 1)) := by
    field_simp; ring
  have hnn : 0 ≤ (s - S) ^ 2 / (s * S * (s - 1)) :=
    div_nonneg (sq_nonneg _) (mul_pos (mul_pos hs0 hS0) (by linarith)).le
  have hkey : log S - u * ((γ * S - 1) / (S - 1)) ≤ log s - u * ((γ * s - 1) / (s - 1)) := by
    rw [hroot] at e; linarith
  have rep : ∀ v, 0 < v → phi γ u v = γ * exp (log v - u * ((γ * v - 1) / (v - 1))) := by
    intro v hv
    unfold phi
    rw [Real.exp_sub, exp_log hv, exp_neg]; ring
  rw [rep S hS0, rep s hs0]
  exact mul_le_mul_of_nonneg_left (exp_le_exp.2 hkey) hγ0.le

lemma phi_anti_u {γ u u' s : ℝ} (hγ0 : 0 < γ) (hs : 1 / γ ≤ s) (hs1 : 1 < s) (huu : u ≤ u') :
    phi γ u' s ≤ phi γ u s := by
  have hw : 0 ≤ (γ * s - 1) / (s - 1) := by
    have : 1 ≤ γ * s := by rw [div_le_iff₀ hγ0] at hs; linarith
    exact div_nonneg (by linarith) (by linarith)
  unfold phi
  exact mul_le_mul_of_nonneg_left (exp_le_exp.2 (by nlinarith)) (by positivity)

lemma Mf_le_phi {γ u s : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1) (hu : 0 < u) (hs : 1 < s) :
    Mf γ u ≤ phi γ u s :=
  phi_min (Sr_gt_one hγ1 hu) (Sr_facts hγ1.le hu.le).1 hs hγ0

lemma Mf_anti {γ u u' : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1) (hu : 1 / γ - 1 ≤ u) (huu : u ≤ u') :
    Mf γ u' ≤ Mf γ u := by
  have hc : 0 < 1 / γ - 1 := by rw [one_div, sub_pos]; exact one_lt_inv_iff₀.2 ⟨hγ0, hγ1⟩
  have hu0 : 0 < u := by linarith
  calc Mf γ u' ≤ phi γ u' (Sr γ u) := Mf_le_phi hγ0 hγ1 (by linarith) (Sr_gt_one hγ1 hu0)
    _ ≤ phi γ u (Sr γ u) := phi_anti_u hγ0 (Sr_ge_inv hγ0 hγ1 hu) (Sr_gt_one hγ1 hu0) huu

lemma Mc_eq {γ u : ℝ} (hu : 1 / γ - 1 ≤ u) : Mc γ u = Mf γ u := by
  unfold Mc; rw [max_eq_left hu]

lemma Mc_anti {γ u u' : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1) (huu : u ≤ u') : Mc γ u' ≤ Mc γ u :=
  Mf_anti hγ0 hγ1 (le_max_right _ _) (max_le_max huu le_rfl)

lemma Mc_bdd {γ : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1) (u : ℝ) : |Mc γ u| ≤ 1 := by
  have hc : 0 < 1 / γ - 1 := by rw [one_div, sub_pos]; exact one_lt_inv_iff₀.2 ⟨hγ0, hγ1⟩
  have hv : 0 < max u (1 / γ - 1) := lt_of_lt_of_le hc (le_max_right _ _)
  have hS := Sr_gt_one hγ1 hv
  have h0 : 0 ≤ Mc γ u := by
    unfold Mc Mf phi; have := exp_pos (-(max u (1 / γ - 1) * ((γ * Sr γ (max u (1 / γ - 1)) - 1)
      / (Sr γ (max u (1 / γ - 1)) - 1)))); positivity
  rw [abs_of_nonneg h0]
  have hinv : 1 < 1 / γ := by linarith
  calc Mc γ u ≤ phi γ (max u (1 / γ - 1)) (1 / γ) := Mf_le_phi hγ0 hγ1 hv hinv
    _ ≤ phi γ (1 / γ - 1) (1 / γ) := phi_anti_u hγ0 le_rfl hinv (le_max_right _ _)
    _ = 1 := by unfold phi; field_simp; simp

lemma Mc_hM {γ Th : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1) (hTh : 1 / γ - 1 ≤ Th) :
    ∀ u, Th ≤ u → ∀ s, 1 / γ < s → Mc γ u ≤ γ * s * exp (-(u * ((γ * s - 1) / (s - 1)))) := by
  intro u hu s hs
  have hc : 0 < 1 / γ - 1 := by rw [one_div, sub_pos]; exact one_lt_inv_iff₀.2 ⟨hγ0, hγ1⟩
  rw [Mc_eq (le_trans hTh hu)]
  exact Mf_le_phi hγ0 hγ1 (by linarith) (by linarith)

lemma Mc_meas (γ : ℝ) : Measurable (Mc γ) := by
  unfold Mc Mf phi Sr; fun_prop

end PricingSamples.OneSampleMHR.Mt

-- ===== from d95b66c5_tail.lean
/-! Session 7 (d95b66c5): step lower bound of the tail integral for an antitone, bounded `M`. -/

namespace PricingSamples.OneSampleMHR.Tail

open Real MeasureTheory

noncomputable def TI (A : ℝ) (M : ℝ → ℝ) (v : ℝ) : ℝ :=
  ∫ q in (0 : ℝ)..A * exp (-v), A * M (-Real.log (q / A))

noncomputable def stepSum (M : ℝ → ℝ) : List ℝ → ℝ
  | u0 :: u1 :: rest => M u1 * (exp (-u0) - exp (-u1)) + stepSum M (u1 :: rest)
  | _ => 0

section
variable {A Th0 C : ℝ} {M : ℝ → ℝ}

lemma tail_ii (hm : Measurable M) (hb : ∀ u, |M u| ≤ C) (x y : ℝ) :
    IntervalIntegrable (fun q => A * M (-Real.log (q / A))) volume x y := by
  rw [intervalIntegrable_iff]
  refine Measure.integrableOn_of_bounded (M := |A| * C)
    (by rw [Set.uIoc, Real.volume_Ioc]; exact ENNReal.ofReal_ne_top)
    (by fun_prop : Measurable fun q => A * M (-Real.log (q / A))).aestronglyMeasurable
    (ae_of_all _ fun q => ?_)
  rw [Real.norm_eq_abs, abs_mul]
  exact mul_le_mul_of_nonneg_left (hb _) (abs_nonneg _)

lemma piece_ge (hA : 0 < A) (hm : Measurable M) (hb : ∀ u, |M u| ≤ C)
    (hanti : ∀ u v, Th0 ≤ u → u ≤ v → M v ≤ M u) {lo hi : ℝ} (hlo : Th0 ≤ lo) (hlh : lo ≤ hi) :
    A * M hi * (A * exp (-lo) - A * exp (-hi))
      ≤ ∫ q in A * exp (-hi)..A * exp (-lo), A * M (-Real.log (q / A)) := by
  have hle : A * exp (-hi) ≤ A * exp (-lo) :=
    mul_le_mul_of_nonneg_left (exp_le_exp.2 (by linarith)) hA.le
  have hc : ∫ _ in A * exp (-hi)..A * exp (-lo), A * M hi
      = (A * exp (-lo) - A * exp (-hi)) * (A * M hi) := by
    rw [intervalIntegral.integral_const, smul_eq_mul]
  calc A * M hi * (A * exp (-lo) - A * exp (-hi))
      = ∫ _ in A * exp (-hi)..A * exp (-lo), A * M hi := by rw [hc]; ring
    _ ≤ _ := by
      refine intervalIntegral.integral_mono_on hle intervalIntegrable_const
        (tail_ii hm hb _ _) ?_
      intro x hx
      have hx0 : 0 < x := lt_of_lt_of_le (mul_pos hA (exp_pos _)) hx.1
      have hxA : 0 < x / A := div_pos hx0 hA
      have h1 : -hi ≤ Real.log (x / A) := by
        rw [Real.le_log_iff_exp_le hxA, le_div_iff₀ hA]; linarith [hx.1]
      have h2 : Real.log (x / A) ≤ -lo := by
        rw [Real.log_le_iff_le_exp hxA, div_le_iff₀ hA]; linarith [hx.2]
      exact mul_le_mul_of_nonneg_left (hanti _ _ (by linarith) (by linarith)) hA.le

lemma TI_split (hm : Measurable M) (hb : ∀ u, |M u| ≤ C) (u0 u1 : ℝ) :
    TI A M u0 = TI A M u1 + ∫ q in A * exp (-u1)..A * exp (-u0), A * M (-Real.log (q / A)) := by
  unfold TI
  rw [intervalIntegral.integral_add_adjacent_intervals (tail_ii hm hb _ _) (tail_ii hm hb _ _)]

lemma TI_nonneg (hA : 0 < A) (hM0 : ∀ u, 0 ≤ M u) (v : ℝ) : 0 ≤ TI A M v := by
  unfold TI
  refine intervalIntegral.integral_nonneg (mul_pos hA (exp_pos _)).le fun q _ => ?_
  exact mul_nonneg hA.le (hM0 _)

lemma TI_anti (hA : 0 < A) (hm : Measurable M) (hb : ∀ u, |M u| ≤ C) (hM0 : ∀ u, 0 ≤ M u)
    {v w : ℝ} (hvw : v ≤ w) : TI A M w ≤ TI A M v := by
  rw [TI_split (A := A) hm hb v w]
  have hle : A * exp (-w) ≤ A * exp (-v) :=
    mul_le_mul_of_nonneg_left (exp_le_exp.2 (by linarith)) hA.le
  have : 0 ≤ ∫ q in A * exp (-w)..A * exp (-v), A * M (-Real.log (q / A)) :=
    intervalIntegral.integral_nonneg hle fun q _ => mul_nonneg hA.le (hM0 _)
  linarith

lemma TI_ge_stepSum (hA : 0 < A) (hm : Measurable M) (hb : ∀ u, |M u| ≤ C)
    (hM0 : ∀ u, 0 ≤ M u) (hanti : ∀ u v, Th0 ≤ u → u ≤ v → M v ≤ M u) :
    ∀ (rest : List ℝ) (u0 : ℝ), List.IsChain (· ≤ ·) (u0 :: rest) → Th0 ≤ u0 →
      A * A * stepSum M (u0 :: rest) ≤ TI A M u0 := by
  intro rest
  induction rest with
  | nil => intro u0 _ _; simp only [stepSum, mul_zero]; exact TI_nonneg hA hM0 u0
  | cons u1 rest ih =>
    intro u0 hch hu0
    rw [List.isChain_cons_cons] at hch
    have h01 := hch.1
    have ih' := ih u1 hch.2 (le_trans hu0 h01)
    have hp := piece_ge hA hm hb hanti hu0 h01
    rw [TI_split (A := A) hm hb u0 u1]
    simp only [stepSum] at ih' ⊢
    nlinarith [ih', hp]

end

end PricingSamples.OneSampleMHR.Tail

-- ===== session 8: assembly of the certificate integral lower bound
namespace PricingSamples.OneSampleMHR.Asm

open Real MeasureTheory
open PricingSamples.OneSampleMHR.Pt2 (PsiF)

/-- The `E` piece for `0 < A ≤ 1` (the `A = 1` edge gives `0 = 0`). -/
lemma E_part {γ A : ℝ} (hγ : 0 < γ) (hA0 : 0 < A) (hA1 : A ≤ 1) :
    ∫ q in A..1, γ * (-Real.log q / -Real.log A) * exp (-(γ * -Real.log q))
      = A * Pt.Eint γ (-Real.log A) := by
  rcases hA1.lt_or_eq with h | h
  · have ha : 0 < -Real.log A := by have := Real.log_neg hA0 h; linarith
    have hE := Pt.E_piece (γ := γ) (a := -Real.log A) hγ ha
    simp only [neg_neg, Real.exp_log hA0] at hE
    exact hE
  · subst h
    simp [Pt.Eint]

/-- Per-cell reduction for `s0 = 0` (no gap / tail pieces). -/
lemma cell_bound0 {γ A a0 a1 T Th C θ eL gL xL : ℝ} {M : ℝ → ℝ}
    (hm : Measurable (PsiF γ A a0 0 T Th M)) (hb : ∀ q, |PsiF γ A a0 0 T Th M q| ≤ C)
    (hγ : 0 < γ) (hA0 : 0 < A) (hA1 : A ≤ 1) (hT : 0 < T) (hTTh : T ≤ Th)
    (ha0 : 0 ≤ a0) (haA : a0 ≤ -Real.log A) (haA1 : -Real.log A ≤ a1) (ha1 : a1 * γ ≤ 1)
    (heL : eL ≤ Pt.Eint γ a0)
    (hgL : gL ≤ γ * exp (a0 * (1 - γ)) * (((a0 * γ * 0 + 1) * 1 + 0) / (a0 * γ * 0 + 1) ^ 2
        - exp (-(a0 * γ * 0 + 1) * T) * ((a0 * γ * 0 + 1) * (1 + 0 * T) + 0)
          / (a0 * γ * 0 + 1) ^ 2))
    (hgL0 : 0 ≤ gL) (hxL : xL ≤ exp (-a1)) (hxL0 : 0 ≤ xL)
    (hθ : θ ≤ eL + xL * gL) :
    θ * A ≤ ∫ q in Set.Icc (0 : ℝ) 1, PsiF γ A a0 0 T Th M q := by
  rw [Int7.PsiF_split hm hb hA0 hA1 hT hTTh]
  simp only [lt_self_iff_false, if_false, ↓reduceIte, intervalIntegral.integral_zero, zero_add]
  rw [E_part hγ hA0 hA1,
    Pt.G1_piece (γ := γ) (A := A) (a0 := a0) (s0 := 0) (T := T) hA0 (by simp)]
  have hE2 : Pt.Eint γ a0 ≤ Pt.Eint γ (-Real.log A) := by
    refine Pt.Eint_mono hγ.le ha0 haA ?_
    have := mul_le_mul_of_nonneg_right haA1 hγ.le
    linarith
  have hAx : xL ≤ A := by
    have h1 : exp (-a1) ≤ exp (-(-Real.log A)) := Real.exp_le_exp.mpr (by linarith)
    rw [neg_neg, Real.exp_log hA0] at h1
    linarith
  have key : ∀ X : ℝ, gL ≤ X → θ * A ≤ A * (A * X) + A * Pt.Eint γ (-Real.log A) := by
    intro X hX
    have h1 : xL * gL ≤ A * X :=
      le_trans (mul_le_mul_of_nonneg_right hAx hgL0) (mul_le_mul_of_nonneg_left hX hA0.le)
    have h2 : eL ≤ Pt.Eint γ (-Real.log A) := le_trans heL hE2
    have h3 : θ * A ≤ (eL + xL * gL) * A := mul_le_mul_of_nonneg_right hθ hA0.le
    linarith [mul_le_mul_of_nonneg_left h1 hA0.le, mul_le_mul_of_nonneg_left h2 hA0.le]
  have := key _ hgL
  linarith

lemma PsiF_int_ge {γ A a0 s0 T Th C : ℝ} {M : ℝ → ℝ}
    (hm : Measurable (PsiF γ A a0 s0 T Th M)) (hb : ∀ q, |PsiF γ A a0 s0 T Th M q| ≤ C)
    (hγ : 0 < γ) (hA0 : 0 < A) (hA1 : A ≤ 1) (hT : 0 < T) (hTTh : T ≤ Th) (hs0 : 0 < s0)
    (hk : a0 * γ * s0 + 1 ≠ 0)
    (hMm : Measurable M) (hMb : ∀ u, |M u| ≤ C) (hM0 : ∀ u, 0 ≤ M u)
    (hanti : ∀ u v, Th ≤ u → u ≤ v → M v ≤ M u)
    (rest : List ℝ) (hch : List.IsChain (· ≤ ·) (Th :: rest)) :
    A * Pt.Eint γ (-Real.log A)
      + A * (A * (γ * exp (a0 * (1 - γ)) * (((a0 * γ * s0 + 1) * 1 + s0) / (a0 * γ * s0 + 1) ^ 2
        - exp (-(a0 * γ * s0 + 1) * T) * ((a0 * γ * s0 + 1) * (1 + s0 * T) + s0)
          / (a0 * γ * s0 + 1) ^ 2)))
      + (A * exp (-T) - A * exp (-Th)) * (A * min (γ * min (1 + s0 * T) (1 / γ)
          * exp (a0 * (1 - γ * min (1 + s0 * T) (1 / γ)))) (M Th))
      + A * A * Tail.stepSum M (Th :: rest)
      ≤ ∫ q in Set.Icc (0 : ℝ) 1, PsiF γ A a0 s0 T Th M q := by
  rw [Int7.PsiF_split hm hb hA0 hA1 hT hTTh]
  simp only [if_pos hs0]
  have hE := E_part hγ hA0 hA1
  have hG := Pt.G1_piece (γ := γ) (A := A) (a0 := a0) (s0 := s0) (T := T) hA0 hk
  have hgap := Pt.const_piece (A * exp (-Th)) (A * exp (-T)) (A * min (γ * min (1 + s0 * T) (1 / γ)
          * exp (a0 * (1 - γ * min (1 + s0 * T) (1 / γ)))) (M Th))
  have htail := Tail.TI_ge_stepSum (Th0 := Th) hA0 hMm hMb hM0 hanti rest Th hch le_rfl
  unfold Tail.TI at htail
  rw [hE, hG, hgap]
  linarith

/-- Per-cell reduction: certified lower bounds for the closed-form pieces give `θ·A ≤ ∫ PsiF`. -/
lemma cell_bound {γ A a0 a1 s0 T Th C θ eL gL dL pL tL xL : ℝ} {M : ℝ → ℝ}
    (hm : Measurable (PsiF γ A a0 s0 T Th M)) (hb : ∀ q, |PsiF γ A a0 s0 T Th M q| ≤ C)
    (hγ : 0 < γ) (hA0 : 0 < A) (hA1 : A ≤ 1) (hT : 0 < T) (hTTh : T ≤ Th) (hs0 : 0 < s0)
    (hk : a0 * γ * s0 + 1 ≠ 0)
    (hMm : Measurable M) (hMb : ∀ u, |M u| ≤ C) (hM0 : ∀ u, 0 ≤ M u)
    (hanti : ∀ u v, Th ≤ u → u ≤ v → M v ≤ M u)
    (rest : List ℝ) (hch : List.IsChain (· ≤ ·) (Th :: rest))
    (ha0 : 0 ≤ a0) (haA : a0 ≤ -Real.log A) (haA1 : -Real.log A ≤ a1) (ha1 : a1 * γ ≤ 1)
    (heL : eL ≤ Pt.Eint γ a0)
    (hgL : gL ≤ γ * exp (a0 * (1 - γ)) * (((a0 * γ * s0 + 1) * 1 + s0) / (a0 * γ * s0 + 1) ^ 2
        - exp (-(a0 * γ * s0 + 1) * T) * ((a0 * γ * s0 + 1) * (1 + s0 * T) + s0)
          / (a0 * γ * s0 + 1) ^ 2))
    (hdL : dL ≤ exp (-T) - exp (-Th)) (hdL0 : 0 ≤ dL)
    (hpL : pL ≤ min (γ * min (1 + s0 * T) (1 / γ)
          * exp (a0 * (1 - γ * min (1 + s0 * T) (1 / γ)))) (M Th)) (hpL0 : 0 ≤ pL)
    (htL : tL ≤ Tail.stepSum M (Th :: rest))
    (hxL : xL ≤ exp (-a1)) (hxL0 : 0 ≤ xL) (hL0 : 0 ≤ gL + dL * pL + tL)
    (hθ : θ ≤ eL + xL * (gL + dL * pL + tL)) :
    θ * A ≤ ∫ q in Set.Icc (0 : ℝ) 1, PsiF γ A a0 s0 T Th M q := by
  have h := PsiF_int_ge hm hb hγ hA0 hA1 hT hTTh hs0 hk hMm hMb hM0 hanti rest hch
  have hE : Pt.Eint γ a0 ≤ Pt.Eint γ (-Real.log A) := by
    refine Pt.Eint_mono hγ.le ha0 haA ?_
    have := mul_le_mul_of_nonneg_right haA1 hγ.le
    linarith
  have hAx : xL ≤ A := by
    have h1 : exp (-a1) ≤ exp (-(-Real.log A)) := Real.exp_le_exp.mpr (by linarith)
    rw [neg_neg, Real.exp_log hA0] at h1
    linarith
  set G := γ * exp (a0 * (1 - γ)) * (((a0 * γ * s0 + 1) * 1 + s0) / (a0 * γ * s0 + 1) ^ 2
        - exp (-(a0 * γ * s0 + 1) * T) * ((a0 * γ * s0 + 1) * (1 + s0 * T) + s0)
          / (a0 * γ * s0 + 1) ^ 2) with hG
  set P := min (γ * min (1 + s0 * T) (1 / γ)
          * exp (a0 * (1 - γ * min (1 + s0 * T) (1 / γ)))) (M Th) with hP
  set D := exp (-T) - exp (-Th) with hD
  set St := Tail.stepSum M (Th :: rest) with hSt
  set L := gL + dL * pL + tL with hL
  have hDP : dL * pL ≤ D * P := mul_le_mul hdL hpL hpL0 (le_trans hdL0 hdL)
  have hS : L ≤ G + D * P + St := by rw [hL]; linarith
  have h2 : xL * L ≤ A * (G + D * P + St) := by
    calc xL * L ≤ A * L := mul_le_mul_of_nonneg_right hAx hL0
      _ ≤ A * (G + D * P + St) := mul_le_mul_of_nonneg_left hS hA0.le
  have h3 : A * (eL + xL * L) ≤ A * Pt.Eint γ (-Real.log A) + A * A * (G + D * P + St) := by
    have := mul_le_mul_of_nonneg_left h2 hA0.le
    have := mul_le_mul_of_nonneg_left (le_trans heL hE) hA0.le
    nlinarith
  have h4 : A * Pt.Eint γ (-Real.log A) + A * A * (G + D * P + St)
      = A * Pt.Eint γ (-Real.log A) + A * (A * G) + (A * exp (-T) - A * exp (-Th)) * (A * P)
        + A * A * St := by rw [hD]; ring
  have h5 : θ * A ≤ A * (eL + xL * L) := by
    rw [mul_comm]; exact mul_le_mul_of_nonneg_left hθ hA0.le
  linarith

end PricingSamples.OneSampleMHR.Asm

-- ===== from d95b66c5_cs.lean (Chk: tables, checker, soundness)
namespace PricingSamples.OneSampleMHR.Chk
open Real

def S : ℕ := 2 ^ 48
def expLo (X : ℤ) : ℕ := Cert.expLo 48 20 X
def expHi (X : ℤ) : ℕ := S * S / expLo (-X) + 1
def TN (n d : ℕ) : ℕ := 720 * d^6 + 720 * n * d^5 + 360 * n^2 * d^4 + 120 * n^3 * d^3 + 30 * n^4 * d^2 + 6 * n^5 * d + n^6
def TL (n d : ℕ) : ℕ := TN n d * S / (720 * d ^ 6)
def TU (n d : ℕ) : ℕ := 720 * d ^ 6 * S / TN n d + 1

lemma sqIter_ge (p : ℕ) : ∀ (k v : ℕ), 2 ^ p ≤ v → 2 ^ p ≤ Cert.sqIter p k v
  | 0, v, h => by simpa [Cert.sqIter] using h
  | k + 1, v, h => by
    simp only [Cert.sqIter]
    apply sqIter_ge p k
    rw [Nat.le_div_iff_mul_le (by positivity)]
    exact Nat.mul_le_mul h h

lemma expLo_ge {X : ℤ} (hX : 0 ≤ X) : 2 ^ 48 ≤ expLo X := by
  unfold expLo Cert.expLo
  apply sqIter_ge
  have : 0 ≤ X / 2 ^ 20 := Int.ediv_nonneg hX (by positivity)
  omega

lemma expLo_le' {X : ℤ} (hX : -(2 : ℤ) ^ 68 ≤ X) :
    ((expLo X : ℕ) : ℝ) / 2 ^ 48 ≤ Real.exp ((X : ℝ) / 2 ^ 48) :=
  Cert.expLo_le 48 20 X (by norm_num at hX ⊢; exact hX)

lemma expHi_ge {X : ℤ} (hX : X ≤ 0) :
    Real.exp ((X : ℝ) / 2 ^ 48) ≤ ((expHi X : ℕ) : ℝ) / 2 ^ 48 := by
  have hE := expLo_ge (X := -X) (by omega)
  have h68 : (0:ℤ) ≤ 2 ^ 68 := by positivity
  have hl := expLo_le' (X := -X) (by linarith)
  set E := expLo (-X) with hEdef
  have hEr : (2 : ℝ) ^ 48 ≤ (E : ℝ) := by exact_mod_cast hE
  have hEp : (0 : ℝ) < (E : ℝ) := lt_of_lt_of_le (by positivity) hEr
  have hp : (0 : ℝ) < 2 ^ 48 := by positivity
  -- exp(X/S) * (E/S) ≤ exp(X/S) * exp(-X/S) = 1
  have h1 : Real.exp ((X : ℝ) / 2 ^ 48) * ((E : ℝ) / 2 ^ 48) ≤ 1 := by
    have : Real.exp ((X : ℝ) / 2 ^ 48) * Real.exp (((-X : ℤ) : ℝ) / 2 ^ 48) = 1 := by
      rw [← Real.exp_add]; push_cast; rw [show (X : ℝ) / 2 ^ 48 + -(X : ℝ) / 2 ^ 48 = 0 by ring, Real.exp_zero]
    calc _ ≤ Real.exp ((X : ℝ) / 2 ^ 48) * Real.exp (((-X : ℤ) : ℝ) / 2 ^ 48) :=
          mul_le_mul_of_nonneg_left hl (Real.exp_pos _).le
      _ = 1 := this
  -- floor bound: S*S/E + 1 ≥ S*S/E (reals)
  have h2 : ((S * S : ℕ) : ℝ) / (E : ℝ) ≤ ((expHi X : ℕ) : ℝ) := by
    unfold expHi
    rw [← hEdef]
    have := Nat.lt_div_mul_add (a := S * S) (b := E) (by exact_mod_cast hEp)
    rw [div_le_iff₀ hEp]
    have : ((S * S : ℕ) : ℝ) < (((S * S / E) * E + E : ℕ) : ℝ) := by exact_mod_cast this
    push_cast at this ⊢
    nlinarith
  have hS : ((S * S : ℕ) : ℝ) = 2 ^ 48 * 2 ^ 48 := by simp [S]; norm_num
  rw [hS] at h2
  rw [le_div_iff₀ hp]
  have h3 : Real.exp ((X : ℝ) / 2 ^ 48) * (E : ℝ) ≤ 2 ^ 48 := by
    have := h1; rw [mul_div_assoc'] at this; rwa [div_le_one hp] at this
  have h4 : (2 : ℝ) ^ 48 * 2 ^ 48 / (E : ℝ) * (E : ℝ) = 2 ^ 48 * 2 ^ 48 := by field_simp
  nlinarith [Real.exp_pos ((X : ℝ) / 2 ^ 48)]

lemma TN_eq (n d : ℕ) (hd : 0 < d) :
    ((TN n d : ℕ) : ℝ) / (720 * (d : ℝ) ^ 6)
      = ∑ i ∈ Finset.range 7, ((n : ℝ) / d) ^ i / (i.factorial : ℝ) := by
  have hd' : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  simp [TN, Finset.sum_range_succ, Nat.factorial]
  field_simp
  ring

lemma TN_pos (n d : ℕ) (hd : 0 < d) : 0 < TN n d := by
  unfold TN; positivity

lemma TL_le (n d : ℕ) (hd : 0 < d) :
    ((TL n d : ℕ) : ℝ) / 2 ^ 48 ≤ Real.exp ((n : ℝ) / d) := by
  have hx : (0 : ℝ) ≤ (n : ℝ) / d := by positivity
  have hs := Real.sum_le_exp_of_nonneg hx 7
  rw [← TN_eq n d hd] at hs
  have hD : (0 : ℝ) < 720 * (d : ℝ) ^ 6 := by have : (0 : ℝ) < d := by exact_mod_cast hd
                                              positivity
  have hp : (0 : ℝ) < 2 ^ 48 := by positivity
  have hc := Nat.cast_div_le (α := ℝ) (m := TN n d * S) (n := 720 * d ^ 6)
  unfold TL
  calc ((TN n d * S / (720 * d ^ 6) : ℕ) : ℝ) / 2 ^ 48
      ≤ ((TN n d * S : ℕ) : ℝ) / ((720 * d ^ 6 : ℕ) : ℝ) / 2 ^ 48 := by gcongr
    _ = ((TN n d : ℕ) : ℝ) / (720 * (d : ℝ) ^ 6) := by simp [S]; field_simp; norm_num
    _ ≤ _ := hs

lemma TU_ge (n d : ℕ) (hd : 0 < d) :
    Real.exp (-((n : ℝ) / d)) ≤ ((TU n d : ℕ) : ℝ) / 2 ^ 48 := by
  have hx : (0 : ℝ) ≤ (n : ℝ) / d := by positivity
  have hs := Real.sum_le_exp_of_nonneg hx 7
  rw [← TN_eq n d hd] at hs
  have hT : (0 : ℝ) < (TN n d : ℝ) := by exact_mod_cast TN_pos n d hd
  have hD : (0 : ℝ) < 720 * (d : ℝ) ^ 6 := by have : (0 : ℝ) < d := by exact_mod_cast hd
                                              positivity
  have hp : (0 : ℝ) < 2 ^ 48 := by positivity
  -- exp(-x) ≤ 720 d^6 / TN
  have h1 : Real.exp (-((n : ℝ) / d)) ≤ 720 * (d : ℝ) ^ 6 / (TN n d : ℝ) := by
    rw [Real.exp_neg, inv_eq_one_div, div_le_div_iff₀ (Real.exp_pos _) hT, one_mul]
    rw [div_le_iff₀ hD] at hs; linarith
  have h2 : 720 * (d : ℝ) ^ 6 * 2 ^ 48 / (TN n d : ℝ) ≤ ((TU n d : ℕ) : ℝ) := by
    unfold TU
    have := Nat.lt_div_mul_add (a := 720 * d ^ 6 * S) (b := TN n d) (TN_pos n d hd)
    have : ((720 * d ^ 6 * S : ℕ) : ℝ) < (((720 * d ^ 6 * S / TN n d) * TN n d + TN n d : ℕ) : ℝ) := by
      exact_mod_cast this
    rw [div_le_iff₀ hT]
    push_cast [S] at this ⊢
    nlinarith
  rw [le_div_iff₀ hp]
  calc Real.exp (-((n : ℝ) / d)) * 2 ^ 48 ≤ 720 * (d : ℝ) ^ 6 / (TN n d : ℝ) * 2 ^ 48 := by gcongr
    _ = 720 * (d : ℝ) ^ 6 * 2 ^ 48 / (TN n d : ℝ) := by ring
    _ ≤ _ := h2

lemma expLo_le_exp {X : ℤ} {y : ℝ} (hX : -(2 : ℤ) ^ 68 ≤ X) (hy : (X : ℝ) / 2 ^ 48 ≤ y) :
    ((expLo X : ℕ) : ℝ) / 2 ^ 48 ≤ Real.exp y :=
  (expLo_le' hX).trans (Real.exp_le_exp.2 hy)

lemma exp_le_expHi {X : ℤ} {y : ℝ} (hX : X ≤ 0) (hy : y ≤ (X : ℝ) / 2 ^ 48) :
    Real.exp y ≤ ((expHi X : ℕ) : ℝ) / 2 ^ 48 :=
  (Real.exp_le_exp.2 hy).trans (expHi_ge hX)

def tn (j : ℕ) : ℕ := 6 * 2 ^ 30 / (19 * j)
def ETU (j : ℕ) : ℕ := expHi (-((tn j : ℤ) * 2 ^ 28))
def ET (j : ℕ) : ℕ := expLo (-((tn j : ℤ) * 2 ^ 28))
def XA (i : ℕ) : ℕ := expLo (-((i : ℤ) * 2 ^ 37))
def GA (i : ℕ) : ℕ := expLo ((6 * i * 2 ^ 37 / 25 : ℕ) : ℤ)
def EA (i : ℕ) : ℕ :=
  if i = 0 then 0 else
  ((19 * (51200 * (expLo ((i : ℤ) * 2 ^ 37) : ℤ) - (51200 + 44 * i : ℕ) * (expHi (-((19 * i * 2 ^ 37 / 25 : ℕ) : ℤ)) : ℤ))) / (1936 * i : ℕ)).toNat
def EH (n : ℕ) : ℕ := expHi (-((n : ℤ) * 2 ^ 42))
def EL (n : ℕ) : ℕ := expLo (-((n : ℤ) * 2 ^ 42))

lemma tn_le (j : ℕ) : tn j ≤ 6 * 2 ^ 30 := Nat.div_le_self _ _

lemma ET_le (j : ℕ) : ((ET j : ℕ) : ℝ) / 2 ^ 48 ≤ Real.exp (-((tn j : ℝ) / 2 ^ 20)) := by
  have h := tn_le j
  have h' : ((tn j : ℕ) : ℤ) ≤ 6 * 2 ^ 30 := by exact_mod_cast h
  exact expLo_le_exp (by linarith) (le_of_eq (by push_cast; ring))

lemma ETU_ge (j : ℕ) : Real.exp (-((tn j : ℝ) / 2 ^ 20)) ≤ ((ETU j : ℕ) : ℝ) / 2 ^ 48 := by
  have h0 : (0 : ℤ) ≤ ((tn j : ℕ) : ℤ) := by positivity
  exact exp_le_expHi (by linarith) (le_of_eq (by push_cast; ring))

lemma XA_le (i : ℕ) (hi : i ≤ 2 ^ 31) : ((XA i : ℕ) : ℝ) / 2 ^ 48 ≤ Real.exp (-((i : ℝ) / 2048)) := by
  have h' : ((i : ℕ) : ℤ) ≤ 2 ^ 31 := by exact_mod_cast hi
  exact expLo_le_exp (by linarith) (le_of_eq (by push_cast; ring))

lemma GA_le (i : ℕ) : ((GA i : ℕ) : ℝ) / 2 ^ 48 ≤ Real.exp ((i : ℝ) / 2048 * (6 / 25)) := by
  have h0 : (0 : ℤ) ≤ (((6 * i * 2 ^ 37 / 25 : ℕ)) : ℤ) := by positivity
  apply expLo_le_exp (by linarith)
  have hc := Nat.cast_div_le (α := ℝ) (m := 6 * i * 2 ^ 37) (n := 25)
  have : ((((6 * i * 2 ^ 37 / 25 : ℕ) : ℤ)) : ℝ) = ((6 * i * 2 ^ 37 / 25 : ℕ) : ℝ) := by norm_cast
  rw [this]
  calc ((6 * i * 2 ^ 37 / 25 : ℕ) : ℝ) / 2 ^ 48 ≤ ((6 * i * 2 ^ 37 : ℕ) : ℝ) / ((25 : ℕ) : ℝ) / 2 ^ 48 := by gcongr
    _ = _ := by push_cast; ring

lemma EH_ge (n : ℕ) : Real.exp (-((n : ℝ) / 64)) ≤ ((EH n : ℕ) : ℝ) / 2 ^ 48 := by
  have h0 : (0 : ℤ) ≤ ((n : ℕ) : ℤ) := by positivity
  exact exp_le_expHi (by linarith) (le_of_eq (by push_cast; ring))

lemma EL_le (n : ℕ) (hn : n ≤ 2 ^ 26) : ((EL n : ℕ) : ℝ) / 2 ^ 48 ≤ Real.exp (-((n : ℝ) / 64)) := by
  have h' : ((n : ℕ) : ℤ) ≤ 2 ^ 26 := by exact_mod_cast hn
  exact expLo_le_exp (by linarith) (le_of_eq (by push_cast; ring))

/-- closed form of `Eint (19/25) (i/2048)` -/
lemma Eint_val (i : ℕ) (hi : 0 < i) :
    Pt.Eint (19 / 25) ((i : ℝ) / 2048) = 19 * 51200 * (Real.exp ((i : ℝ) / 2048)
      - (1 + 44 * (i : ℝ) / 51200) * Real.exp (-((i : ℝ) / 2048 * (19 / 25)))) / (1936 * (i : ℝ)) := by
  have hi' : (0 : ℝ) < i := by exact_mod_cast hi
  rw [Pt.Eint_eq _ _ (by positivity)]
  have he : Real.exp ((i : ℝ) / 2048) * Real.exp (-((1 + 19 / 25) * ((i : ℝ) / 2048)) * 1)
      = Real.exp (-((i : ℝ) / 2048 * (19 / 25))) := by rw [← Real.exp_add]; congr 1; ring
  rw [← he]
  field_simp
  ring

lemma Eint_nonneg (a : ℝ) (ha : 0 ≤ a) : 0 ≤ Pt.Eint (19 / 25) a := by
  unfold Pt.Eint
  apply intervalIntegral.integral_nonneg zero_le_one
  intro v hv
  have := Real.exp_pos (a * (1 - (1 + 19 / 25) * v))
  have := hv.1
  positivity

lemma EA_le (i : ℕ) (hi : i ≤ 2048) :
    ((EA i : ℕ) : ℝ) / 2 ^ 48 ≤ Pt.Eint (19 / 25) ((i : ℝ) / 2048) := by
  rcases Nat.eq_zero_or_pos i with rfl | hi0
  · simp [EA]; exact Eint_nonneg 0 le_rfl
  have hEn := Eint_nonneg ((i : ℝ) / 2048) (by positivity)
  have h2 : Real.exp (-((i : ℝ) / 2048 * (19 / 25))) ≤ (expHi (-((19 * i * 2 ^ 37 / 25 : ℕ) : ℤ)) : ℝ) / 2 ^ 48 := by
    have h0 : (0 : ℤ) ≤ (((19 * i * 2 ^ 37 / 25 : ℕ)) : ℤ) := by positivity
    apply exp_le_expHi (by linarith)
    have hmn : (19 * i * 2 ^ 37 / 25) * 25 ≤ 19 * i * 2 ^ 37 := Nat.div_mul_le_self _ _
    generalize 19 * i * 2 ^ 37 / 25 = m at hmn ⊢
    have hmr : (m : ℝ) * 25 ≤ 19 * (i : ℝ) * 2 ^ 37 := by exact_mod_cast hmn
    have hc : (((-(m : ℤ)) : ℤ) : ℝ) = -(m : ℝ) := by push_cast; ring
    rw [hc]
    have hp : (0:ℝ) < 2 ^ 48 := by positivity
    rw [neg_div, neg_le_neg_iff, div_le_iff₀ hp]
    nlinarith
  rw [Eint_val i hi0]
  set eL := expLo ((i : ℤ) * 2 ^ 37) with heL
  set eH := expHi (-((19 * i * 2 ^ 37 / 25 : ℕ) : ℤ)) with heH
  have h1 : (eL : ℝ) / 2 ^ 48 ≤ Real.exp ((i : ℝ) / 2048) := by
    have h0 : (0 : ℤ) ≤ ((i : ℕ) : ℤ) := by positivity
    exact expLo_le_exp (by nlinarith) (le_of_eq (by push_cast; ring))
  have hi' : (0 : ℝ) < i := by exact_mod_cast hi0
  have hp : (0:ℝ) < 2 ^ 48 := by positivity
  -- integer numerator
  set N : ℤ := 19 * (51200 * (eL : ℤ) - (51200 + 44 * i : ℕ) * (eH : ℤ)) with hN
  have hEA : EA i = (N / (1936 * i : ℕ)).toNat := by simp [EA, hi0.ne', hN, heL, heH]
  have hNr : (N : ℝ) ≤ 19 * 51200 * 2 ^ 48 * (Real.exp ((i : ℝ) / 2048)
      - (1 + 44 * (i : ℝ) / 51200) * Real.exp (-((i : ℝ) / 2048 * (19 / 25)))) := by
    rw [hN]; push_cast
    have a1 : (eL : ℝ) ≤ 2 ^ 48 * Real.exp ((i : ℝ) / 2048) := by rw [div_le_iff₀ hp] at h1; linarith
    have a2 : 2 ^ 48 * Real.exp (-((i : ℝ) / 2048 * (19 / 25))) ≤ (eH : ℝ) := by rw [le_div_iff₀ hp] at h2; linarith
    have a3 : (0:ℝ) ≤ 1 + 44 * (i : ℝ) / 51200 := by positivity
    nlinarith [mul_le_mul_of_nonneg_left a2 a3]
  rw [hEA]
  rcases le_or_gt (N / (1936 * i : ℕ)) 0 with hq | hq
  · rw [Int.toNat_of_nonpos hq]; simp
    rw [← Eint_val i hi0]; exact hEn
  · have hq' : (((N / (1936 * i : ℕ)).toNat : ℕ) : ℝ) = ((N / (1936 * i : ℕ) : ℤ) : ℝ) := by
      rw [← Int.cast_natCast, Int.toNat_of_nonneg hq.le]
    rw [hq']
    have hd : (0 : ℤ) < ((1936 * i : ℕ) : ℤ) := by positivity
    have hfl : ((N / (1936 * i : ℕ) : ℤ) : ℝ) * (1936 * (i : ℝ)) ≤ (N : ℝ) := by
      have := Int.ediv_mul_le N (ne_of_gt hd)
      have h3 : (((N / (1936 * i : ℕ)) * ((1936 * i : ℕ) : ℤ) : ℤ) : ℝ) ≤ (N : ℝ) := by exact_mod_cast this
      have hcast : (((1936 * i : ℕ) : ℤ) : ℝ) = 1936 * (i : ℝ) := by push_cast; ring
      rw [Int.cast_mul, hcast] at h3; exact h3
    have hD : (0 : ℝ) < 1936 * (i : ℝ) := by positivity
    rw [div_le_iff₀ hp, div_mul_eq_mul_div, le_div_iff₀ hD]
    nlinarith

lemma sqIter_zero (p : ℕ) : ∀ k, Cert.sqIter p k 0 = 0
  | 0 => rfl
  | k + 1 => by simp only [Cert.sqIter, mul_zero, Nat.zero_div]; exact sqIter_zero p k

/-- `expLo` lower bound with no range hypothesis (too-negative arguments give 0). -/
lemma expLo_le_gen {X : ℤ} {y : ℝ} (hy : (X : ℝ) / 2 ^ 48 ≤ y) :
    ((expLo X : ℕ) : ℝ) / 2 ^ 48 ≤ Real.exp y := by
  rcases le_or_gt (-(2 : ℤ) ^ 68) X with hX | hX
  · exact expLo_le_exp hX hy
  · have h0 : (2 : ℤ) ^ 48 + X / 2 ^ 20 < 0 := by
      have : X / 2 ^ 20 < -(2 : ℤ) ^ 48 := by
        rw [Int.ediv_lt_iff_lt_mul (by positivity)]; norm_num at hX ⊢; linarith
      linarith
    have : expLo X = 0 := by
      unfold expLo Cert.expLo
      rw [Int.toNat_of_nonpos h0.le]; exact sqIter_zero _ _
    rw [this]; simp; exact (Real.exp_pos _).le

lemma cast_sub_ge (a b : ℕ) : (a : ℝ) - b ≤ ((a - b : ℕ) : ℝ) := by
  rcases le_total b a with h | h
  · rw [Nat.cast_sub h]
  · rw [Nat.sub_eq_zero_of_le h]; simp; exact_mod_cast h

lemma S_cast : ((S : ℕ) : ℝ) = 2 ^ 48 := by unfold S; push_cast; ring

def MLR (n : ℕ) : ℕ := Nat.sqrt (6 * n * (4 * 1600 + 6 * n) * 2 ^ 96)
def MLSlo (n : ℕ) : ℕ := ((2 * 1600 + 6 * n) * S + MLR n) / (2 * 1600)
def MLShi (n : ℕ) : ℕ := ((2 * 1600 + 6 * n) * S + MLR n + 1) / (2 * 1600) + 1
def MLX (n : ℕ) : ℤ := -((n * (19 * MLShi n - 25 * S) * S : ℕ) : ℤ) / ((1600 * (MLShi n - S) : ℕ) : ℤ)
def ML (n : ℕ) : ℕ := 19 * MLSlo n * expLo (MLX n) / (25 * S)

lemma EL_le' (n : ℕ) : ((EL n : ℕ) : ℝ) / 2 ^ 48 ≤ Real.exp (-((n : ℝ) / 64)) :=
  expLo_le_gen (le_of_eq (by push_cast; ring))

lemma ML_core (n R Slo Shi : ℕ) (X : ℤ) (hn0 : 0 < n) (hu : 6 * 64 ≤ 19 * n)
    (hR1 : (R : ℝ) ^ 2 ≤ 6 * n * (6400 + 6 * n) * 2 ^ 96)
    (hR2 : 6 * (n : ℝ) * (6400 + 6 * n) * 2 ^ 96 < ((R : ℝ) + 1) ^ 2)
    (hSlo : (Slo : ℝ) * 3200 ≤ (3200 + 6 * n) * 2 ^ 48 + R)
    (hShi : (3200 + 6 * (n : ℝ)) * 2 ^ 48 + R + 1 ≤ Shi * 3200)
    (hX : (X : ℝ) * (1600 * ((Shi : ℝ) - 2 ^ 48)) ≤ -((n : ℝ) * (19 * Shi - 25 * 2 ^ 48) * 2 ^ 48)) :
    ((19 * Slo * expLo X / (25 * S) : ℕ) : ℝ) / 2 ^ 48 ≤ Mt.Mc (19 / 25) ((n : ℝ) / 64) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn0
  have hu' : (6 / 19 : ℝ) ≤ (n : ℝ) / 64 := by
    have : (6 * 64 : ℝ) ≤ 19 * n := by exact_mod_cast hu
    rw [le_div_iff₀ (by norm_num)]; linarith
  have hmax : max ((n : ℝ) / 64) (1 / (19 / 25) - 1) = (n : ℝ) / 64 := by
    apply max_eq_left; norm_num; linarith
  unfold Mt.Mc; rw [hmax]; unfold Mt.Mf Mt.phi
  set x : ℝ := 2 + (1 - 19 / 25) * ((n : ℝ) / 64) with hx
  set σ := √(x ^ 2 - 4) with hσ
  have hsq : x ^ 2 - 4 = 6 * n * (6400 + 6 * n) / 1600 ^ 2 := by rw [hx]; ring
  have hpos : 0 ≤ x ^ 2 - 4 := by rw [hsq]; positivity
  have hp : (0 : ℝ) < 2 ^ 48 := by positivity
  have hA : (R : ℝ) / (2 ^ 48 * 1600) ≤ σ := by
    apply Real.le_sqrt_of_sq_le
    rw [hsq, div_pow, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  have hB : σ < ((R : ℝ) + 1) / (2 ^ 48 * 1600) := by
    rw [hσ, Real.sqrt_lt' (by positivity), hsq, div_pow, div_lt_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  have hSr : Mt.Sr (19 / 25) ((n : ℝ) / 64) = (x + σ) / 2 := rfl
  rw [hSr]
  set Sr := (x + σ) / 2 with hSrd
  have hσ0 : 0 ≤ σ := Real.sqrt_nonneg _
  have hx2 : 2 < x := by rw [hx]; nlinarith
  have hSr1 : 1 < Sr := by rw [hSrd]; linarith
  have hlo : (Slo : ℝ) / 2 ^ 48 ≤ Sr := by
    rw [hSrd, div_le_iff₀ hp]
    have : (R : ℝ) ≤ σ * (2 ^ 48 * 1600) := by rwa [div_le_iff₀ (by positivity)] at hA
    rw [hx]; nlinarith
  have hhi : Sr ≤ (Shi : ℝ) / 2 ^ 48 := by
    rw [hSrd, le_div_iff₀ hp]
    have : σ * (2 ^ 48 * 1600) < (R : ℝ) + 1 := by rwa [lt_div_iff₀ (by positivity)] at hB
    rw [hx]; nlinarith
  set Sh := (Shi : ℝ) / 2 ^ 48 with hShd
  have hSh1 : 1 < Sh := lt_of_lt_of_le hSr1 hhi
  have hShi' : (Shi : ℝ) = Sh * 2 ^ 48 := by rw [hShd]; field_simp
  -- exponent bound
  have hXe : (X : ℝ) / 2 ^ 48 ≤ -((n : ℝ) / 64 * ((19 / 25 * Sr - 1) / (Sr - 1))) := by
    rw [hShi'] at hX
    have hd : 0 < 1600 * (Sh * 2 ^ 48 - 2 ^ 48) := by nlinarith
    have h1 : (X : ℝ) / 2 ^ 48 ≤ -((n : ℝ) * (19 * Sh - 25) / (1600 * (Sh - 1))) := by
      rw [div_le_iff₀ hp]
      have h2 : (X : ℝ) ≤ -((n : ℝ) * (19 * (Sh * 2 ^ 48) - 25 * 2 ^ 48) * 2 ^ 48) / (1600 * (Sh * 2 ^ 48 - 2 ^ 48)) := by
        rw [le_div_iff₀ hd]; exact hX
      calc (X : ℝ) ≤ _ := h2
        _ = _ := by field_simp
    refine h1.trans ?_
    rw [neg_le_neg_iff]
    have e1 : (n : ℝ) / 64 * ((19 / 25 * Sr - 1) / (Sr - 1)) = (n : ℝ) * (19 * Sr - 25) / (1600 * (Sr - 1)) := by
      field_simp; ring
    have hq1 : 0 < 1600 * (Sr - 1) := by linarith
    have hq2 : 0 < 1600 * (Sh - 1) := by linarith
    rw [e1, div_le_div_iff₀ hq1 hq2]
    have : (19 * Sr - 25) * (Sh - 1) ≤ (19 * Sh - 25) * (Sr - 1) := by linarith
    linear_combination (1600 * (n : ℝ)) * this
  have hE := expLo_le_gen hXe
  -- assemble
  have hc := Nat.cast_div_le (α := ℝ) (m := 19 * Slo * expLo X) (n := 25 * S)
  have hS : ((25 * S : ℕ) : ℝ) = 25 * 2 ^ 48 := by rw [Nat.cast_mul, S_cast]; norm_num
  calc ((19 * Slo * expLo X / (25 * S) : ℕ) : ℝ) / 2 ^ 48
      ≤ ((19 * Slo * expLo X : ℕ) : ℝ) / ((25 * S : ℕ) : ℝ) / 2 ^ 48 := by gcongr
    _ = 19 / 25 * ((Slo : ℝ) / 2 ^ 48) * (((expLo X : ℕ) : ℝ) / 2 ^ 48) := by
        rw [hS]; push_cast; field_simp
    _ ≤ 19 / 25 * Sr * Real.exp (-((n : ℝ) / 64 * ((19 / 25 * Sr - 1) / (Sr - 1)))) := by
        gcongr

lemma ML_le (n : ℕ) (hu : 6 * 64 ≤ 19 * n) :
    ((ML n : ℕ) : ℝ) / 2 ^ 48 ≤ Mt.Mc (19 / 25) ((n : ℝ) / 64) := by
  have hn0 : 0 < n := by omega
  have hR1 := Nat.sqrt_le' (6 * n * (4 * 1600 + 6 * n) * 2 ^ 96)
  have hR2 := Nat.lt_succ_sqrt' (6 * n * (4 * 1600 + 6 * n) * 2 ^ 96)
  have hSlo := Nat.div_mul_le_self ((2 * 1600 + 6 * n) * S + MLR n) (2 * 1600)
  have hShi := Nat.lt_div_mul_add (a := (2 * 1600 + 6 * n) * S + MLR n + 1) (b := 2 * 1600) (by norm_num)
  have hSS : S < MLShi n := by
    unfold MLShi
    have : S ≤ ((2 * 1600 + 6 * n) * S + MLR n + 1) / (2 * 1600) := by
      rw [Nat.le_div_iff_mul_le (by norm_num)]; nlinarith
    omega
  have hd : (0 : ℤ) < ((1600 * (MLShi n - S) : ℕ) : ℤ) := by
    have : 0 < 1600 * (MLShi n - S) := by omega
    exact_mod_cast this
  have hX := Int.ediv_mul_le (-((n * (19 * MLShi n - 25 * S) * S : ℕ) : ℤ)) (ne_of_gt hd)
  have hXr : ((MLX n : ℤ) : ℝ) * (1600 * ((MLShi n : ℝ) - 2 ^ 48))
      ≤ -((n : ℝ) * (19 * MLShi n - 25 * 2 ^ 48) * 2 ^ 48) := by
    have h1 : ((MLX n * ((1600 * (MLShi n - S) : ℕ) : ℤ) : ℤ) : ℝ)
        ≤ ((-((n * (19 * MLShi n - 25 * S) * S : ℕ) : ℤ) : ℤ) : ℝ) := by exact_mod_cast hX
    have hc1 : ((((1600 * (MLShi n - S) : ℕ) : ℤ)) : ℝ) = 1600 * ((MLShi n : ℝ) - 2 ^ 48) := by
      rw [Int.cast_natCast, Nat.cast_mul, Nat.cast_sub hSS.le, S_cast]; norm_num
    have hc2 : (n : ℝ) * (19 * MLShi n - 25 * 2 ^ 48) * 2 ^ 48 ≤ (((n * (19 * MLShi n - 25 * S) * S : ℕ)) : ℝ) := by
      have := cast_sub_ge (19 * MLShi n) (25 * S)
      push_cast at this ⊢
      rw [S_cast] at this ⊢
      have hn' : (0:ℝ) ≤ n := by positivity
      first
        | exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left this hn') (by positivity)
        | gcongr
    rw [Int.cast_mul, hc1, Int.cast_neg, Int.cast_natCast] at h1
    linarith
  apply ML_core n (MLR n) (MLSlo n) (MLShi n) (MLX n) hn0 hu
  · have : ((MLR n ^ 2 : ℕ) : ℝ) ≤ ((6 * n * (4 * 1600 + 6 * n) * 2 ^ 96 : ℕ) : ℝ) := by exact_mod_cast hR1
    push_cast at this; linarith
  · have : ((6 * n * (4 * 1600 + 6 * n) * 2 ^ 96 : ℕ) : ℝ) < (((MLR n + 1) ^ 2 : ℕ) : ℝ) := by
      unfold MLR; exact_mod_cast hR2
    push_cast at this; linarith
  · have : ((MLSlo n * (2 * 1600) : ℕ) : ℝ) ≤ (((2 * 1600 + 6 * n) * S + MLR n : ℕ) : ℝ) := by
      unfold MLSlo; exact_mod_cast hSlo
    push_cast at this; rw [S_cast] at this; linarith
  · have : (((2 * 1600 + 6 * n) * S + MLR n + 1 : ℕ) : ℝ)
        < ((((2 * 1600 + 6 * n) * S + MLR n + 1) / (2 * 1600) * (2 * 1600) + 2 * 1600 : ℕ) : ℝ) := by
      exact_mod_cast hShi
    have e : (MLShi n : ℝ) = ((((2 * 1600 + 6 * n) * S + MLR n + 1) / (2 * 1600) : ℕ) : ℝ) + 1 := by
      unfold MLShi; push_cast; ring
    push_cast at this; rw [S_cast] at this; rw [e]; linarith
  · exact hXr

def NG : ℕ := 768
def sufAux : ℕ → ℕ
  | 0 => 0
  | k + 1 =>
    let m := NG - (k + 1)
    (if EH (m + 1) < EL m ∧ 6 * 2 ^ 6 ≤ 19 * (m + 1) then (EL m - EH (m + 1)) * ML (m + 1) / S else 0) + sufAux k
def SUF (n : ℕ) : ℕ := sufAux (NG - n)

/-- grid `[n/64, (n+1)/64, ..., (n+k)/64]` -/
noncomputable def grid (n : ℕ) : ℕ → List ℝ
  | 0 => [(n : ℝ) / 64]
  | k + 1 => ((n : ℝ) / 64) :: grid (n + 1) k

lemma grid_head (n k : ℕ) : ∃ rest, grid n k = ((n : ℝ) / 64) :: rest := by
  cases k <;> exact ⟨_, rfl⟩

lemma grid_chain : ∀ (k n : ℕ), List.IsChain (· ≤ ·) (grid n k)
  | 0, n => by simp [grid]
  | k + 1, n => by
    obtain ⟨rest, hr⟩ := grid_head (n + 1) k
    have ih := grid_chain k (n + 1)
    simp only [grid]; rw [hr] at ih ⊢
    refine List.IsChain.cons_cons ?_ ih
    push_cast; linarith

lemma Mc_nonneg (u : ℝ) : 0 ≤ Mt.Mc (19 / 25) u := by
  unfold Mt.Mc Mt.Mf Mt.phi
  have hm : (0:ℝ) ≤ max u (1 / (19 / 25) - 1) := le_trans (by norm_num) (le_max_right _ _)
  apply mul_nonneg (mul_nonneg (by norm_num) ?_) (Real.exp_pos _).le
  unfold Mt.Sr
  apply div_nonneg (add_nonneg (by nlinarith) (Real.sqrt_nonneg _)) (by norm_num)

lemma SUF_term (m : ℕ) :
    (((if EH (m + 1) < EL m ∧ 6 * 2 ^ 6 ≤ 19 * (m + 1) then (EL m - EH (m + 1)) * ML (m + 1) / S else 0) : ℕ) : ℝ) / 2 ^ 48
      ≤ Mt.Mc (19 / 25) (((m + 1 : ℕ) : ℝ) / 64) * (Real.exp (-((m : ℝ) / 64)) - Real.exp (-(((m + 1 : ℕ) : ℝ) / 64))) := by
  have hd : 0 ≤ Real.exp (-((m : ℝ) / 64)) - Real.exp (-(((m + 1 : ℕ) : ℝ) / 64)) := by
    rw [sub_nonneg, Real.exp_le_exp]; push_cast; linarith
  split_ifs with h
  · obtain ⟨h1, h2⟩ := h
    have hp : (0:ℝ) < 2 ^ 48 := by positivity
    have hEL := EL_le' m
    have hEH := EH_ge (m + 1)
    have hM := ML_le (m + 1) (by norm_num at h2 ⊢; omega)
    have hc := Nat.cast_div_le (α := ℝ) (m := (EL m - EH (m + 1)) * ML (m + 1)) (n := S)
    have hsub : ((EL m - EH (m + 1) : ℕ) : ℝ) = (EL m : ℝ) - (EH (m + 1) : ℝ) := Nat.cast_sub h1.le
    have hdiff : ((EL m - EH (m + 1) : ℕ) : ℝ) / 2 ^ 48
        ≤ Real.exp (-((m : ℝ) / 64)) - Real.exp (-(((m + 1 : ℕ) : ℝ) / 64)) := by
      rw [hsub, sub_div]; linarith
    have h0 : (0 : ℝ) ≤ ((EL m - EH (m + 1) : ℕ) : ℝ) / 2 ^ 48 := by positivity
    have hM0 : (0 : ℝ) ≤ ((ML (m + 1) : ℕ) : ℝ) / 2 ^ 48 := by positivity
    calc (((EL m - EH (m + 1)) * ML (m + 1) / S : ℕ) : ℝ) / 2 ^ 48
        ≤ (((EL m - EH (m + 1)) * ML (m + 1) : ℕ) : ℝ) / (S : ℝ) / 2 ^ 48 := by gcongr
      _ = (((ML (m + 1) : ℕ) : ℝ) / 2 ^ 48) * (((EL m - EH (m + 1) : ℕ) : ℝ) / 2 ^ 48) := by
          rw [S_cast]; push_cast; ring
      _ ≤ _ := mul_le_mul hM hdiff h0 (Mc_nonneg _)
  · rw [Nat.cast_zero, zero_div]; exact mul_nonneg (Mc_nonneg _) hd

lemma SUF_aux : ∀ (k n : ℕ), n + k = NG →
    ((sufAux k : ℕ) : ℝ) / 2 ^ 48 ≤ Tail.stepSum (Mt.Mc (19 / 25)) (grid n k)
  | 0, n, _ => by simp [sufAux, grid, Tail.stepSum]
  | k + 1, n, h => by
    have hm : NG - (k + 1) = n := by omega
    have ih := SUF_aux k (n + 1) (by omega)
    obtain ⟨rest, hr⟩ := grid_head (n + 1) k
    have ht := SUF_term n
    simp only [sufAux, hm]
    simp only [grid]; rw [hr] at ih ⊢
    simp only [Tail.stepSum]
    push_cast at ht ih ⊢
    rw [add_div]
    linarith

lemma SUF_le (n : ℕ) (hn : n ≤ NG) :
    ((SUF n : ℕ) : ℝ) / 2 ^ 48 ≤ Tail.stepSum (Mt.Mc (19 / 25)) (grid n (NG - n)) :=
  SUF_aux (NG - n) n (by omega)


/-! ## S11: checker over the Chk defs (with guards) + soundness `cell_nums` -/

def thn (j : ℕ) : ℕ := (393216 + 19 * j - 1) / (19 * j)
def kd : ℕ := 25 * 2 ^ 21
def eK (i0 j0 j1 : ℕ) : ℕ := ETU j1 * TU (19 * i0 * j0 * tn j1) (25 * 2 ^ 41) / S + 1
def GLz (i0 j0 j1 : ℕ) : ℤ :=
  ((((S * ((kd + 19 * i0 * j0) * 1024 + j0 * kd) * 2 ^ 20 : ℕ) : ℤ)
    - ((eK i0 j0 j1 * ((kd + 19 * i0 * j0) * (2 ^ 30 + j0 * tn j1) + j0 * kd * 2 ^ 20) : ℕ) : ℤ))
    * (kd : ℤ)) / (((kd + 19 * i0 * j0) * (kd + 19 * i0 * j0) * 2 ^ 30 : ℕ) : ℤ)
def G1Lof (i0 : ℕ) (g : ℤ) : ℕ := 19 * GA i0 * g.toNat / (25 * S)
def psiL (i0 j0 j1 : ℕ) : ℕ :=
  19 * (2 ^ 30 + j0 * tn j1) * TL (i0 * (6 * 2 ^ 30 - 19 * j0 * tn j1)) (25 * 2 ^ 41) / (25 * 2 ^ 30)

def chk (i0 i1 j0 j1 : ℕ) : Bool :=
  if ¬ (i0 ≤ i1 ∧ i1 ≤ 2048 ∧ j0 < j1 ∧ j1 ≤ 1024 ∧ 0 < tn j1) then false else
  let g := GLz i0 j0 j1
  if g < 0 then false
  else if j0 = 0 then
    decide (644001 * S * S * S ≤ 1000000 * (EA i0 * S * S + XA i1 * (G1Lof i0 g * S)))
  else if ¬ (6 * 2 ^ 16 ≤ 19 * j0 * thn j0 ∧ tn j1 * 64 ≤ thn j0 * 2 ^ 20 ∧ 6 * 64 ≤ 19 * thn j0) then false
  else if NG < thn j0 then
    decide (644001 * S * S * S ≤ 1000000 * (EA i0 * S * S + XA i1 * (G1Lof i0 g * S)))
  else if 25 * 2 ^ 30 < 19 * (2 ^ 30 + j0 * tn j1) then false
  else if ET j1 < EH (thn j0) then false
  else decide (644001 * S * S * S ≤ 1000000 * (EA i0 * S * S + XA i1 * (G1Lof i0 g * S
      + (ET j1 - EH (thn j0)) * min (psiL i0 j0 j1) (ML (thn j0)) + SUF (thn j0) * S)))

noncomputable def Gx (γ a0 s0 T : ℝ) : ℝ :=
  γ * exp (a0 * (1 - γ)) * (((a0 * γ * s0 + 1) * 1 + s0) / (a0 * γ * s0 + 1) ^ 2
        - exp (-(a0 * γ * s0 + 1) * T) * ((a0 * γ * s0 + 1) * (1 + s0 * T) + s0)
          / (a0 * γ * s0 + 1) ^ 2)

noncomputable def Px (γ a0 s0 T m : ℝ) : ℝ :=
  min (γ * min (1 + s0 * T) (1 / γ) * exp (a0 * (1 - γ * min (1 + s0 * T) (1 / γ)))) m

lemma natdiv_ge (a b : ℕ) (hb : 0 < b) : (a : ℝ) / b ≤ ((a / b : ℕ) : ℝ) + 1 := by
  have h1 := Nat.div_add_mod a b
  have h2 := Nat.mod_lt a hb
  have e1 : (a : ℝ) = (b : ℝ) * ((a / b : ℕ) : ℝ) + ((a % b : ℕ) : ℝ) := by exact_mod_cast h1.symm
  have e2 : ((a % b : ℕ) : ℝ) < b := by exact_mod_cast h2
  have hb' : (0 : ℝ) < b := by exact_mod_cast hb
  rw [div_le_iff₀ hb']
  nlinarith

lemma eK_ge (i0 j0 j1 : ℕ) :
    Real.exp (-((i0 : ℝ) / 2048 * (19 / 25) * ((j0 : ℝ) / 1024) + 1) * ((tn j1 : ℝ) / 2 ^ 20))
      ≤ ((eK i0 j0 j1 : ℕ) : ℝ) / 2 ^ 48 := by
  have h1 := ETU_ge j1
  have h2 := TU_ge (19 * i0 * j0 * tn j1) (25 * 2 ^ 41) (by positivity)
  have hsplit : -((i0 : ℝ) / 2048 * (19 / 25) * ((j0 : ℝ) / 1024) + 1) * ((tn j1 : ℝ) / 2 ^ 20)
      = -((tn j1 : ℝ) / 2 ^ 20)
        + -(((19 * i0 * j0 * tn j1 : ℕ) : ℝ) / ((25 * 2 ^ 41 : ℕ) : ℝ)) := by
    push_cast; ring
  rw [hsplit, Real.exp_add]
  have hd := natdiv_ge (ETU j1 * TU (19 * i0 * j0 * tn j1) (25 * 2 ^ 41)) S (by unfold S; positivity)
  rw [S_cast, Nat.cast_mul] at hd
  have hq : ((eK i0 j0 j1 : ℕ) : ℝ)
      = ((ETU j1 * TU (19 * i0 * j0 * tn j1) (25 * 2 ^ 41) / S : ℕ) : ℝ) + 1 := by
    unfold eK; rw [Nat.cast_succ]
  rw [hq]
  have hETU0 : (0 : ℝ) ≤ ((ETU j1 : ℕ) : ℝ) / 2 ^ 48 := by positivity
  calc Real.exp (-((tn j1 : ℝ) / 2 ^ 20))
        * Real.exp (-(((19 * i0 * j0 * tn j1 : ℕ) : ℝ) / ((25 * 2 ^ 41 : ℕ) : ℝ)))
      ≤ ((ETU j1 : ℕ) : ℝ) / 2 ^ 48 * (((TU (19 * i0 * j0 * tn j1) (25 * 2 ^ 41) : ℕ) : ℝ) / 2 ^ 48) :=
        mul_le_mul h1 h2 (Real.exp_pos _).le hETU0
    _ = ((ETU j1 : ℕ) : ℝ) * ((TU (19 * i0 * j0 * tn j1) (25 * 2 ^ 41) : ℕ) : ℝ) / 2 ^ 48 / 2 ^ 48 := by
        ring
    _ ≤ (((ETU j1 * TU (19 * i0 * j0 * tn j1) (25 * 2 ^ 41) / S : ℕ) : ℝ) + 1) / 2 ^ 48 := by
        gcongr

lemma bracket_eq (kn kd j0 t E : ℝ) (hkd : kd ≠ 0) (hkn : kn ≠ 0) :
    ((kn / kd) * 1 + j0 / 1024) / (kn / kd) ^ 2
      - E * ((kn / kd) * (1 + j0 / 1024 * (t / 2 ^ 20)) + j0 / 1024) / (kn / kd) ^ 2
    = kd * ((kn * 1024 + j0 * kd) * 2 ^ 20 - E * (kn * (2 ^ 30 + j0 * t) + j0 * kd * 2 ^ 20))
      / (kn * kn * 2 ^ 30) := by
  field_simp
  ring

lemma GL_sound (i0 j0 j1 : ℕ) :
    ((GLz i0 j0 j1 : ℤ) : ℝ) / 2 ^ 48 ≤
      (((i0 : ℝ) / 2048 * (19 / 25) * ((j0 : ℝ) / 1024) + 1) * 1 + (j0 : ℝ) / 1024)
        / ((i0 : ℝ) / 2048 * (19 / 25) * ((j0 : ℝ) / 1024) + 1) ^ 2
      - Real.exp (-((i0 : ℝ) / 2048 * (19 / 25) * ((j0 : ℝ) / 1024) + 1) * ((tn j1 : ℝ) / 2 ^ 20))
        * (((i0 : ℝ) / 2048 * (19 / 25) * ((j0 : ℝ) / 1024) + 1)
            * (1 + (j0 : ℝ) / 1024 * ((tn j1 : ℝ) / 2 ^ 20)) + (j0 : ℝ) / 1024)
        / ((i0 : ℝ) / 2048 * (19 / 25) * ((j0 : ℝ) / 1024) + 1) ^ 2 := by
  have hE := eK_ge i0 j0 j1
  have hD : (0 : ℤ) < (((kd + 19 * i0 * j0) * (kd + 19 * i0 * j0) * 2 ^ 30 : ℕ) : ℤ) := by
    unfold kd; positivity
  have hdiv : GLz i0 j0 j1 * (((kd + 19 * i0 * j0) * (kd + 19 * i0 * j0) * 2 ^ 30 : ℕ) : ℤ) ≤
      ((((S * ((kd + 19 * i0 * j0) * 1024 + j0 * kd) * 2 ^ 20 : ℕ) : ℤ)
      - ((eK i0 j0 j1 * ((kd + 19 * i0 * j0) * (2 ^ 30 + j0 * tn j1) + j0 * kd * 2 ^ 20) : ℕ) : ℤ))
      * (kd : ℤ)) := by
    unfold GLz; exact Int.ediv_mul_le _ hD.ne'
  have hR := (Int.cast_le (R := ℝ)).2 hdiv
  push_cast at hR
  simp only [S_cast] at hR
  have hk : (i0 : ℝ) / 2048 * (19 / 25) * ((j0 : ℝ) / 1024) + 1
      = ((kd : ℝ) + 19 * i0 * j0) / (kd : ℝ) := by
    unfold kd; push_cast; field_simp; ring
  have hkd0 : (0 : ℝ) < kd := by unfold kd; positivity
  have hkn0 : (0 : ℝ) < (kd : ℝ) + 19 * i0 * j0 := by positivity
  rw [hk] at hE ⊢
  rw [bracket_eq _ _ _ _ _ hkd0.ne' hkn0.ne']
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have hQ : (0 : ℝ) ≤ ((kd : ℝ) + 19 * i0 * j0) * (2 ^ 30 + j0 * tn j1) + j0 * kd * 2 ^ 20 := by
    positivity
  have hEQ := mul_le_mul_of_nonneg_right hE (mul_nonneg hQ hkd0.le)
  nlinarith [hR, hEQ]

lemma G1L_sound (i0 j0 j1 : ℕ) (hg : 0 ≤ GLz i0 j0 j1) :
    ((G1Lof i0 (GLz i0 j0 j1) : ℕ) : ℝ) / 2 ^ 48
      ≤ Gx (19 / 25) ((i0 : ℝ) / 2048) ((j0 : ℝ) / 1024) ((tn j1 : ℝ) / 2 ^ 20) := by
  have hGL := GL_sound i0 j0 j1
  have hGA := GA_le i0
  have hgR : (0 : ℝ) ≤ ((GLz i0 j0 j1 : ℤ) : ℝ) := by exact_mod_cast hg
  have htn : (((GLz i0 j0 j1).toNat : ℕ) : ℝ) = ((GLz i0 j0 j1 : ℤ) : ℝ) := by
    rw [← Int.cast_natCast, Int.toNat_of_nonneg hg]
  have h1 := (Nat.cast_div_le (α := ℝ) (m := 19 * GA i0 * (GLz i0 j0 j1).toNat) (n := 25 * S))
  simp only [Nat.cast_mul, Nat.cast_ofNat, htn, S_cast] at h1
  unfold Gx
  have he : (i0 : ℝ) / 2048 * (1 - 19 / 25) = (i0 : ℝ) / 2048 * (6 / 25) := by norm_num
  rw [he]
  calc ((G1Lof i0 (GLz i0 j0 j1) : ℕ) : ℝ) / 2 ^ 48
      ≤ (19 * ((GA i0 : ℕ) : ℝ) * ((GLz i0 j0 j1 : ℤ) : ℝ) / (25 * 2 ^ 48)) / 2 ^ 48 := by
        unfold G1Lof; gcongr
    _ = 19 / 25 * (((GA i0 : ℕ) : ℝ) / 2 ^ 48) * (((GLz i0 j0 j1 : ℤ) : ℝ) / 2 ^ 48) := by ring
    _ ≤ _ := mul_le_mul (mul_le_mul_of_nonneg_left hGA (by norm_num)) hGL
        (div_nonneg hgR (by positivity)) (by positivity)

lemma dL_sound (j1 n : ℕ) (h : EH n ≤ ET j1) :
    ((ET j1 - EH n : ℕ) : ℝ) / 2 ^ 48
      ≤ Real.exp (-((tn j1 : ℝ) / 2 ^ 20)) - Real.exp (-((n : ℝ) / 64)) := by
  rw [Nat.cast_sub h, sub_div]
  linarith [ET_le j1, EH_ge n]

lemma psiL_sound (i0 j0 j1 : ℕ) (h : 19 * (2 ^ 30 + j0 * tn j1) ≤ 25 * 2 ^ 30) :
    ((psiL i0 j0 j1 : ℕ) : ℝ) / 2 ^ 48 ≤
      19 / 25 * min (1 + (j0 : ℝ) / 1024 * ((tn j1 : ℝ) / 2 ^ 20)) (1 / (19 / 25))
      * Real.exp ((i0 : ℝ) / 2048
          * (1 - 19 / 25 * min (1 + (j0 : ℝ) / 1024 * ((tn j1 : ℝ) / 2 ^ 20)) (1 / (19 / 25)))) := by
  have hle : 19 * j0 * tn j1 ≤ 6 * 2 ^ 30 := by nlinarith [h]
  have hR : (19 : ℝ) * (2 ^ 30 + j0 * tn j1) ≤ 25 * 2 ^ 30 := by exact_mod_cast h
  have hmin : min (1 + (j0 : ℝ) / 1024 * ((tn j1 : ℝ) / 2 ^ 20)) (1 / (19 / 25))
      = 1 + (j0 : ℝ) / 1024 * ((tn j1 : ℝ) / 2 ^ 20) := by
    apply min_eq_left
    rw [le_div_iff₀ (by norm_num)]
    linarith
  rw [hmin]
  have hTL := TL_le (i0 * (6 * 2 ^ 30 - 19 * j0 * tn j1)) (25 * 2 ^ 41) (by positivity)
  have harg : (((i0 * (6 * 2 ^ 30 - 19 * j0 * tn j1) : ℕ) : ℝ) / ((25 * 2 ^ 41 : ℕ) : ℝ))
      = (i0 : ℝ) / 2048 * (1 - 19 / 25 * (1 + (j0 : ℝ) / 1024 * ((tn j1 : ℝ) / 2 ^ 20))) := by
    rw [Nat.cast_mul, Nat.cast_sub hle]; push_cast; ring
  rw [harg] at hTL
  have h1 := (Nat.cast_div_le (α := ℝ)
    (m := 19 * (2 ^ 30 + j0 * tn j1) * TL (i0 * (6 * 2 ^ 30 - 19 * j0 * tn j1)) (25 * 2 ^ 41))
    (n := 25 * 2 ^ 30))
  unfold psiL
  calc _ ≤ (((19 * (2 ^ 30 + j0 * tn j1) * TL (i0 * (6 * 2 ^ 30 - 19 * j0 * tn j1)) (25 * 2 ^ 41) : ℕ) : ℝ)
          / ((25 * 2 ^ 30 : ℕ) : ℝ)) / 2 ^ 48 := by gcongr
    _ = 19 / 25 * (1 + (j0 : ℝ) / 1024 * ((tn j1 : ℝ) / 2 ^ 20))
          * (((TL (i0 * (6 * 2 ^ 30 - 19 * j0 * tn j1)) (25 * 2 ^ 41) : ℕ) : ℝ) / 2 ^ 48) := by
        push_cast; ring
    _ ≤ _ := by gcongr

lemma theta_of (e x g d p u : ℕ)
    (h : 644001 * S * S * S ≤ 1000000 * (e * S * S + x * (g * S + d * p + u * S))) :
    (644001 / 1000000 : ℝ) ≤ (e : ℝ) / 2 ^ 48 + (x : ℝ) / 2 ^ 48 *
      ((g : ℝ) / 2 ^ 48 + (d : ℝ) / 2 ^ 48 * ((p : ℝ) / 2 ^ 48) + (u : ℝ) / 2 ^ 48) := by
  unfold S at h
  have h' : ((644001 * 2 ^ 48 * 2 ^ 48 * 2 ^ 48 : ℕ) : ℝ)
      ≤ ((1000000 * (e * 2 ^ 48 * 2 ^ 48 + x * (g * 2 ^ 48 + d * p + u * 2 ^ 48)) : ℕ) : ℝ) := by
    exact_mod_cast h
  push_cast at h'
  have key : (e : ℝ) / 2 ^ 48 + (x : ℝ) / 2 ^ 48 *
      ((g : ℝ) / 2 ^ 48 + (d : ℝ) / 2 ^ 48 * ((p : ℝ) / 2 ^ 48) + (u : ℝ) / 2 ^ 48)
      = ((e : ℝ) * 2 ^ 48 * 2 ^ 48 + x * (g * 2 ^ 48 + d * p + u * 2 ^ 48)) / ((2 : ℝ) ^ 48) ^ 3 := by
    ring
  rw [key, le_div_iff₀ (by positivity)]
  linarith

lemma theta0 (e x g : ℕ)
    (h : 644001 * S * S * S ≤ 1000000 * (e * S * S + x * (g * S))) :
    (644001 / 1000000 : ℝ) ≤ (e : ℝ) / 2 ^ 48 + (x : ℝ) / 2 ^ 48 * ((g : ℝ) / 2 ^ 48) := by
  have := theta_of e x g 0 0 0 (by simpa using h)
  simpa using this

lemma chk_guard {i0 i1 j0 j1 : ℕ} (h : chk i0 i1 j0 j1 = true) :
    (i0 ≤ i1 ∧ i1 ≤ 2048 ∧ j0 < j1 ∧ j1 ≤ 1024 ∧ 0 < tn j1) ∧ 0 ≤ GLz i0 j0 j1 := by
  unfold chk at h
  try dsimp only at h
  split_ifs at h with hA hB
  all_goals first
    | exact ⟨by simpa using hA, by simpa using hB⟩
    | exact absurd h Bool.false_ne_true

lemma chk_noGap {i0 i1 j0 j1 : ℕ} (h : chk i0 i1 j0 j1 = true) (hc : j0 = 0 ∨ NG < thn j0) :
    644001 * S * S * S ≤ 1000000 * (EA i0 * S * S + XA i1 * (G1Lof i0 (GLz i0 j0 j1) * S)) := by
  unfold chk at h
  try dsimp only at h
  split_ifs at h <;> first
    | (exfalso; omega)
    | exact of_decide_eq_true h
    | exact absurd h Bool.false_ne_true

lemma chk_thn {i0 i1 j0 j1 : ℕ} (h : chk i0 i1 j0 j1 = true) (hj : j0 ≠ 0) :
    6 * 2 ^ 16 ≤ 19 * j0 * thn j0 ∧ tn j1 * 64 ≤ thn j0 * 2 ^ 20 ∧ 6 * 64 ≤ 19 * thn j0 := by
  unfold chk at h
  try dsimp only at h
  split_ifs at h with hA hB hC <;> first
    | (exfalso; omega)
    | simpa using hC
    | exact absurd h Bool.false_ne_true

lemma chk_full {i0 i1 j0 j1 : ℕ} (h : chk i0 i1 j0 j1 = true) (hj : j0 ≠ 0) (hn : thn j0 ≤ NG) :
    19 * (2 ^ 30 + j0 * tn j1) ≤ 25 * 2 ^ 30 ∧ EH (thn j0) ≤ ET j1 ∧
    644001 * S * S * S ≤ 1000000 * (EA i0 * S * S + XA i1 * (G1Lof i0 (GLz i0 j0 j1) * S
      + (ET j1 - EH (thn j0)) * min (psiL i0 j0 j1) (ML (thn j0)) + SUF (thn j0) * S)) := by
  unfold chk at h
  try dsimp only at h
  split_ifs at h with hA hB hC hD hE hF <;> first
    | (exfalso; omega)
    | exact ⟨not_lt.1 hE, not_lt.1 hF, of_decide_eq_true h⟩
    | exact absurd h Bool.false_ne_true

set_option maxHeartbeats 1000000 in
theorem cell_nums {i0 i1 j0 j1 : ℕ} (h : chk i0 i1 j0 j1 = true) :
    i0 ≤ i1 ∧ i1 ≤ 2048 ∧ j0 < j1 ∧ j1 ≤ 1024 ∧ 0 < tn j1 ∧
    ∃ eL gL xL : ℝ, eL ≤ Pt.Eint (19 / 25) ((i0 : ℝ) / 2048) ∧
      gL ≤ Gx (19 / 25) ((i0 : ℝ) / 2048) ((j0 : ℝ) / 1024) ((tn j1 : ℝ) / 2 ^ 20) ∧ 0 ≤ gL ∧
      xL ≤ Real.exp (-((i1 : ℝ) / 2048)) ∧ 0 ≤ xL ∧
      ((j0 = 0 ∧ (644001 / 1000000 : ℝ) ≤ eL + xL * gL) ∨
       (0 < j0 ∧ 6 / 19 ≤ (j0 : ℝ) / 1024 * ((thn j0 : ℝ) / 64) ∧
        (tn j1 : ℝ) / 2 ^ 20 ≤ (thn j0 : ℝ) / 64 ∧
        ∃ (dL pL tL : ℝ) (rest : List ℝ), List.IsChain (· ≤ ·) (((thn j0 : ℝ) / 64) :: rest) ∧
          dL ≤ Real.exp (-((tn j1 : ℝ) / 2 ^ 20)) - Real.exp (-((thn j0 : ℝ) / 64)) ∧ 0 ≤ dL ∧
          pL ≤ Px (19 / 25) ((i0 : ℝ) / 2048) ((j0 : ℝ) / 1024) ((tn j1 : ℝ) / 2 ^ 20)
            (Mt.Mc (19 / 25) ((thn j0 : ℝ) / 64)) ∧ 0 ≤ pL ∧
          tL ≤ Tail.stepSum (Mt.Mc (19 / 25)) (((thn j0 : ℝ) / 64) :: rest) ∧ 0 ≤ tL ∧
          (644001 / 1000000 : ℝ) ≤ eL + xL * (gL + dL * pL + tL))) := by
  obtain ⟨⟨hii, hi1, hj01, hj1, htn⟩, hg⟩ := chk_guard h
  refine ⟨hii, hi1, hj01, hj1, htn, ((EA i0 : ℕ) : ℝ) / 2 ^ 48,
    ((G1Lof i0 (GLz i0 j0 j1) : ℕ) : ℝ) / 2 ^ 48, ((XA i1 : ℕ) : ℝ) / 2 ^ 48,
    EA_le i0 (by omega), G1L_sound i0 j0 j1 hg, by positivity, XA_le i1 (by omega), by positivity, ?_⟩
  by_cases hj0 : j0 = 0
  · exact Or.inl ⟨hj0, theta0 _ _ _ (chk_noGap h (Or.inl hj0))⟩
  right
  obtain ⟨g1, g2, g3⟩ := chk_thn h hj0
  have hjpos : 0 < j0 := Nat.pos_of_ne_zero hj0
  have hTh : (6 : ℝ) / 19 ≤ (j0 : ℝ) / 1024 * ((thn j0 : ℝ) / 64) := by
    have : ((6 * 2 ^ 16 : ℕ) : ℝ) ≤ ((19 * j0 * thn j0 : ℕ) : ℝ) := by exact_mod_cast g1
    push_cast at this
    nlinarith
  have hTT : (tn j1 : ℝ) / 2 ^ 20 ≤ (thn j0 : ℝ) / 64 := by
    have : ((tn j1 * 64 : ℕ) : ℝ) ≤ ((thn j0 * 2 ^ 20 : ℕ) : ℝ) := by exact_mod_cast g2
    push_cast at this
    rw [div_le_div_iff₀ (by norm_num) (by norm_num)]
    linarith
  refine ⟨hjpos, hTh, hTT, ?_⟩
  by_cases hn : NG < thn j0
  · refine ⟨0, 0, 0, [], by simp, ?_, le_rfl, ?_, le_rfl, by simp [Tail.stepSum], le_rfl, ?_⟩
    · exact sub_nonneg.2 (Real.exp_le_exp.2 (by linarith))
    · unfold Px
      refine le_min ?_ (Mc_nonneg _)
      exact mul_nonneg (mul_nonneg (by norm_num) (le_min (by positivity) (by norm_num)))
        (Real.exp_pos _).le
    · have := theta0 _ _ _ (chk_noGap h (Or.inr hn))
      rw [mul_zero, add_zero, add_zero]
      exact this
  push Not at hn
  obtain ⟨hF, hG, hdec⟩ := chk_full h hj0 hn
  obtain ⟨rest, hr⟩ := grid_head (thn j0) (NG - thn j0)
  have hch := grid_chain (NG - thn j0) (thn j0)
  rw [hr] at hch
  have hsuf := SUF_le (thn j0) hn
  rw [hr] at hsuf
  refine ⟨((ET j1 - EH (thn j0) : ℕ) : ℝ) / 2 ^ 48,
    ((min (psiL i0 j0 j1) (ML (thn j0)) : ℕ) : ℝ) / 2 ^ 48, ((SUF (thn j0) : ℕ) : ℝ) / 2 ^ 48, rest,
    hch, dL_sound j1 _ hG, by positivity, ?_, by positivity, hsuf, by positivity,
    theta_of _ _ _ _ _ _ hdec⟩
  unfold Px
  apply le_min
  · have hm : ((min (psiL i0 j0 j1) (ML (thn j0)) : ℕ) : ℝ) ≤ ((psiL i0 j0 j1 : ℕ) : ℝ) :=
      Nat.cast_le.2 (Nat.min_le_left _ _)
    calc _ ≤ ((psiL i0 j0 j1 : ℕ) : ℝ) / 2 ^ 48 := by gcongr
      _ ≤ _ := psiL_sound i0 j0 j1 hF
  · have hm : ((min (psiL i0 j0 j1) (ML (thn j0)) : ℕ) : ℝ) ≤ ((ML (thn j0) : ℕ) : ℝ) :=
      Nat.cast_le.2 (Nat.min_le_right _ _)
    calc _ ≤ ((ML (thn j0) : ℕ) : ℝ) / 2 ^ 48 := by gcongr
      _ ≤ _ := ML_le _ g3

end PricingSamples.OneSampleMHR.Chk

-- ===== from d95b66c5_cover.lean

/-! S9: tree-cover soundness for the kernel checker (generic in the leaf check `c`). -/
namespace PricingSamples.OneSampleMHR.Cover

/-- Preorder bit-tree walk: bit 0 = leaf (run `c` on the box), bit 1 = split the wider side. -/
def goP (c : ℕ → ℕ → ℕ → ℕ → Bool) : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → Option ℕ
  | 0, _, _, _, _, _ => none
  | f + 1, t, i0, i1, j0, j1 =>
    if t % 2 = 0 then (if c i0 i1 j0 j1 then some (t / 2) else none)
    else if 2 * (j1 - j0) ≤ i1 - i0 then
      match goP c f (t / 2) i0 ((i0 + i1) / 2) j0 j1 with
      | none => none
      | some r => goP c f r ((i0 + i1) / 2) i1 j0 j1
    else
      match goP c f (t / 2) i0 i1 j0 ((j0 + j1) / 2) with
      | none => none
      | some r => goP c f r i0 i1 ((j0 + j1) / 2) j1

lemma goP_sound (c : ℕ → ℕ → ℕ → ℕ → Bool) (Q : ℝ → ℝ → Prop)
    (hc : ∀ i0 i1 j0 j1, c i0 i1 j0 j1 = true → ∀ a σ : ℝ, (i0 : ℝ) / 2048 ≤ a → a ≤ (i1 : ℝ) / 2048 →
      (j0 : ℝ) / 1024 ≤ σ → σ ≤ (j1 : ℝ) / 1024 → Q a σ) :
    ∀ f t i0 i1 j0 j1 r, goP c f t i0 i1 j0 j1 = some r → i0 ≤ i1 → j0 ≤ j1 →
      ∀ a σ : ℝ, (i0 : ℝ) / 2048 ≤ a → a ≤ (i1 : ℝ) / 2048 →
        (j0 : ℝ) / 1024 ≤ σ → σ ≤ (j1 : ℝ) / 1024 → Q a σ := by
  intro f
  induction f with
  | zero => intro t i0 i1 j0 j1 r h; simp [goP] at h
  | succ f ih =>
    intro t i0 i1 j0 j1 r h hi hj a σ ha0 ha1 hs0 hs1
    simp only [goP] at h
    split_ifs at h with h0 hc0 hsp
    · exact hc i0 i1 j0 j1 hc0 a σ ha0 ha1 hs0 hs1
    · split at h
      · simp at h
      · rename_i r1 h1
        have hm0 : i0 ≤ (i0 + i1) / 2 := by omega
        have hm1 : (i0 + i1) / 2 ≤ i1 := by omega
        rcases le_total a ((((i0 + i1) / 2 : ℕ) : ℝ) / 2048) with hl | hl
        · exact ih _ _ _ _ _ _ h1 hm0 hj a σ ha0 hl hs0 hs1
        · exact ih _ _ _ _ _ _ h hm1 hj a σ hl ha1 hs0 hs1
    · split at h
      · simp at h
      · rename_i r1 h1
        have hm0 : j0 ≤ (j0 + j1) / 2 := by omega
        have hm1 : (j0 + j1) / 2 ≤ j1 := by omega
        rcases le_total σ ((((j0 + j1) / 2 : ℕ) : ℝ) / 1024) with hl | hl
        · exact ih _ _ _ _ _ _ h1 hi hm0 a σ ha0 ha1 hs0 hl
        · exact ih _ _ _ _ _ _ h hi hm1 a σ ha0 ha1 hl hs1

end PricingSamples.OneSampleMHR.Cover

namespace PricingSamples.OneSampleMHR.Chk
def TREE : Nat := 2582486257366472707496018525158491279278437198744822284115542940401878736803606785756439325768974221222117821994934297763538844775331311772849477257089111134989231456000477164974563842319472453179326365972730105141716467598157460542410497961004731227257546472118500596728249209956665491262476572944661781859308076138130175143314307103531297933318164449732502741080798359006165867369909557737315925035280287155667304487634561837367147412026529662470615378172317476835356838507417101471445758807024904893173675562401290876436659427317601211516346206495140626842503424922029250185400137677047248646318949375585429401049662279230675362509413287489131379103987157337679250503527531079729532249001545439318091217048699763156207557822797711004016048664054919394485538941432543313744712363698409941642504498628849350728249439118286925981034654740499679665558814688933355795302259747824499384369183812875871420050199047894993739642956477691948611345662518506529350051444111653182077099277861544300041784309837052223985225648503854628669815358074815841583528506086063496572977884175644957686976878321976904541899777293778446283287876707345329667088110172947037513202885697142674855908730654303558374422755429497487184736541108566850481370865085963738251478362221275481682316213037651129398950433565866053948885548297631957655686406827002543569568636984808871184082262334831892424567380165611563851436010177830066082511032610229065544013001986475365038361703880217284042983947737748617421230744879346092317949569436694433848944131721775292883762722310948514243637660748846625549137477438474143821971020795738380520492504712698420244224531165339999859051463829787870514492964326239877326808564764580601638100814390024290177478626850743830982762534506403117511020223230813363717326395900054750828618571054778409324242272703529454756347877074213531474940485460604902880075674283003879441488113039103824781043077401154553954401955044341533180625970850389959806188407380846812284778944548050001208591609231383382384323617363556245604338462070236608887726500299442396065825705520147203550378576872199441667161970107353067119580227973593478081047229964671388317165101514600577934982308086640632143683747705281220264363589268353803776888909731022595123882716407020639550595916129100992001223157787798285193421519161724472201580975559055138389830724098057614593964749380942075905423571982164378079489103100621191909420307970777765522658191684958803397893826024860627115496673988569360920486646602468423137172641435675995036686073455116345045222616936709357119296357443396723087998798146918704029373293910147994872289232113630389670247145507350669706991058326359561915684456800008346570886203718676091521630369713085265374795465571215745845734143044964236630011770551278172697767502577498757245301746219071715827996073091798788439787748370479041084705616094249440644855011834153505483701418341264105427245238173803495575970541864536318903303737166204020476184939130791184948277897751842837097767780373955204766877930663464746654974376738891004228196855956270799343687674646027754657893904094179512370633124530029804981541160176547346406411261302794549086436256906091065530494533241036569827033170634671875904499464403157344410134717592180146253014747083412628537867514931466703819382284042080995296437776707997346721078528581861615296418678276914652750596528061537811737207136583959809283946264477120033032692623680223968917577805196227247212789527685307284793279174602870560809743148022524789757996302426149644162276952059211874728208946243939623870626622737995551527765189955096443147827460155977949345801421723276941771269751792783942834557183894419018349549714899647893115126306749611041039580200017143265119832267360011222519077376942875556361179334135283302682252578212057472112624837892259552083423710851858078711223350487078676685295094888609114114000839970024258742031803164242603897777865930153329385788188218912273991424537190703056493686599049409352296260826177548414635992100218107754910878012637033250956272510446199668994557154408638953688794759095129620709490725845363094519639169094734056511078314383891271049518857164290379909294317006251905984202088559346610633544559096146519063240555730220251298830819383642306003462705564876641234432462122763132131933916878510321227059015994727401511643576957070689950809578585199597915454007705128577637679044228236028315672074567661642490649776498508910953287863970816420065063011605051927716888388599464325676015147425656559034407404412762844803306933851710828521308922305714450896191033397889134991620199929555623975241614609346208911685194506263161760366313155865741113224638052076379147832934368230443072988877306759842039630890062576236297926731870992307471414328269375074128045847693401622460972274709284517401330647442709617689424266078490218407912435123983947871102483064319769881569351521687881020709724335377541449305745561906555670672285809688546885062490901057055715969246599318443852010477439602148833179683609889080437047707139259452746422064298409756121900314597156891241530156754966118828527364218281057934284985413321557463331310129814607172271758594087439999389896800403883800724219911662102468806391621232170532688651642806638715854007015797230458283974512847277676822555736524990620113750347275161637093272177613467680542847061652888639036666437585842930015145826847079359645509010386783768529032652415
end PricingSamples.OneSampleMHR.Chk

theorem cert_ok : (PricingSamples.OneSampleMHR.Cover.goP PricingSamples.OneSampleMHR.Chk.chk 40 PricingSamples.OneSampleMHR.Chk.TREE 0 2048 0 1024).isSome = true := by decide +kernel

namespace PricingSamples.OneSampleMHR.Fin

open Real MeasureTheory
open PricingSamples.OneSampleMHR.Pt2 (PsiF)

/-- What one certified cell gives for a point `(a, σ)` of it. -/
def Q (a σ : ℝ) : Prop :=
  ∃ a0 s0 T Th : ℝ, 0 ≤ a0 ∧ a0 ≤ a ∧ 0 ≤ s0 ∧ s0 ≤ σ ∧ 0 < T ∧ T * σ ≤ 6 / 19 ∧
    (0 < s0 → 6 / 19 ≤ s0 * Th) ∧ 6 / 19 ≤ Th ∧ a0 ≤ 1 ∧ s0 * T ≤ 6 / 19 ∧
    ∀ A : ℝ, 0 < A → A ≤ 1 → -Real.log A = a →
      (644001 / 1000000 : ℝ) * A ≤
        ∫ q in Set.Icc (0 : ℝ) 1, PsiF (19 / 25) A a0 s0 T Th (Mt.Mc (19 / 25)) q

lemma hbdd {A a0 s0 T Th : ℝ} (hA0 : 0 < A) (hA1 : A ≤ 1) (ha0 : 0 ≤ a0) (ha01 : a0 ≤ 1)
    (hs0 : 0 ≤ s0) (hT : 0 ≤ T) (hsT : s0 * T ≤ 6 / 19) :
    ∀ q, |PsiF (19 / 25) A a0 s0 T Th (Mt.Mc (19 / 25)) q| ≤ 3 + 1 := fun q =>
  Pt2.PsiF_bdd (by norm_num) (by norm_num) hA0 hA1 ha0 ha01 hs0 hT (by linarith)
    (fun u => Mt.Mc_bdd (by norm_num) (by norm_num) u) q

lemma cell_Q (i0 i1 j0 j1 : ℕ) (h : Chk.chk i0 i1 j0 j1 = true) (a σ : ℝ)
    (ha0 : (i0 : ℝ) / 2048 ≤ a) (ha1 : a ≤ (i1 : ℝ) / 2048)
    (hs0 : (j0 : ℝ) / 1024 ≤ σ) (hs1 : σ ≤ (j1 : ℝ) / 1024) : Q a σ := by
  unfold Q
  obtain ⟨hii, hi1, hj01, hj1, htn, eL, gL, xL, heL, hgL, hgL0, hxL, hxL0, hcase⟩ :=
    Chk.cell_nums h
  have hσ0 : 0 ≤ σ := le_trans (by positivity) hs0
  have hTpos : (0 : ℝ) < (Chk.tn j1 : ℝ) / 2 ^ 20 := by
    have : (0 : ℝ) < (Chk.tn j1 : ℝ) := by exact_mod_cast htn
    positivity
  have htnb : (Chk.tn j1 : ℝ) * (19 * j1) ≤ 6 * 2 ^ 30 := by
    have : Chk.tn j1 * (19 * j1) ≤ 6 * 2 ^ 30 := by unfold Chk.tn; exact Nat.div_mul_le_self _ _
    exact_mod_cast this
  have hTσ : (Chk.tn j1 : ℝ) / 2 ^ 20 * σ ≤ 6 / 19 := by
    have h1 : (Chk.tn j1 : ℝ) / 2 ^ 20 * σ ≤ (Chk.tn j1 : ℝ) / 2 ^ 20 * ((j1 : ℝ) / 1024) :=
      mul_le_mul_of_nonneg_left hs1 hTpos.le
    have h2 : (Chk.tn j1 : ℝ) / 2 ^ 20 * ((j1 : ℝ) / 1024)
        = (Chk.tn j1 : ℝ) * (19 * j1) / (19 * 2 ^ 30) := by ring
    have h3 : (Chk.tn j1 : ℝ) * (19 * j1) / (19 * 2 ^ 30) ≤ 6 / 19 := by
      rw [div_le_iff₀ (by norm_num)]; linarith
    linarith
  have hi1r : (i1 : ℝ) ≤ 2048 := by exact_mod_cast hi1
  have hiir : (i0 : ℝ) ≤ i1 := by exact_mod_cast hii
  have ha01 : (i0 : ℝ) / 2048 ≤ 1 := by rw [div_le_one (by norm_num)]; linarith
  have ha1g : (i1 : ℝ) / 2048 * (19 / 25) ≤ 1 := by
    have : (i1 : ℝ) / 2048 ≤ 1 := by rw [div_le_one (by norm_num)]; linarith
    linarith
  have hsT : ∀ s0 : ℝ, 0 ≤ s0 → s0 ≤ σ → s0 * ((Chk.tn j1 : ℝ) / 2 ^ 20) ≤ 6 / 19 := by
    intro s0 _ hs0σ
    have := mul_le_mul_of_nonneg_right hs0σ hTpos.le
    linarith
  rcases hcase with ⟨hj0, hθ⟩ |
      ⟨hj0, hTh, hTTh, dL, pL, tL, rest, hch, hdL, hdL0, hpL, hpL0, htL, htL0, hθ⟩
  · subst hj0
    simp only [Nat.cast_zero, zero_div] at hgL
    refine ⟨(i0 : ℝ) / 2048, 0, (Chk.tn j1 : ℝ) / 2 ^ 20, (Chk.tn j1 : ℝ) / 2 ^ 20 + 1,
      by positivity, ha0, le_rfl, hσ0, hTpos, hTσ, fun h => absurd h (lt_irrefl 0),
      by linarith, ha01, by norm_num, ?_⟩
    intro A hA0 hA1 hAa
    exact Asm.cell_bound0 (Pt2.PsiF_meas (Mt.Mc_meas _))
      (hbdd hA0 hA1 (by positivity) ha01 le_rfl hTpos.le (by norm_num))
      (by norm_num) hA0 hA1 hTpos (by linarith) (by positivity) (by rw [hAa]; exact ha0)
      (by rw [hAa]; exact ha1) ha1g heL hgL hgL0 hxL hxL0 hθ
  · have hj0r : (0 : ℝ) < (j0 : ℝ) / 1024 := by
      have : (0 : ℝ) < j0 := by exact_mod_cast hj0
      positivity
    have hσ1 : σ ≤ 1 := le_trans hs1 (by
      rw [div_le_one (by norm_num)]; exact_mod_cast hj1)
    have hThr : (0 : ℝ) ≤ (Chk.thn j0 : ℝ) / 64 := by positivity
    have hTh' : 6 / 19 ≤ (Chk.thn j0 : ℝ) / 64 := by
      have hs01 : (j0 : ℝ) / 1024 ≤ 1 := le_trans hs0 hσ1
      have := mul_le_mul_of_nonneg_right hs01 hThr
      linarith
    refine ⟨(i0 : ℝ) / 2048, (j0 : ℝ) / 1024, (Chk.tn j1 : ℝ) / 2 ^ 20, (Chk.thn j0 : ℝ) / 64,
      by positivity, ha0, hj0r.le, hs0, hTpos, hTσ, fun _ => hTh, hTh', ha01,
      hsT _ hj0r.le hs0, ?_⟩
    intro A hA0 hA1 hAa
    exact Asm.cell_bound (Pt2.PsiF_meas (Mt.Mc_meas _))
      (hbdd hA0 hA1 (by positivity) ha01 hj0r.le hTpos.le (hsT _ hj0r.le hs0))
      (by norm_num) hA0 hA1 hTpos hTTh hj0r (by positivity)
      (Mt.Mc_meas _) (fun u => le_trans (Mt.Mc_bdd (by norm_num) (by norm_num) u) (by norm_num))
      Chk.Mc_nonneg (fun u v _ huv => Mt.Mc_anti (by norm_num) (by norm_num) huv) rest hch
      (by positivity) (by rw [hAa]; exact ha0) (by rw [hAa]; exact ha1) ha1g heL hgL hdL hdL0
      hpL hpL0 htL hxL hxL0 (by have := mul_nonneg hdL0 hpL0; linarith) hθ

lemma cover_Q (a σ : ℝ) (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hs0 : 0 ≤ σ) (hs1 : σ ≤ 1) : Q a σ := by
  obtain ⟨r, hr⟩ := Option.isSome_iff_exists.mp cert_ok
  exact Cover.goP_sound Chk.chk Q
    (fun i0 i1 j0 j1 h a σ h1 h2 h3 h4 => cell_Q i0 i1 j0 j1 h a σ h1 h2 h3 h4)
    40 Chk.TREE 0 2048 0 1024 r hr (by norm_num) (by norm_num) a σ
    (by simpa using ha0) (by rw [show ((2048 : ℕ) : ℝ) / 2048 = 1 by norm_num]; exact ha1)
    (by simpa using hs0) (by rw [show ((1024 : ℕ) : ℝ) / 1024 = 1 by norm_num]; exact hs1)

theorem main (μ : Measure ℝ) (hF : InFAlpha 1 μ) :
    (0.644 : ℝ) * opt μ ≤ postRev 0.76 μ := by
  rw [show (0.644 : ℝ) = 161 / 250 by norm_num, show (0.76 : ℝ) = 19 / 25 by norm_num]
  obtain ⟨r, hr0, hr⟩ := Lib.exists_optPrice μ hF
  have hrne : r ≠ 0 := hr0.ne'
  have hoptr := Lib.opt_eq_of_IsOptPrice μ hr
  have hF' := hF
  obtain ⟨⟨hP, -, -, -⟩, ⟨hac, hcv⟩⟩ := hF'
  have := hP
  obtain ⟨f, hf⟩ : ∃ f : ℝ → ℝ, f = fun x => ccdf μ (r * x) := ⟨_, rfl⟩
  have hfx : ∀ x, f x = ccdf μ (r * x) := fun x => by rw [hf]
  have hnn : ∀ v, 0 ≤ f v := fun v => by rw [hfx]; exact Lib.ccdf_nonneg μ _
  have h0 : f 0 = 1 := by rw [hfx, mul_zero]; exact Lib.ccdf_zero μ hF
  have hanti : ∀ u v : ℝ, u ≤ v → f v ≤ f u := fun u v huv => by
    rw [hfx, hfx]; exact Lib.ccdf_antitone μ (mul_le_mul_of_nonneg_left huv hr0.le)
  have hf1 : f 1 = ccdf μ r := by rw [hfx, mul_one]
  have hoptf : ∀ x : ℝ, 0 ≤ x → x * f x ≤ f 1 := by
    intro x hx
    have h : r * x * ccdf μ (r * x) ≤ r * ccdf μ r :=
      isMaxOn_iff.mp hr.2 (r * x) (Set.mem_Ici.mpr (mul_nonneg hr0.le hx))
    rw [hf1, hfx]
    rw [mul_assoc] at h
    exact le_of_mul_le_mul_left h hr0
  have hf1le : f 1 ≤ 1 := by rw [hf1]; exact Lib.ccdf_le_one μ _
  have h1 : 0 < f 1 := by
    have hc := Lib.ccdf_continuous μ hac
    have hev : ∀ᶠ p in nhds (0 : ℝ), (1 : ℝ) / 2 < ccdf μ p :=
      hc.continuousAt.eventually (lt_mem_nhds (by rw [Lib.ccdf_zero μ hF]; norm_num))
    obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.mp hev
    have hp : (1 : ℝ) / 2 < ccdf μ (δ / 2) := hball (by
      rw [Real.dist_eq, sub_zero, abs_of_pos (by positivity)]; linarith)
    have h : δ / 2 * ccdf μ (δ / 2) ≤ r * ccdf μ r :=
      isMaxOn_iff.mp hr.2 (δ / 2) (Set.mem_Ici.mpr (by positivity))
    have hpos : 0 < δ / 2 * ccdf μ (δ / 2) := mul_pos (by positivity) (by linarith)
    rw [hf1]
    by_contra hneg
    have hle : ccdf μ r ≤ 0 := not_lt.mp hneg
    have := mul_le_mul_of_nonneg_left hle hr0.le
    rw [mul_zero] at this
    linarith
  have hconv : ConvexOn ℝ {v : ℝ | 0 ≤ v ∧ 0 < f v} (fun v => -Real.log (f v)) := by
    have h2 := hcv.comp_linearMap (LinearMap.lsmul ℝ ℝ r)
    have hset : (LinearMap.lsmul ℝ ℝ r) ⁻¹' {v : ℝ | 0 ≤ v ∧ 0 < ccdf μ v}
        = {v : ℝ | 0 ≤ v ∧ 0 < f v} := by
      ext v
      simp only [Set.mem_preimage, Set.mem_setOf_eq, LinearMap.lsmul_apply, smul_eq_mul, hfx,
        mul_nonneg_iff_of_pos_left hr0]
    rw [hset] at h2
    have hfun : (fun v => -Real.log (f v))
        = (fun v => GammaAInv 1 (ccdf μ v)) ∘ ⇑(LinearMap.lsmul ℝ ℝ r) := by
      funext v
      simp [hfx, GammaAInv]
    rw [hfun]
    exact h2
  have ha0 : 0 ≤ -Real.log (f 1) := by
    have := Real.log_nonpos (hnn 1) hf1le; linarith
  have ha1 : -Real.log (f 1) ≤ 1 := Pt2.a_le_one f hconv h0 h1 hanti hoptf
  obtain ⟨σ, hσv⟩ : ∃ σ : ℝ, σ = if 0 < f (1 / (19 / 25)) then
      6 / 19 / (-Real.log (f (1 / (19 / 25))) - -Real.log (f 1)) else 0 := ⟨_, rfl⟩
  have e6 : (1 : ℝ) / (19 / 25) - 1 = 6 / 19 := by norm_num
  have hτ : 0 < f (1 / (19 / 25)) →
      6 / 19 ≤ -Real.log (f (1 / (19 / 25))) - -Real.log (f 1) := by
    intro hpos
    have := Pt2.tau_ge f hconv h1 hanti hoptf (s := 1 / (19 / 25)) (by norm_num) hpos
    linarith
  have hσ01 : 0 ≤ σ ∧ σ ≤ 1 := by
    by_cases hpos : 0 < f (1 / (19 / 25))
    · rw [if_pos hpos] at hσv
      have ht := hτ hpos
      rw [hσv]
      exact ⟨div_nonneg (by norm_num) (by linarith), by rw [div_le_one (by linarith)]; exact ht⟩
    · rw [if_neg hpos] at hσv
      rw [hσv]; norm_num
  have hQ := cover_Q (-Real.log (f 1)) σ ha0 ha1 hσ01.1 hσ01.2
  unfold Q at hQ
  obtain ⟨a0, s0, T, Th, ha00, ha0a, hs00, hs0σ, hT, hTσ, hsTh, hTh, ha01, hsT, hA⟩ := hQ
  have hint := hA (f 1) h1 hf1le rfl
  have hσ : 0 < f (1 / (19 / 25)) →
      s0 * (-Real.log (f (1 / (19 / 25))) - -Real.log (f 1)) ≤ 1 / (19 / 25) - 1 ∧
      T ≤ -Real.log (f (1 / (19 / 25))) - -Real.log (f 1) := by
    intro hpos
    have ht := hτ hpos
    rw [if_pos hpos] at hσv
    set τ := -Real.log (f (1 / (19 / 25))) - -Real.log (f 1) with hτdef
    have hτp : 0 < τ := by linarith
    have hτne : τ ≠ 0 := hτp.ne'
    have hστ : σ * τ = 6 / 19 := by rw [hσv]; field_simp
    have hσp : 0 < σ := by rw [hσv]; exact div_pos (by norm_num) hτp
    constructor
    · have := mul_le_mul_of_nonneg_right hs0σ hτp.le
      linarith
    · exact le_of_mul_le_mul_right (by linarith : T * σ ≤ τ * σ) hσp
  have hσ0 : f (1 / (19 / 25)) = 0 → s0 = 0 := by
    intro hz
    have hn : ¬ 0 < f (1 / (19 / 25)) := by rw [hz]; exact lt_irrefl 0
    rw [if_neg hn] at hσv
    linarith
  have hpw : ∀ x, 0 ≤ x → PsiF (19 / 25) (f 1) a0 s0 T Th (Mt.Mc (19 / 25)) (f x)
      ≤ 19 / 25 * x * f (19 / 25 * x) := fun x hx =>
    Pt2.pw_all f hconv h0 h1 hanti hoptf hnn (by norm_num) (by norm_num) hT ha0a hs00 hσ hσ0
      (fun h => by rw [e6]; exact hsTh h)
      (Mt.Mc_hM (by norm_num) (by norm_num) (by rw [e6]; exact hTh)) hx
  have hb0 := hbdd (Th := Th) h1 hf1le ha00 ha01 hs00 hT.le hsT
  have hm0 : Measurable (PsiF (19 / 25) (f 1) a0 s0 T Th (Mt.Mc (19 / 25))) :=
    Pt2.PsiF_meas (Mt.Mc_meas _)
  have hpost := Lib.postRev_ge_of_pointwise μ hF (γ := 19 / 25) (by norm_num)
    (Ψ := fun q => r * PsiF (19 / 25) (f 1) a0 s0 T Th (Mt.Mc (19 / 25)) q)
    (measurable_const.mul hm0) (C := r * (3 + 1))
    (fun q => by
      show |r * PsiF (19 / 25) (f 1) a0 s0 T Th (Mt.Mc (19 / 25)) q| ≤ r * (3 + 1)
      rw [abs_mul, abs_of_pos hr0]; exact mul_le_mul_of_nonneg_left (hb0 q) hr0.le)
    (fun s hs => by
      show r * PsiF (19 / 25) (f 1) a0 s0 T Th (Mt.Mc (19 / 25)) (ccdf μ s)
        ≤ 19 / 25 * s * ccdf μ (19 / 25 * s)
      have hx : 0 ≤ s / r := div_nonneg hs hr0.le
      have h := hpw (s / r) hx
      have e1 : r * (s / r) = s := by field_simp
      have e2 : r * (19 / 25 * (s / r)) = 19 / 25 * s := by
        rw [← mul_assoc, mul_comm r, mul_assoc, e1]
      rw [hfx (s / r), hfx (19 / 25 * (s / r)), e1, e2] at h
      calc r * PsiF (19 / 25) (f 1) a0 s0 T Th (Mt.Mc (19 / 25)) (ccdf μ s)
          ≤ r * (19 / 25 * (s / r) * ccdf μ (19 / 25 * s)) := mul_le_mul_of_nonneg_left h hr0.le
        _ = 19 / 25 * s * ccdf μ (19 / 25 * s) := by
          rw [show r * (19 / 25 * (s / r) * ccdf μ (19 / 25 * s))
            = 19 / 25 * (r * (s / r)) * ccdf μ (19 / 25 * s) by ring, e1])
  have hpost' : r * ∫ q in Set.Icc (0 : ℝ) 1, PsiF (19 / 25) (f 1) a0 s0 T Th (Mt.Mc (19 / 25)) q
      ≤ postRev (19 / 25) μ := by
    rw [← integral_const_mul]; exact hpost
  rw [hoptr, ← hf1]
  have k := mul_le_mul_of_nonneg_left hint hr0.le
  have hrf := mul_nonneg hr0.le (hnn 1)
  linarith

end PricingSamples.OneSampleMHR.Fin

open PricingSamples.OneSampleMHR MeasureTheory in
theorem solution (μ : Measure ℝ) (hF : InFAlpha 1 μ) :
    (0.644 : ℝ) * opt μ ≤ postRev 0.76 μ := by
  exact PricingSamples.OneSampleMHR.Fin.main μ hF
