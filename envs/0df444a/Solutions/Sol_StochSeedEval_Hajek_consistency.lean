-- Prove2me | solution 1 for StochSeedEval.Hajek.consistency
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-21T07:56:51.348756+00:00
-- url     : https://prove2.me/submissions/1e54e40e-bd9e-4e45-ae80-4383e37b6a9e

import Mathlib
import Definitions.Def_StochSeedEval_Hajek_Estimators

open MeasureTheory ProbabilityTheory Filter Topology

set_option linter.unusedSectionVars false

namespace HajekDev
open StochSeedEval.Hajek

variable {Ω : Type*} [Countable Ω] [MeasurableSpace Ω] [MeasurableSingletonClass Ω]

lemma toMeasure_eq_withDensity (pA pD : PMF Ω) (hpos : ∀ s, pA s ≠ 0 → pD s ≠ 0) :
    pA.toMeasure = pD.toMeasure.withDensity (fun s => pA s / pD s) := by
  refine Measure.ext_of_singleton fun s => ?_
  rw [withDensity_apply _ (measurableSet_singleton s), Measure.restrict_singleton,
    lintegral_smul_measure, lintegral_dirac, PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton s),
    PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton s)]
  by_cases h : pA s = 0
  · simp [h]
  · rw [smul_eq_mul, ENNReal.mul_div_cancel (hpos s h) (PMF.apply_ne_top _ _)]

lemma integral_weight_mul (pA pD : PMF Ω) (hpos : ∀ s, pA s ≠ 0 → pD s ≠ 0) (g : Ω → ℝ) :
    ∫ s, weightA pA pD s * g s ∂pD.toMeasure = ∫ s, g s ∂pA.toMeasure := by
  rw [toMeasure_eq_withDensity pA pD hpos, integral_withDensity_eq_integral_toReal_smul
    (measurable_of_countable _)]
  · congr 1; ext s
    simp [weightA, ENNReal.toReal_div]
  · refine ae_of_all _ fun s => ?_
    by_cases h : pA s = 0
    · simp [h]
    · exact ENNReal.div_lt_top (PMF.apply_ne_top _ _) (hpos s h)

lemma integral_weight (pA pD : PMF Ω) (hpos : ∀ s, pA s ≠ 0 → pD s ≠ 0) :
    ∫ s, weightA pA pD s ∂pD.toMeasure = 1 := by
  have := integral_weight_mul pA pD hpos (fun _ => 1)
  simpa using this


section Sample
variable {Ω' : Type*} [MeasurableSpace Ω'] (P : Measure Ω') [IsProbabilityMeasure P]
  (pD : PMF Ω) (S : ℕ → Ω' → Ω)

lemma identDistrib_comp (hSm : ∀ i, Measurable (S i))
    (hSlaw : ∀ i, P.map (S i) = pD.toMeasure) (g : Ω → ℝ) (i : ℕ) :
    IdentDistrib (fun ω => g (S i ω)) (fun ω => g (S 0 ω)) P P where
  aemeasurable_fst := ((measurable_of_countable g).comp (hSm i)).aemeasurable
  aemeasurable_snd := ((measurable_of_countable g).comp (hSm 0)).aemeasurable
  map_eq := by
    have h1 : P.map (fun ω => g (S i ω)) = (P.map (S i)).map g :=
      (Measure.map_map (measurable_of_countable g) (hSm i)).symm
    have h2 : P.map (fun ω => g (S 0 ω)) = (P.map (S 0)).map g :=
      (Measure.map_map (measurable_of_countable g) (hSm 0)).symm
    rw [h1, h2, hSlaw, hSlaw]

lemma integral_comp_S (hSm : ∀ i, Measurable (S i))
    (hSlaw : ∀ i, P.map (S i) = pD.toMeasure) (g : Ω → ℝ) (i : ℕ) :
    ∫ ω, g (S i ω) ∂P = ∫ s, g s ∂pD.toMeasure := by
  rw [← hSlaw i, integral_map (hSm i).aemeasurable
    (measurable_of_countable g).aestronglyMeasurable]

lemma slln_avg (hSm : ∀ i, Measurable (S i)) (hSi : iIndepFun S P)
    (hSlaw : ∀ i, P.map (S i) = pD.toMeasure) (g : Ω → ℝ)
    (hg : Integrable g pD.toMeasure) :
    ∀ᵐ ω ∂P, Tendsto (fun N => sampleAverage S g N ω) atTop
      (𝓝 (∫ s, g s ∂pD.toMeasure)) := by
  have hint : Integrable (fun ω => g (S 0 ω)) P := by
    rw [← hSlaw 0] at hg
    exact hg.comp_measurable (hSm 0)
  have hind : Pairwise (Function.onFun (· ⟂ᵢ[P] ·) (fun i ω => g (S i ω))) := by
    intro i j hij
    exact (hSi.comp (fun _ => g) (fun _ => measurable_of_countable g)).indepFun hij
  have := strong_law_ae_real (fun i ω => g (S i ω)) hint hind
    (identDistrib_comp P pD S hSm hSlaw g)
  filter_upwards [this] with ω hω
  rw [integral_comp_S P pD S hSm hSlaw g 0] at hω
  convert hω using 2 with N
  simp [sampleAverage, div_eq_inv_mul]


lemma sqrt_mul_sampleAverage (g : Ω → ℝ) (N : ℕ) (ω : Ω') :
    Real.sqrt (N : ℝ) * sampleAverage S g N ω =
      (Real.sqrt N)⁻¹ * (∑ k ∈ Finset.range N, g (S k ω) - N * 0) := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp [sampleAverage]
  · have hs : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast hN)
    have hsq : Real.sqrt (N : ℝ) * Real.sqrt N = N := Real.mul_self_sqrt (by positivity)
    have h1 : (1 / (N : ℝ)) = (Real.sqrt N)⁻¹ * (Real.sqrt N)⁻¹ := by
      rw [← mul_inv, hsq, one_div]
    simp only [sampleAverage, mul_zero, sub_zero, h1]
    rw [← mul_assoc, ← mul_assoc, mul_inv_cancel₀ hs.ne', one_mul]

lemma clt_avg (hSm : ∀ i, Measurable (S i)) (hSi : iIndepFun S P)
    (hSlaw : ∀ i, P.map (S i) = pD.toMeasure) (g : Ω → ℝ)
    (hg : MemLp g 2 pD.toMeasure) (h0 : ∫ s, g s ∂pD.toMeasure = 0)
    {Ω'' : Type*} [MeasurableSpace Ω''] (Q : Measure Ω'') [IsProbabilityMeasure Q]
    (Z : Ω'' → ℝ) (hZ : HasLaw Z (gaussianReal 0 (variance g pD.toMeasure).toNNReal) Q) :
    TendstoInDistribution (fun (N : ℕ) ω => Real.sqrt (N : ℝ) * sampleAverage S g N ω)
      atTop Z (fun _ => P) Q := by
  have hvar : variance (fun ω => g (S 0 ω)) P = variance g pD.toMeasure := by
    rw [← hSlaw 0, variance_map (measurable_of_countable g).aemeasurable (hSm 0).aemeasurable]
    rfl
  have hmean : ∫ ω, g (S 0 ω) ∂P = 0 := by
    rw [integral_comp_S P pD S hSm hSlaw g 0, h0]
  have hX : MemLp (fun ω => g (S 0 ω)) 2 P := by
    rw [← hSlaw 0] at hg
    exact hg.comp_of_map (hSm 0).aemeasurable
  have := tendstoInDistribution_inv_sqrt_mul_sum_sub (X := fun i ω => g (S i ω))
    (by rw [hvar]; exact hZ) hX
    (hSi.comp (fun _ => g) (fun _ => measurable_of_countable g))
    (identDistrib_comp P pD S hSm hSlaw g)
  rw [hmean] at this
  convert this using 3 with N ω
  exact sqrt_mul_sampleAverage S g N ω

end Sample


section Conv
variable {Ω' Ω'' : Type*} [MeasurableSpace Ω'] [MeasurableSpace Ω'']
  {P : Measure Ω'} [IsProbabilityMeasure P] {Q : Measure Ω''} [IsProbabilityMeasure Q]

lemma tendstoInMeasure_of_tendstoInDistribution_const {X : ℕ → Ω' → ℝ} (c : ℝ)
    (h : TendstoInDistribution X atTop (fun _ : Ω'' => c) (fun _ => P) Q) :
    TendstoInMeasure P X atTop (fun _ => c) := by
  rw [tendstoInMeasure_iff_measureReal_norm]
  intro ε hε
  set E : Set ℝ := {x : ℝ | ε ≤ ‖x - c‖} with hE
  have hEm : MeasurableSet E := measurableSet_le measurable_const (by fun_prop)
  have hfr : frontier E ⊆ {x : ℝ | ε = ‖x - c‖} :=
    frontier_le_subset_eq continuous_const (by fun_prop)
  have hnull : (Q.map (fun _ => c)) (frontier E) = 0 := by
    rw [Measure.map_const]
    refine measure_mono_null hfr ?_
    rw [Measure.smul_apply, Measure.dirac_apply' _ (measurableSet_eq_fun measurable_const
      (by fun_prop))]
    simp [hε.ne']
  have key := ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto h.tendsto
    (E := E) (by show ((Q.map (fun _ => c)) (frontier E)).toNNReal = 0; rw [hnull]; rfl)
  have hlim : (Q.map (fun _ => c)) E = 0 := by
    rw [Measure.map_const, Measure.smul_apply, Measure.dirac_apply' _ hEm]
    simp [hE, hε.not_ge]
  have key' : Tendsto (fun n => ((P.map (X n)) E).toNNReal) atTop
      (𝓝 (((Q.map fun _ => c) E).toNNReal)) := key
  rw [hlim, ENNReal.toNNReal_zero] at key'
  have key2 := (NNReal.continuous_coe.tendsto _).comp key'
  simp only [NNReal.coe_zero] at key2
  refine key2.congr fun n => ?_
  simp only [Function.comp_apply, ENNReal.coe_toNNReal_eq_toReal]
  rw [Measure.map_apply_of_aemeasurable (h.forall_aemeasurable n) hEm]
  rfl


lemma mul_tendstoInMeasure_zero {U W : ℕ → Ω' → ℝ} {Z : Ω'' → ℝ}
    (hU : TendstoInDistribution U atTop Z (fun _ => P) Q)
    (hW : TendstoInMeasure P W atTop (fun _ => 0)) (hWm : ∀ n, AEMeasurable (W n) P) :
    TendstoInMeasure P (fun n ω => U n ω * W n ω) atTop (fun _ => 0) := by
  have := hU.continuous_comp_prodMk_of_tendstoInMeasure_const
    (g := fun p : ℝ × ℝ => p.1 * p.2) (by fun_prop) hW hWm
  apply tendstoInMeasure_of_tendstoInDistribution_const (Q := Q) 0
  simpa using this

end Conv

lemma sampleAverage_measurable {Ω' : Type*} [MeasurableSpace Ω'] (S : ℕ → Ω' → Ω)
    (hSm : ∀ i, Measurable (S i)) (g : Ω → ℝ) (N : ℕ) :
    Measurable (sampleAverage S g N) := by
  unfold sampleAverage
  have : ∀ i, Measurable (fun ω => g (S i ω)) := fun i => (measurable_of_countable g).comp (hSm i)
  fun_prop

lemma hajek_measurable {Ω' : Type*} [MeasurableSpace Ω'] (pA pB pD : PMF Ω) (y : Ω → ℝ)
    (S : ℕ → Ω' → Ω) (hSm : ∀ i, Measurable (S i)) (N : ℕ) :
    Measurable (hajek pA pB pD y S N) := by
  unfold hajek
  have h1 : ∀ i, Measurable (fun ω => weightA pA pD (S i ω)) :=
    fun i => (measurable_of_countable (weightA pA pD)).comp (hSm i)
  have h2 : ∀ i, Measurable (fun ω => weightB pB pD (S i ω)) :=
    fun i => (measurable_of_countable (weightB pB pD)).comp (hSm i)
  have h3 : ∀ i, Measurable (fun ω => y (S i ω)) :=
    fun i => (measurable_of_countable y).comp (hSm i)
  have h4 := sampleAverage_measurable S hSm (weightA pA pD) N
  have h5 := sampleAverage_measurable S hSm (weightB pB pD) N
  fun_prop

lemma hajek_eq {Ω' : Type*} (pA pB pD : PMF Ω) (y : Ω → ℝ) (S : ℕ → Ω' → Ω) (N : ℕ) (ω : Ω') :
    hajek pA pB pD y S N ω =
      sampleAverage S (fun s => weightA pA pD s * y s) N ω / sampleAverage S (weightA pA pD) N ω -
      sampleAverage S (fun s => weightB pB pD s * y s) N ω / sampleAverage S (weightB pB pD) N ω := by
  simp only [hajek, sampleAverage, sub_mul, Finset.sum_sub_distrib, mul_sub, div_eq_mul_inv,
    Finset.mul_sum, Finset.sum_mul]
  congr 1 <;> refine Finset.sum_congr rfl fun i _ => by ring

lemma sampleAverage_sub_const_mul {Ω' : Type*} (S : ℕ → Ω' → Ω) (f g : Ω → ℝ) (c : ℝ)
    (N : ℕ) (ω : Ω') :
    sampleAverage S (fun s => f s - c * g s) N ω =
      sampleAverage S f N ω - c * sampleAverage S g N ω := by
  simp only [sampleAverage, Finset.sum_sub_distrib, ← Finset.mul_sum]
  ring

lemma sampleAverage_sub {Ω' : Type*} (S : ℕ → Ω' → Ω) (f g : Ω → ℝ)
    (N : ℕ) (ω : Ω') :
    sampleAverage S (fun s => f s - g s) N ω =
      sampleAverage S f N ω - sampleAverage S g N ω := by
  simp only [sampleAverage, Finset.sum_sub_distrib]
  ring

lemma meanA_eq (pA pD : PMF Ω) (y : Ω → ℝ) (hpos : ∀ s, pA s ≠ 0 → pD s ≠ 0) :
    meanA pA y = ∫ s, weightA pA pD s * y s ∂pD.toMeasure :=
  (integral_weight_mul pA pD hpos y).symm

lemma meanB_eq (pB pD : PMF Ω) (y : Ω → ℝ) (hpos : ∀ s, pB s ≠ 0 → pD s ≠ 0) :
    meanB pB y = ∫ s, weightB pB pD s * y s ∂pD.toMeasure := by
  have := integral_weight_mul pB pD hpos y
  simp only [weightA] at this
  simp only [weightB, meanB]
  exact this.symm

lemma integral_weightB (pB pD : PMF Ω) (hpos : ∀ s, pB s ≠ 0 → pD s ≠ 0) :
    ∫ s, weightB pB pD s ∂pD.toMeasure = 1 := integral_weight pB pD hpos

lemma integrable_weight (pA pD : PMF Ω) (hpos : ∀ s, pA s ≠ 0 → pD s ≠ 0) :
    Integrable (weightA pA pD) pD.toMeasure := by
  by_contra h
  have := integral_weight pA pD hpos
  rw [integral_undef h] at this
  exact zero_ne_one this

theorem ms_weight_moments
    (pA pB pD : PMF Ω) (y : Ω → ℝ)
    (hpos : ∀ s, (pA s ≠ 0 ∨ pB s ≠ 0) → pD s ≠ 0)
    (hAy : Integrable (fun s => weightA pA pD s * y s) pD.toMeasure)
    (hBy : Integrable (fun s => weightB pB pD s * y s) pD.toMeasure) :
    (∫ s, weightA pA pD s ∂pD.toMeasure) = 1 ∧
    (∫ s, weightB pB pD s ∂pD.toMeasure) = 1 ∧
    (∫ s, weightA pA pD s * y s ∂pD.toMeasure) = meanA pA y ∧
    (∫ s, weightB pB pD s * y s ∂pD.toMeasure) = meanB pB y :=
  ⟨integral_weight pA pD (fun s h => hpos s (Or.inl h)),
   integral_weightB pB pD (fun s h => hpos s (Or.inr h)),
   (meanA_eq pA pD y (fun s h => hpos s (Or.inl h))).symm,
   (meanB_eq pB pD y (fun s h => hpos s (Or.inr h))).symm⟩

theorem ms_sample_averages
    (pA pB pD : PMF Ω) (y : Ω → ℝ)
    (hpos : ∀ s, (pA s ≠ 0 ∨ pB s ≠ 0) → pD s ≠ 0)
    (hAy : Integrable (fun s => weightA pA pD s * y s) pD.toMeasure)
    (hBy : Integrable (fun s => weightB pB pD s * y s) pD.toMeasure)
    {Ω' : Type*} [MeasurableSpace Ω'] (P : Measure Ω') [IsProbabilityMeasure P]
    (S : ℕ → Ω' → Ω) (hSm : ∀ i, Measurable (S i)) (hSi : iIndepFun S P)
    (hSlaw : ∀ i, P.map (S i) = pD.toMeasure) :
    ∀ᵐ ω ∂P,
      Tendsto (fun N => sampleAverage S (weightA pA pD) N ω) atTop (𝓝 (1 : ℝ)) ∧
      Tendsto (fun N => sampleAverage S (weightB pB pD) N ω) atTop (𝓝 (1 : ℝ)) ∧
      Tendsto (fun N => sampleAverage S (fun s => weightA pA pD s * y s) N ω)
        atTop (𝓝 (meanA pA y)) ∧
      Tendsto (fun N => sampleAverage S (fun s => weightB pB pD s * y s) N ω)
        atTop (𝓝 (meanB pB y)) := by
  have hpA : ∀ s, pA s ≠ 0 → pD s ≠ 0 := fun s h => hpos s (Or.inl h)
  have hpB : ∀ s, pB s ≠ 0 → pD s ≠ 0 := fun s h => hpos s (Or.inr h)
  have h1 := slln_avg P pD S hSm hSi hSlaw _ (integrable_weight pA pD hpA)
  have h2 := slln_avg P pD S hSm hSi hSlaw _ (integrable_weight pB pD hpB)
  have h3 := slln_avg P pD S hSm hSi hSlaw _ hAy
  have h4 := slln_avg P pD S hSm hSi hSlaw _ hBy
  rw [integral_weight pA pD hpA] at h1
  rw [integral_weight pB pD hpB] at h2
  rw [← meanA_eq pA pD y hpA] at h3
  rw [← meanB_eq pB pD y hpB] at h4
  filter_upwards [h1, h2, h3, h4] with ω a b c d
  exact ⟨a, b, c, d⟩

theorem ms_consistency
    (pA pB pD : PMF Ω) (y : Ω → ℝ)
    (hpos : ∀ s, (pA s ≠ 0 ∨ pB s ≠ 0) → pD s ≠ 0)
    (hAy : Integrable (fun s => weightA pA pD s * y s) pD.toMeasure)
    (hBy : Integrable (fun s => weightB pB pD s * y s) pD.toMeasure)
    {Ω' : Type*} [MeasurableSpace Ω'] (P : Measure Ω') [IsProbabilityMeasure P]
    (S : ℕ → Ω' → Ω) (hSm : ∀ i, Measurable (S i)) (hSi : iIndepFun S P)
    (hSlaw : ∀ i, P.map (S i) = pD.toMeasure) :
    ∀ᵐ ω ∂P, Tendsto (fun N => hajek pA pB pD y S N ω) atTop (𝓝 (contrast pA pB y)) := by
  filter_upwards [ms_sample_averages pA pB pD y hpos hAy hBy P S hSm hSi hSlaw]
    with ω ⟨h1, h2, h3, h4⟩
  have := (h3.div h1 one_ne_zero).sub (h4.div h2 one_ne_zero)
  simp only [div_one] at this
  refine this.congr fun N => ?_
  rw [hajek_eq]; rfl

theorem ms_variance_identity
    (pA pB pD : PMF Ω) (y : Ω → ℝ)
    (hpos : ∀ s, (pA s ≠ 0 ∨ pB s ≠ 0) → pD s ≠ 0)
    (hA2 : MemLp (weightA pA pD) 2 pD.toMeasure)
    (hB2 : MemLp (weightB pB pD) 2 pD.toMeasure)
    (hAy2 : MemLp (fun s => weightA pA pD s * y s) 2 pD.toMeasure)
    (hBy2 : MemLp (fun s => weightB pB pD s * y s) 2 pD.toMeasure) :
    (∫ s, influence pA pB pD y s ∂pD.toMeasure) = 0 ∧
    variance (influence pA pB pD y) pD.toMeasure = asymptoticVariance pA pB pD y := by
  have hpA : ∀ s, pA s ≠ 0 → pD s ≠ 0 := fun s h => hpos s (Or.inl h)
  have hpB : ∀ s, pB s ≠ 0 → pD s ≠ 0 := fun s h => hpos s (Or.inr h)
  have hA1 := integral_weight pA pD hpA
  have hB1 := integral_weightB pB pD hpB
  have hAy1 := (meanA_eq pA pD y hpA).symm
  have hBy1 := (meanB_eq pB pD y hpB).symm
  have hLT : influence pA pB pD y = fun s =>
      (weightA pA pD s * y s - meanA pA y * weightA pA pD s) -
      (weightB pB pD s * y s - meanB pB y * weightB pB pD s) := by
    funext s; simp only [influence]; ring
  have iAy := hAy2.integrable one_le_two
  have iBy := hBy2.integrable one_le_two
  have iA : Integrable (fun s => meanA pA y * weightA pA pD s) pD.toMeasure :=
    (hA2.integrable one_le_two).const_mul _
  have iB : Integrable (fun s => meanB pB y * weightB pB pD s) pD.toMeasure :=
    (hB2.integrable one_le_two).const_mul _
  have iTA : Integrable (fun s => weightA pA pD s * y s - meanA pA y * weightA pA pD s)
    pD.toMeasure := iAy.sub iA
  have iTB : Integrable (fun s => weightB pB pD s * y s - meanB pB y * weightB pB pD s)
    pD.toMeasure := iBy.sub iB
  have hL0 : ∫ s, influence pA pB pD y s ∂pD.toMeasure = 0 := by
    rw [hLT, integral_sub iTA iTB, integral_sub iAy iA, integral_sub iBy iB,
      integral_const_mul, integral_const_mul, hA1, hB1, hAy1, hBy1]
    ring
  refine ⟨hL0, ?_⟩
  rw [variance_eq_integral (measurable_of_countable _).aemeasurable, hL0]
  unfold asymptoticVariance
  refine integral_congr_ae (ae_of_all _ fun s => ?_)
  simp only [influence, weightA, weightB, sub_zero]
  ring

theorem ms_joint_clt
    (pA pB pD : PMF Ω) (y : Ω → ℝ)
    (hpos : ∀ s, (pA s ≠ 0 ∨ pB s ≠ 0) → pD s ≠ 0)
    (hA2 : MemLp (weightA pA pD) 2 pD.toMeasure)
    (hB2 : MemLp (weightB pB pD) 2 pD.toMeasure)
    (hAy2 : MemLp (fun s => weightA pA pD s * y s) 2 pD.toMeasure)
    (hBy2 : MemLp (fun s => weightB pB pD s * y s) 2 pD.toMeasure)
    {Ω' : Type*} [MeasurableSpace Ω'] (P : Measure Ω') [IsProbabilityMeasure P]
    (S : ℕ → Ω' → Ω) (hSm : ∀ i, Measurable (S i)) (hSi : iIndepFun S P)
    (hSlaw : ∀ i, P.map (S i) = pD.toMeasure) :
    ∀ (c : Fin 4 → ℝ) {Ω'' : Type*} [MeasurableSpace Ω'']
      (Q : Measure Ω'') [IsProbabilityMeasure Q] (Z : Ω'' → ℝ),
      HasLaw Z (gaussianReal 0 (variance (linearStatistic pA pB pD y c) pD.toMeasure).toNNReal) Q →
      TendstoInDistribution
        (fun (N : ℕ) ω => Real.sqrt (N : ℝ) *
          (c 0 * (sampleAverage S (weightA pA pD) N ω - 1) +
           c 1 * (sampleAverage S (weightB pB pD) N ω - 1) +
           c 2 * (sampleAverage S (fun s => weightA pA pD s * y s) N ω - meanA pA y) +
           c 3 * (sampleAverage S (fun s => weightB pB pD s * y s) N ω - meanB pB y)))
        atTop Z (fun _ => P) Q := by
  intro c Ω'' _ Q _ Z hZ
  have hpA : ∀ s, pA s ≠ 0 → pD s ≠ 0 := fun s h => hpos s (Or.inl h)
  have hpB : ∀ s, pB s ≠ 0 → pD s ≠ 0 := fun s h => hpos s (Or.inr h)
  have hA1 := integral_weight pA pD hpA
  have hB1 := integral_weightB pB pD hpB
  have hAy1 := (meanA_eq pA pD y hpA).symm
  have hBy1 := (meanB_eq pB pD y hpB).symm
  set m : ℝ := c 0 + c 1 + c 2 * meanA pA y + c 3 * meanB pB y with hm
  have hlin2 : MemLp (linearStatistic pA pB pD y c) 2 pD.toMeasure := by
    have := (((hA2.const_mul (c 0)).add (hB2.const_mul (c 1))).add
      (hAy2.const_mul (c 2))).add (hBy2.const_mul (c 3))
    convert this using 1
    funext s; simp only [linearStatistic, Pi.add_apply]; ring
  have hlinI : ∫ s, linearStatistic pA pB pD y c s ∂pD.toMeasure = m := by
    unfold linearStatistic
    have e : (fun s => c 0 * weightA pA pD s + c 1 * weightB pB pD s +
        c 2 * weightA pA pD s * y s + c 3 * weightB pB pD s * y s) =
        fun s => c 0 * weightA pA pD s + c 1 * weightB pB pD s +
        c 2 * (weightA pA pD s * y s) + c 3 * (weightB pB pD s * y s) := by
      funext s; ring
    have i0 : Integrable (fun s => c 0 * weightA pA pD s) pD.toMeasure :=
      (hA2.integrable one_le_two).const_mul _
    have i1 : Integrable (fun s => c 1 * weightB pB pD s) pD.toMeasure :=
      (hB2.integrable one_le_two).const_mul _
    have i2 : Integrable (fun s => c 2 * (weightA pA pD s * y s)) pD.toMeasure :=
      (hAy2.integrable one_le_two).const_mul _
    have i3 : Integrable (fun s => c 3 * (weightB pB pD s * y s)) pD.toMeasure :=
      (hBy2.integrable one_le_two).const_mul _
    have i01 : Integrable (fun s => c 0 * weightA pA pD s + c 1 * weightB pB pD s)
      pD.toMeasure := i0.add i1
    have i012 : Integrable (fun s => c 0 * weightA pA pD s + c 1 * weightB pB pD s +
      c 2 * (weightA pA pD s * y s)) pD.toMeasure := i01.add i2
    rw [e, integral_add i012 i3, integral_add i01 i2, integral_add i0 i1, integral_const_mul,
      integral_const_mul, integral_const_mul, integral_const_mul, hA1, hB1, hAy1, hBy1]
    rw [hm]; ring
  have hg2 : MemLp (fun s => linearStatistic pA pB pD y c s - m) 2 pD.toMeasure :=
    hlin2.sub (memLp_const m)
  have hg0 : ∫ s, (linearStatistic pA pB pD y c s - m) ∂pD.toMeasure = 0 := by
    rw [integral_sub (hlin2.integrable one_le_two) (integrable_const m), hlinI]; simp
  have hvar : variance (fun s => linearStatistic pA pB pD y c s - m) pD.toMeasure =
      variance (linearStatistic pA pB pD y c) pD.toMeasure :=
    variance_sub_const (measurable_of_countable _).aestronglyMeasurable m
  have := clt_avg P pD S hSm hSi hSlaw _ hg2 hg0 Q Z (by rw [hvar]; exact hZ)
  convert this using 3 with N ω
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp
  · congr 1
    have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
    simp only [sampleAverage, linearStatistic, Finset.sum_sub_distrib, Finset.sum_add_distrib,
      Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_assoc, ← Finset.mul_sum, hm]
    field_simp
    ring

end HajekDev

open StochSeedEval.Hajek


theorem solution
    {Ω : Type*} [Countable Ω] [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    (pA pB pD : PMF Ω) (y : Ω → ℝ)
    (hpos : ∀ s, (pA s ≠ 0 ∨ pB s ≠ 0) → pD s ≠ 0)
    (hAy : Integrable (fun s => weightA pA pD s * y s) pD.toMeasure)
    (hBy : Integrable (fun s => weightB pB pD s * y s) pD.toMeasure)
    {Ω' : Type*} [MeasurableSpace Ω'] (P : Measure Ω') [IsProbabilityMeasure P]
    (S : ℕ → Ω' → Ω) (hSm : ∀ i, Measurable (S i)) (hSi : iIndepFun S P)
    (hSlaw : ∀ i, P.map (S i) = pD.toMeasure) :
    ∀ᵐ ω ∂P, Tendsto (fun N => hajek pA pB pD y S N ω) atTop (𝓝 (contrast pA pB y)) :=
  HajekDev.ms_consistency pA pB pD y hpos hAy hBy P S hSm hSi hSlaw
