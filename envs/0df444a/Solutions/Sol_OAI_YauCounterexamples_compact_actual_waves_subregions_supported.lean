-- Prove2me | solution 1 for OAI.YauCounterexamples.compact_actual_waves_subregions_supported
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T13:03:57.411119+00:00
-- url     : https://prove2.me/submissions/c2f6b96f-2d3a-4596-9e7f-78d816360e48

import Mathlib
import Definitions.Def_SmoothYau
import Definitions.Def_OAIQ070A009
import Definitions.Def_OAIQ070A010
import Theorems.Thm_OAI_YauCounterexamples_compact_actual_sign_noncancellation_supported

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Smoothness_ProbabilityBadJet
attribute [-instance] _root_.OAI.YauCounterexamples.circle_dimension_fact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open MvPolynomial
open Set Filter
open scoped ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open scoped Topology
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Matrix
open scoped Topology Matrix.Norms.Elementwise
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set Filter
open scoped ContDiff Topology
open Set
open Set MeasureTheory
open scoped ENNReal
namespace YauCounterexamples

theorem exists_good_of_expectation {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (F : Ω → ℝ)
    (hF : Integrable F μ) (G : Set Ω) (hG : MeasurableSet G)
    (C a c : ℝ) (hC : ∀ outcome, F outcome ≤ C) (hc : 0 ≤ c)
    (ha : a ≤ ∫ outcome, F outcome ∂μ) (hbad : c + C * (μ Gᶜ).toReal < a) :
    ∃ outcome ∈ G, c < F outcome := by
  by_contra h
  push Not at h
  let B : Ω → ℝ := fun outcome => c + Gᶜ.indicator (fun _ => C) outcome
  have hB : Integrable B μ := (integrable_const c).add
    ((integrable_const C).indicator hG.compl)
  have hFB : ∀ outcome, F outcome ≤ B outcome := by
    intro outcome
    by_cases hω : outcome ∈ G
    · simpa [B, hω] using h outcome hω
    · simp only [B, Set.indicator_of_mem (show outcome ∈ Gᶜ from hω)]
      linarith [hC outcome]
  have hint : (∫ outcome, B outcome ∂μ) = c + C * (μ Gᶜ).toReal := by
    dsimp only [B]
    rw [integral_add (integrable_const c) ((integrable_const C).indicator hG.compl),
      integral_indicator hG.compl]
    simp [mul_comm, Measure.real]
  exact (not_lt_of_ge (ha.trans ((integral_mono hF hB hFB).trans_eq hint))) hbad

end YauCounterexamples

end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Estimates_FiniteRegionsWaveSignExpectation
attribute [-instance] _root_.OAI.YauCounterexamples.circle_dimension_fact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples
section
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal

theorem finite_section_score_expectation
    {Ω X J : Type*} [MeasurableSpace Ω] [MeasurableSpace X] [Fintype J]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ν : Measure X) [IsFiniteMeasure ν]
    (E : J → Set (Ω×X)) (hE : ∀ j, MeasurableSet (E j)) (p : ℝ)
    (hprob : ∀ᵐ x ∂ν, p ≤ ∑ j, (μ {ω | (ω,x) ∈ E j}).toReal) :
    Integrable (fun ω => ∑ j, (ν {x | (ω,x) ∈ E j}).toReal) μ ∧
    (∀ ω, 0 ≤ ∑ j, (ν {x | (ω,x) ∈ E j}).toReal ∧
      ∑ j, (ν {x | (ω,x) ∈ E j}).toReal ≤ (Fintype.card J : ℝ)*(ν univ).toReal) ∧
    p*(ν univ).toReal ≤ ∫ ω, ∑ j, (ν {x | (ω,x) ∈ E j}).toReal ∂μ := by
  classical
  have hm (j : J) : Measurable (fun ω => (ν {x | (ω,x) ∈ E j}).toReal) :=
    (measurable_measure_prodMk_left (ν := ν) (hE j)).ennreal_toReal
  have hn (j : J) : Measurable (fun x => (μ {ω | (ω,x) ∈ E j}).toReal) :=
    (measurable_measure_prodMk_right (μ := μ) (hE j)).ennreal_toReal
  have hb (j : J) (ω : Ω) : (ν {x | (ω,x) ∈ E j}).toReal ≤ (ν univ).toReal :=
    ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono (subset_univ _))
  have hi (j : J) : Integrable (fun ω => (ν {x | (ω,x) ∈ E j}).toReal) μ := by
    apply (integrable_const ((ν univ).toReal)).mono' (hm j).aestronglyMeasurable
    filter_upwards [] with ω
    simpa only [Real.norm_eq_abs,abs_of_nonneg ENNReal.toReal_nonneg] using hb j ω
  have hi' (j : J) : Integrable (fun x => (μ {ω | (ω,x) ∈ E j}).toReal) ν := by
    apply (integrable_const (1 : ℝ)).mono' (hn j).aestronglyMeasurable
    filter_upwards [] with x
    rw [Real.norm_eq_abs,abs_of_nonneg ENNReal.toReal_nonneg]
    exact (ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono (subset_univ _))).trans_eq (by simp)
  have heq (j : J) : (∫ ω, (ν {x | (ω,x) ∈ E j}).toReal ∂μ) =
      ∫ x, (μ {ω | (ω,x) ∈ E j}).toReal ∂ν := by
    calc
      _ = (∫⁻ ω, ν {x | (ω,x) ∈ E j} ∂μ).toReal :=
        integral_toReal (measurable_measure_prodMk_left (ν := ν) (hE j)).aemeasurable
          (ae_of_all _ (fun _ => measure_lt_top _ _))
      _ = (∫⁻ x, μ {ω | (ω,x) ∈ E j} ∂ν).toReal :=
        congrArg ENNReal.toReal ((Measure.prod_apply (μ := μ) (ν := ν) (hE j)).symm.trans
          (Measure.prod_apply_symm (μ := μ) (ν := ν) (hE j)))
      _ = _ := (integral_toReal
        (measurable_measure_prodMk_right (μ := μ) (hE j)).aemeasurable
          (ae_of_all _ (fun _ => measure_lt_top _ _))).symm

  refine ⟨integrable_finsetSum _ (fun j _ => hi j),?_,?_⟩
  · intro ω
    refine ⟨Finset.sum_nonneg (fun _ _ => ENNReal.toReal_nonneg),?_⟩
    calc
      _ ≤ ∑ _j : J, (ν univ).toReal := Finset.sum_le_sum (fun j _ => hb j ω)
      _ = _ := by simp
  · calc
      _ = ∫ _x, p ∂ν := by simp [mul_comm,Measure.real]
      _ ≤ ∫ x, ∑ j, (μ {ω | (ω,x) ∈ E j}).toReal ∂ν :=
        integral_mono_ae (integrable_const p) (integrable_finsetSum _ (fun j _ => hi' j)) hprob
      _ = ∫ ω, ∑ j, (ν {x | (ω,x) ∈ E j}).toReal ∂μ := by
        rw [integral_finsetSum _ (fun j _ => hi' j),integral_finsetSum _ (fun j _ => hi j)]
        exact Finset.sum_congr rfl (fun j _ => (heq j).symm)
end


section
open Set MeasureTheory ProbabilityTheory
open scoped Topology ENNReal
lemma continuous_finiteWaveSuperposition_joint {I X : Type*} [Fintype I]
    [TopologicalSpace X] (w : X → ℝ) (U : I → Fin 3 → X → ℂ)
    (hw : Continuous w) (hU : ∀ i j, Continuous (U i j)) :
    Continuous (fun q : (I → Fin 3 → ℂ) × X => finiteWaveSuperposition w U q.1 q.2) := by
  classical
  unfold finiteWaveSuperposition
  apply (hw.comp continuous_snd).add
  apply continuous_finsetSum
  intro i hi
  apply continuous_finsetSum
  intro j hj
  have hc : Continuous (fun q : (I → Fin 3 → ℂ) × X => q.1 i j) := by fun_prop
  exact Complex.continuous_re.comp (hc.mul ((hU i j).comp continuous_snd))

theorem actual_wave_sign_expectation {I J X : Type*} [Fintype I] [Fintype J]
    [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X]
    (w : X → ℝ) (U : I → Fin 3 → X → ℂ)
    (hw : Continuous w) (hU : ∀ i j, Continuous (U i j))
    (S : J → X → X) (hS : ∀ j, Continuous (S j))
    (ν : Measure X) [IsFiniteMeasure ν] (p : ℝ)
    (hprob : ∀ᵐ x ∂ν, ∃ j, ENNReal.ofReal p ≤
      (Measure.pi (fun _ : I => Measure.pi (fun _ : Fin 3 => stdGaussian ℂ)))
        {γ | finiteWaveSuperposition w U γ x * finiteWaveSuperposition w U γ (S j x) < 0}) :
    let μ := Measure.pi (fun _ : I => Measure.pi (fun _ : Fin 3 => stdGaussian ℂ))
    let F := fun γ => ∑ j, (ν {x | finiteWaveSuperposition w U γ x *
      finiteWaveSuperposition w U γ (S j x) < 0}).toReal
    Integrable F μ ∧ (∀ γ, 0 ≤ F γ ∧ F γ ≤ (Fintype.card J : ℝ)*(ν univ).toReal) ∧
      p*(ν univ).toReal ≤ ∫ γ, F γ ∂μ := by
  classical
  let μ := Measure.pi (fun _ : I => Measure.pi (fun _ : Fin 3 => stdGaussian ℂ))
  let E : J → Set ((I → Fin 3 → ℂ)×X) := fun j => {q |
    finiteWaveSuperposition w U q.1 q.2 * finiteWaveSuperposition w U q.1 (S j q.2) < 0}
  have hc := continuous_finiteWaveSuperposition_joint w U hw hU
  have hm (j : J) : MeasurableSet (E j) := by
    exact isOpen_lt (hc.mul (hc.comp (continuous_fst.prodMk ((hS j).comp continuous_snd))))
      continuous_const |>.measurableSet
  apply finite_section_score_expectation μ ν E hm p
  filter_upwards [hprob] with x hx
  obtain ⟨j,hj⟩ := hx
  apply (ENNReal.ofReal_le_iff_le_toReal (measure_ne_top μ _)).mp hj |>.trans
  apply Finset.single_le_sum (fun _ _ => ENNReal.toReal_nonneg) (Finset.mem_univ j)

theorem exists_large_score_avoiding {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (F : Ω → ℝ) (hF : Integrable F μ)
    (B : Set Ω) (C a c : ℝ) (hC : ∀ ω, F ω ≤ C) (hc : 0 ≤ c)
    (ha : a ≤ ∫ ω, F ω ∂μ) (hbad : c+C*(μ B).toReal < a) :
    ∃ ω, ω ∉ B ∧ c < F ω := by
  obtain ⟨ω,hω,hscore⟩ := exists_good_of_expectation μ F hF (toMeasurable μ B)ᶜ
    (measurableSet_toMeasurable μ B).compl C a c hC hc ha (by
      simpa only [compl_compl,measure_toMeasurable] using hbad)
  exact ⟨ω,fun h => hω (subset_toMeasurable μ B h),hscore⟩
end


open Set MeasureTheory ProbabilityTheory
open scoped Topology ENNReal

theorem finite_regions_wave_sign_expectation {I P X : Type*} [Fintype I] [Fintype P]
    [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X]
    (w : X → ℝ) (U : I → Fin 3 → X → ℂ)
    (hw : Continuous w) (hU : ∀ i j, Continuous (U i j))
    (S : P → Fin 3 → X → X) (hS : ∀ a j, Continuous (S a j))
    (ν : P → Measure X) [∀ a, IsFiniteMeasure (ν a)]
    (q : P → ℝ) (hq : ∀ a, 0 ≤ q a) (p : ℝ)
    (hprob : ∀ a, ∀ᵐ x ∂ν a, ∃ j, ENNReal.ofReal p ≤
      (Measure.pi (fun _ : I => Measure.pi (fun _ : Fin 3 => stdGaussian ℂ)))
        {γ | finiteWaveSuperposition w U γ x * finiteWaveSuperposition w U γ (S a j x) < 0}) :
    let μ := Measure.pi (fun _ : I => Measure.pi (fun _ : Fin 3 => stdGaussian ℂ))
    let V := ∑ a, q a*(ν a univ).toReal
    let F := fun γ => ∑ a, q a*∑ j, (ν a {x | finiteWaveSuperposition w U γ x *
      finiteWaveSuperposition w U γ (S a j x) < 0}).toReal
    Integrable F μ ∧ (∀ γ, 0 ≤ F γ ∧ F γ ≤ 3*V) ∧
      p*V ≤ ∫ γ, F γ ∂μ := by
  classical
  let μ := Measure.pi (fun _ : I => Measure.pi (fun _ : Fin 3 => stdGaussian ℂ))
  let f := fun a γ => ∑ j, (ν a {x | finiteWaveSuperposition w U γ x *
    finiteWaveSuperposition w U γ (S a j x) < 0}).toReal
  have hh (a : P) := actual_wave_sign_expectation w U hw hU (S a) (hS a) (ν a) p (hprob a)
  change (∀ a : P, Integrable (f a) μ ∧ (∀ γ, 0 ≤ f a γ ∧
    f a γ ≤ (Fintype.card (Fin 3) : ℝ)*(ν a univ).toReal) ∧
    p*(ν a univ).toReal ≤ ∫ γ, f a γ ∂μ) at hh
  dsimp only
  refine ⟨integrable_finsetSum _ (fun a _ => (hh a).1.const_mul (q a)),?_,?_⟩
  · intro γ
    refine ⟨Finset.sum_nonneg (fun a _ => mul_nonneg (hq a) ((hh a).2.1 γ).1),?_⟩
    calc
      _ ≤ ∑ a, q a*(3*(ν a univ).toReal) := by
        apply Finset.sum_le_sum; intro a ha
        apply mul_le_mul_of_nonneg_left _ (hq a)
        simpa only [Fintype.card_fin,Nat.cast_ofNat] using ((hh a).2.1 γ).2
      _ = _ := by rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro a ha; ring
  · rw [integral_finsetSum _ (fun a _ => (hh a).1.const_mul (q a)),Finset.mul_sum]
    apply Finset.sum_le_sum
    intro a ha
    rw [integral_const_mul]
    calc
      _ = q a*(p*(ν a univ).toReal) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (hh a).2.2 (hq a)

end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Limits_CompactActualWavesSubregionsSupported
attribute [-instance] _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_acg _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_mod _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_nacg _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_ns _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_snacg _root_.OAI.YauCounterexamples.MetricIntegralAtlas.volumeMeasure_finite _root_.OAI.YauCounterexamples.MetricIntegralAtlas.volumeMeasure_openPos _root_.OAI.YauCounterexamples.circle_dimension_fact _root_.OAI.YauCounterexamples.normalCoordinateVolume_finiteOnCompacts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples


open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set Filter Metric
open scoped Topology InnerProductSpace
open Set Filter Function Metric
open scoped Topology
open Set Filter Function Metric
open scoped Topology
open Set Filter Manifold
open scoped Topology ContDiff
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology ContDiff ENNReal

theorem compact_actual_waves_subregions_supported_oai
    (g : SmoothMetric NormalWaveSpace NormalWaveSpace)
    {K : Set NormalWaveSpace} (hK : IsCompact K)
    {O : Set NormalWaveSpace} (hO : IsOpen O) (hKO : K ⊆ O) :
    ∃ ε > 0, ε ≤ 1 ∧ ∃ p₀ > 0,
    ∀ φ : NormalWaveSpace → ℝ, ContDiff ℝ ∞ φ →
    (∀ x ∈ K, fderiv ℝ φ x ≠ 0 → actualProfileStrict g φ x) →
    (∀ x ∈ K, fderiv ℝ φ x = 0 →
      ∃ P : Submodule ℝ NormalWaveSpace, Module.finrank ℝ P = 2 ∧
        ∀ v ∈ P, v ≠ 0 → 0 < actualCoordinateHessian g φ x v v) →
    ∀ m D : ℕ, ∀ T₀ H : ℝ, 0 ≤ T₀ → 0 ≤ H → ∃ c₀ > 0, ∃ T > 0, ∃ c > 0, ∃ Q > 0,
    ∃ N : ℝ, 2 ≤ N ∧ ∀ s : ℝ, N ≤ s →
    let n := s^4
    ∃ t : Finset (Fin 3 → ℝ), ∃ p : t → metricFrameSet g K,
    ∃ U : t → Fin 3 → NormalWaveSpace → ℂ,
      (∀ i ℓ, tsupport (U i ℓ) ⊆ O) ∧
      (t.card : ℝ) ≤ Q*n^3 ∧
      (∀ i ℓ, ContDiff ℝ ∞ (U i ℓ) ∧ HasCompactSupport (U i ℓ) ∧
        U i ℓ (p i).1.1 = Complex.exp ((n : ℂ)*(φ (p i).1.1 : ℂ)) ∧
        ∀ y : NormalWaveSpace, ∀ k ≤ max m 2,
          ‖iteratedFDeriv ℝ k (U i ℓ) y‖ ≤ T*n^k*Real.exp (n*φ y)*Real.exp (-c*n*‖y-(p i).1.1‖^2) ∧
          ‖iteratedFDeriv ℝ k (fun w => complexLaplaceBeltrami g (U i ℓ) w +
            (n : ℂ)*((n : ℂ)+2)*U i ℓ w) y‖ ≤ T*(n^(D+1))⁻¹*Real.exp (n*φ y)) ∧
      ∀ S : Set (Fin 3 → ℝ), Convex ℝ S →
        ∀ E : Set (Fin 3 → ℝ), E ⊆ S → E ⊆ normalWaveEquiv.symm '' K →
        ∀ w : NormalWaveSpace → ℝ, ContDiff ℝ ∞ w →
        ∀ W : (Fin 3 → ℝ) → ℝ, Differentiable ℝ W → (∀ y, 0 < W y) →
        (∀ y ∈ S, Real.exp (n*φ (normalWaveEquiv y)) ≤ W y) →
        (∀ y ∈ E, W y ≤ (1+n^6)*Real.exp (n*φ (normalWaveEquiv y))) →
        (∀ y ∈ S, ∀ j ≤ 2, ‖iteratedFDeriv ℝ j (w ∘ normalWaveEquiv) y‖ ≤ T₀*n^j*W y) →
        (∀ y ∈ S, ‖fderiv ℝ W y‖ ≤ H*n*W y) →
        ∀ J : Set NormalWaveSpace, J ⊆ K →
        (∀ y ∈ J, |w y| ≤ c₀*Real.exp (n*φ y)) →
        ∀ (P : Type) [Fintype P] (ℓ q : P → ℝ), (∀ a, 0 ≤ q a) →
        ∀ ν : P → Measure NormalWaveSpace, ∀ _ : ∀ a, IsFiniteMeasure (ν a),
        0 < ∑ a, q a*(ν a univ).toReal →
        (∀ a, ∀ᵐ x ∂ν a, x ∈ J ∧ profileFrequencyScale g φ x ≤ ℓ a ∧
          ℓ a ≤ 2*profileFrequencyScale g φ x ∧ (∀ j, packetAxisShift x n ε (ℓ a) j ∈ J)) →
        ∃ γ : t → Fin 3 → ℂ, (∀ i j, ‖γ i j‖ ≤ n) ∧
          (∀ y ∈ E, 1/n^110 ≤
            ‖realWaveJet n (W y) (finiteWaveSuperposition (w ∘ normalWaveEquiv)
              (fun i j => U i j ∘ normalWaveEquiv) γ) y‖) ∧
          (p₀/2)*(∑ a, q a*(ν a univ).toReal) <
            ∑ a, q a*∑ j : Fin 3, (ν a {x | finiteWaveSuperposition w U γ x *
              finiteWaveSuperposition w U γ (packetAxisShift x n ε (ℓ a) j) < 0}).toReal := by
  classical
  obtain ⟨ε,hε,hε1,p₀,hp₀,hdata⟩ := compact_actual_sign_noncancellation_supported g hK hO hKO
  refine ⟨ε,hε,hε1,p₀,hp₀,?_⟩
  intro φ hφ hnc hcrit m D T₀ H hT₀ hH
  obtain ⟨c₀,hc₀,T,hT,c,hc,A,hA,Q,hQ,N,hN,hdata⟩ := hdata φ hφ hnc hcrit m D T₀ H hT₀ hH
  refine ⟨c₀,hc₀,T,hT,c,hc,Q,hQ,max N (12*A/p₀+1),le_max_of_le_left hN,?_⟩
  intro s hs
  have hsN : N ≤ s := (le_max_left _ _).trans hs
  have hs1 : 1 ≤ s := (by linarith : (1:ℝ) ≤ N).trans hsN
  have hs4 : s ≤ s^4 := by simpa only [pow_one] using pow_le_pow_right₀ hs1 (show 1 ≤ 4 by omega)
  let n := s^4
  have hn1 : 1 ≤ n := hs1.trans hs4
  have hn0 : 0 < n := zero_lt_one.trans_le hn1
  have hAn : A/n^5 < p₀/6 := by
    have hlarge : 12*A/p₀ < n := (lt_add_one _).trans_le (((le_max_right _ _).trans hs).trans hs4)
    have hm := (div_lt_iff₀ hp₀).mp hlarge
    have hd : A/n < p₀/6 := (div_lt_iff₀ hn0).mpr (by nlinarith)
    apply lt_of_le_of_lt _ hd
    exact div_le_div_of_nonneg_left hA.le hn0 (by
      simpa only [pow_one] using pow_le_pow_right₀ hn1 (show 1 ≤ 5 by omega))
  obtain ⟨t,p,U,hSupport,ht,hU,hbad,hsign⟩ := hdata s hsN
  refine ⟨t,p,U,hSupport,ht,hU,?_⟩
  intro S hS E hES hEK w hw W hW hW0 hWlower hWupper hwbound hlog J hJK hb P _ ℓ q hq ν _ hv hregion
  let μ := Measure.pi (fun _ : t => Measure.pi (fun _ : Fin 3 => stdGaussian ℂ))
  let Bad : Set (t → Fin 3 → ℂ) := {γ | (∃ i j, n < ‖γ i j‖) ∨ ∃ y ∈ E,
    ‖realWaveJet n (W y) (finiteWaveSuperposition (w ∘ normalWaveEquiv)
      (fun i j => U i j ∘ normalWaveEquiv) γ) y‖ < 1/n^110}
  have hBad : μ Bad ≤ ENNReal.ofReal (A/n^5) :=
    hbad S hS E hES hEK w hw W hW hW0 hWlower hWupper hwbound hlog
  let V := ∑ a, q a*(ν a univ).toReal
  let F := fun γ => ∑ a, q a*∑ j : Fin 3, (ν a {x | finiteWaveSuperposition w U γ x *
    finiteWaveSuperposition w U γ (packetAxisShift x n ε (ℓ a) j) < 0}).toReal
  have hshift (a : P) (j : Fin 3) : Continuous (fun x => packetAxisShift x n ε (ℓ a) j) :=
    continuous_id.add continuous_const
  obtain ⟨hF,hFb,hFe⟩ := finite_regions_wave_sign_expectation w U hw.continuous
    (fun i j => (hU i j).1.continuous) (fun a j x => packetAxisShift x n ε (ℓ a) j) hshift ν q hq p₀ (by
      intro a
      filter_upwards [hregion a] with x hx
      have hb' : ∀ y ∈ K, |(J.indicator w) y| ≤ c₀*Real.exp (n*φ y) := by
        intro y _
        by_cases hy : y ∈ J
        · simpa only [Set.indicator_of_mem hy] using hb y hy
        · simp only [Set.indicator_of_notMem hy, abs_zero]
          positivity
      obtain ⟨j,hj⟩ := hsign (J.indicator w) hb' x (hJK hx.1) (ℓ a)
        hx.2.1 hx.2.2.1 (fun j => hJK (hx.2.2.2 j))
      refine ⟨j,?_⟩
      simpa only [finiteWaveSuperposition, Set.indicator_of_mem hx.1,
        Set.indicator_of_mem (hx.2.2.2 j)] using hj)
  have htBad : (μ Bad).toReal < p₀/6 := by
    apply lt_of_le_of_lt _ hAn
    simpa only [ENNReal.toReal_ofReal (by positivity : 0 ≤ A/n^5)] using
      ENNReal.toReal_mono ENNReal.ofReal_ne_top hBad
  obtain ⟨γ,hγ,hscore⟩ := exists_large_score_avoiding μ F hF Bad
    (3*V) (p₀*V) ((p₀/2)*V)
    (fun γ => (hFb γ).2)
    (by positivity) hFe (by
      have hm := mul_lt_mul_of_pos_left htBad (show 0 < 3*V by dsimp [V]; positivity)
      nlinarith [mul_pos hp₀ hv])
  exact ⟨γ,(fun i j => le_of_not_gt (fun hh => hγ (Or.inl ⟨i,j,hh⟩))),
    (fun y hy => le_of_not_gt (fun hh => hγ (Or.inr ⟨y,hy,hh⟩))),hscore⟩


end YauCounterexamples
end

end OAI
end

theorem solution : type_of% @OAI.YauCounterexamples.compact_actual_waves_subregions_supported_oai := @OAI.YauCounterexamples.compact_actual_waves_subregions_supported_oai
