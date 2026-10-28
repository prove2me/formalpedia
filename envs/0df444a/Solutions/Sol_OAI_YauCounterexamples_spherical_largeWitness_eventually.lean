-- Prove2me | solution 1 for OAI.YauCounterexamples.spherical_largeWitness_eventually
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T12:48:03.775332+00:00
-- url     : https://prove2.me/submissions/642abeee-03f4-40c3-9511-ea21aab0b98a

import Mathlib
import Definitions.Def_SmoothYau
import Definitions.Def_OAIQ070A009
import Theorems.Thm_OAI_YauCounterexamples_CompactMetricAtlas_actual_simple_eigenpair_persistence
import Theorems.Thm_OAI_YauCounterexamples_nonempty_compactMetricAtlas

section
-- module Solutions.OAIQ070_YAU.SmoothYau_NodalMeasure_ExtrusionEquiv
attribute [-instance] _root_.OAI.YauCounterexamples.circle_dimension_fact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section
open Set Filter MeasureTheory Metric
open scoped Topology ENNReal NNReal
namespace YauCounterexamples.SignTests

theorem lowerSemicontinuous_measure_neg {A X : Type*} [TopologicalSpace A]
    [FirstCountableTopology A] [MeasurableSpace X] (μ : Measure X)
    (F : A → X → ℝ) (hF : ∀ a, Measurable (F a))
    (hc : ∀ x, Continuous (fun a => F a x)) :
    LowerSemicontinuous (fun a => μ {x | F a x < 0}) := by
  let G : A → X → ℝ≥0∞ := fun a => {x | F a x < 0}.indicator (fun _ => 1)
  have hG (a : A) : Measurable (G a) :=
    measurable_const.indicator (measurableSet_lt (hF a) measurable_const)
  have hGl (x : X) : LowerSemicontinuous (fun a => G a x) := by
    have ho : IsOpen {a | F a x < 0} := isOpen_lt (hc x) continuous_const
    exact ho.lowerSemicontinuous_indicator (show (0 : ℝ≥0∞) ≤ 1 from zero_le)
  have hGi (a : A) : ∫⁻ x, G a x ∂μ = μ {x | F a x < 0} := by
    dsimp only [G]
    rw [lintegral_indicator (measurableSet_lt (hF a) measurable_const)]
    simp
  apply lowerSemicontinuous_iff_le_liminf.mpr
  intro a
  rw [← hGi a]
  calc
    ∫⁻ x, G a x ∂μ ≤ ∫⁻ x, liminf (fun a' => G a' x) (𝓝 a) ∂μ :=
      lintegral_mono (fun x => (hGl x).le_liminf a)
    _ ≤ liminf (fun a' => ∫⁻ x, G a' x ∂μ) (𝓝 a) := lintegral_liminf_le hG
    _ = liminf (fun a' => μ {x | F a' x < 0}) (𝓝 a) := by simp_rw [hGi]

theorem lowerSemicontinuous_signMass {A X M : Type*} [TopologicalSpace A]
    [FirstCountableTopology A] [MeasurableSpace X] (μ : Measure X)
    (D : Set X) (a b : X → M) (F : A → M → ℝ)
    (hFa : ∀ p, Measurable (fun x => F p (a x)))
    (hFb : ∀ p, Measurable (fun x => F p (b x)))
    (hc : ∀ x, Continuous (fun p => F p x)) :
    LowerSemicontinuous (fun p => signMass μ D a b (F p)) := by
  have h := lowerSemicontinuous_measure_neg (μ.restrict D)
    (fun p x => F p (a x) * F p (b x))
    (fun p => (hFa p).mul (hFb p)) (fun x => (hc _).mul (hc _))
  have heq (p : A) : (μ.restrict D) {x | F p (a x) * F p (b x) < 0} =
      signMass μ D a b (F p) := by
    have hm : MeasurableSet {x | F p (a x) * F p (b x) < 0} :=
      measurableSet_lt ((hFa p).mul (hFb p)) measurable_const
    rw [Measure.restrict_apply hm]
    unfold signMass
    congr 1
    ext x
    simp only [mem_inter_iff, mem_ofPred_eq, oppositeSet]
    exact and_comm
  simpa only [heq] using h

theorem lowerSemicontinuous_signCertificate {A ι J : Type*}
    [TopologicalSpace A] [FirstCountableTopology A]
    [Fintype ι] [DecidableEq ι] [Fintype J]
    (P : J → Set (ι → ℝ)) (d : J → ℝ) (F : A → (ι → ℝ) → ℝ)
    (hm : ∀ a, Measurable (F a)) (hc : ∀ x, Continuous (fun a => F a x)) :
    LowerSemicontinuous (fun a => signCertificate P d (F a)) := by
  apply lowerSemicontinuous_sum
  intro p _
  apply lowerSemicontinuous_sum
  intro i _
  have hb : Measurable (fun x : ι → ℝ => x + Pi.single i (d p)) :=
    (continuous_id.add continuous_const).measurable
  have h := lowerSemicontinuous_signMass ((ENNReal.ofReal (d p))⁻¹ • volume)
    {x | x ∈ P p ∧ x + Pi.single i (d p) ∈ P p}
    id (fun x => x + Pi.single i (d p)) F
    (fun a => hm a) (fun a => (hm a).comp hb) hc
  simpa only [signMass, Measure.smul_apply, smul_eq_mul] using h

end YauCounterexamples.SignTests
end

open Set Function MeasureTheory
open scoped ENNReal
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Smoothness_LocalIntegrationParts
attribute [-instance] _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_acg _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_mod _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_nacg _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_ns _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_snacg _root_.OAI.YauCounterexamples.MetricIntegralAtlas.volumeMeasure_finite _root_.OAI.YauCounterexamples.MetricIntegralAtlas.volumeMeasure_openPos _root_.OAI.YauCounterexamples.circle_dimension_fact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples

section
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
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M]

lemma contDiffAt_metricFirstCoefficient (g : SmoothMetric E M) (p : M) (j : CoordIndex E)
    {y : E} (hy : y ∈ (chartAt E p).target) :
    ContDiffAt ℝ ∞ (metricFirstCoefficient g p j) y := by
  have hd := (contDiffOn_metricDensity g p).contDiffAt ((chartAt E p).open_target.mem_nhds hy)
  have hn : Real.sqrt (metricCoefficients g p y).det ≠ 0 :=
    (Real.sqrt_pos.mpr (metricCoefficients_det_pos g p hy)).ne'
  apply (hd.inv hn).mul
  apply ContDiffAt.sum
  intro i _
  have ha := (contDiffOn_metricInverse g p i j).contDiffAt ((chartAt E p).open_target.mem_nhds hy)
  exact ((hd.mul ha).fderiv_right (m := ∞) (by simp)).clm_apply contDiffAt_const

end

section
open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open scoped Manifold ContDiff Matrix.Norms.Elementwise
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M]


theorem exists_smooth_metric_coefficients_on_compact (g : SmoothMetric E M) (p : M)
    {K : Set E} (hK : IsCompact K) (hKs : K ⊆ (chartAt E p).target) :
    ∃ (a : CoordIndex E → CoordIndex E → E → ℝ) (c : CoordIndex E → E → ℝ),
      (∀ i j, ContDiff ℝ ∞ (a i j)) ∧ (∀ i, ContDiff ℝ ∞ (c i)) ∧
      (∀ y ∈ K, (∀ i j, a i j y = (metricCoefficients g p y)⁻¹ i j) ∧
        (∀ i, c i y = metricFirstCoefficient g p i y)) := by
  let φ : E → Matrix (CoordIndex E) (CoordIndex E) ℝ × (CoordIndex E → ℝ) :=
    fun y => ((metricCoefficients g p y)⁻¹, fun i => metricFirstCoefficient g p i y)
  have hφ : ContDiffOn ℝ ∞ φ (chartAt E p).target := by
    apply ContDiffOn.prodMk
    · exact contDiffOn_pi.mpr (fun i => contDiffOn_pi.mpr (fun j =>
        contDiffOn_metricInverse g p i j))
    · exact contDiffOn_pi.mpr (fun i y hy =>
        (contDiffAt_metricFirstCoefficient g p i hy).contDiffWithinAt)
  obtain ⟨ψ, hψ, he⟩ := smooth_extension_near_compact hK (chartAt E p).open_target hKs hφ
  refine ⟨fun i j y => (ψ y).1 i j, fun i y => (ψ y).2 i,
    fun i j => contDiff_pi.mp (contDiff_pi.mp hψ.fst i) j,
    fun i => contDiff_pi.mp hψ.snd i, ?_⟩
  intro y hy
  have hh := he.self_of_nhdsSet hy
  exact ⟨fun i j => congrFun (congrFun (congrArg Prod.fst hh.symm) i) j,
    fun i => congrFun (congrArg Prod.snd hh.symm) i⟩


end

open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open Set Filter Manifold Bundle MeasureTheory NNReal
open scoped Topology ContDiff ENNReal
open Set Filter Topology NNReal
open Set Filter Module
open scoped Topology
open Set Filter MeasureTheory Manifold Function
open scoped Topology ContDiff


end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Smoothness_ExistsFinitePatchPartition
attribute [-instance] _root_.OAI.YauCounterexamples.circle_dimension_fact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open Set Function Filter
open scoped Topology Manifold ContDiff
namespace YauCounterexamples
section PatchCutoffs
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M]

theorem exists_finite_patch_partition (U : M → Set M) (hU : ∀ p, IsOpen (U p))
    (hp : ∀ p, p ∈ U p) :
    ∃ t : Finset M, ∃ ρ : SmoothPartitionOfUnity t 𝓘(ℝ, E) M univ,
      ρ.IsSubordinate (fun i => U (i : M)) := by
  classical
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover U hU
    (by intro x _; exact mem_iUnion_of_mem x (hp x))
  refine ⟨t, ?_⟩
  apply SmoothPartitionOfUnity.exists_isSubordinate (I := 𝓘(ℝ, E)) isClosed_univ
    (fun i : t => U (i : M)) (fun i => hU (i : M))
  intro x hx
  obtain ⟨p, hp, hpx⟩ := mem_iUnion₂.mp (ht hx)
  exact mem_iUnion_of_mem ⟨p, hp⟩ hpx

end PatchCutoffs

end YauCounterexamples


end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Geometry_CoefficientGradientApply
attribute [-instance] _root_.OAI.YauCounterexamples.MetricIntegralAtlas.volumeMeasure_finite _root_.OAI.YauCounterexamples.MetricIntegralAtlas.volumeMeasure_openPos _root_.OAI.YauCounterexamples.circle_dimension_fact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples

section
open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open Set Filter Manifold Bundle MeasureTheory NNReal
open scoped Topology ContDiff ENNReal
open Set Filter Topology NNReal
open Set Filter Module
open scoped Topology
open Set Filter MeasureTheory Manifold Function
open scoped Topology ContDiff BoundedContinuousFunction
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M]

omit [MeasurableSpace E] [BorelSpace E] in
lemma nonempty_metricIntegralAtlas : Nonempty (MetricIntegralAtlas (E := E) (M := M)) := by
  obtain ⟨t, ρ, hρ⟩ := exists_finite_patch_partition (E := E)
    (fun p : M => (chartAt E p).source) (fun p => (chartAt E p).open_source) (mem_chart_source E)
  exact ⟨⟨t, ρ, hρ⟩⟩

end

open MeasureTheory TopologicalSpace
open scoped Distributions ContDiff



end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Smoothness_ContinuousSobolevFirstDerivative
attribute [-instance] _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_acg _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_mod _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_nacg _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_ns _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_snacg _root_.OAI.YauCounterexamples.circle_dimension_fact _root_.OAI.YauCounterexamples.manifoldSobolev_completeSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples

open Set Filter Function Manifold
open scoped Topology ContDiff BoundedContinuousFunction
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
variable {s : ℝ} (h1 : Module.finrank ℝ E < 2*(s-1))
  (h0 : Module.finrank ℝ E < 2*s)
include h1 in

lemma continuous_sobolev_firstDerivative :
    Continuous (fun z : FourierSobolevSpace E ℂ s × E =>
      fderiv ℝ (sobolevRepresentative h0 z.1 : E → ℂ) z.2) := by
  apply continuous_clm_apply.mpr
  intro v
  simp_rw [← sobolevDerivative_representative h1 h0]
  exact (((sobolevRepresentative h1).continuous.comp
    (sobolevDerivative s v).continuous).comp continuous_fst).eval continuous_snd

include h1 in
lemma fderiv_real_sobolevRepresentative (u : FourierSobolevSpace E ℂ s) (x : E) :
    fderiv ℝ (fun y => (sobolevRepresentative h0 u y).re) x =
      Complex.reCLM ∘L fderiv ℝ (sobolevRepresentative h0 u : E → ℂ) x := by
  exact (Complex.reCLM.hasFDerivAt.comp x
    (((contDiff_sobolevRepresentative 1 (by simpa using h1) h0 u).differentiable
      (by norm_num)).differentiableAt.hasFDerivAt)).fderiv

include h1 in
lemma continuous_real_sobolev_firstJet :
    Continuous (fun z : FourierSobolevSpace E ℂ s × E =>
      ((sobolevRepresentative h0 z.1 z.2).re,
        fderiv ℝ (fun y => (sobolevRepresentative h0 z.1 y).re) z.2)) := by
  simp_rw [fderiv_real_sobolevRepresentative h1 h0]
  exact (Complex.continuous_re.comp
    (((sobolevRepresentative h0).continuous.comp continuous_fst).eval continuous_snd)).prodMk
      (continuous_const.clm_comp (continuous_sobolev_firstDerivative h1 h0))

end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Smoothness_ChartDerivativeNeZeroTransfer
attribute [-instance] _root_.OAI.YauCounterexamples.MetricIntegralAtlas.volumeMeasure_finite _root_.OAI.YauCounterexamples.MetricIntegralAtlas.volumeMeasure_openPos _root_.OAI.YauCounterexamples.circle_dimension_fact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples

section
open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open scoped Manifold BoundedContinuousFunction
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M]
namespace CompactMetricAtlas
variable {g : SmoothMetric E M} {k : ℕ} {hs : Module.finrank ℝ E < 2 * (2 * (k : ℝ))}
variable (A : CompactMetricAtlas g k hs)

omit [T2Space M] in
lemma nonempty_patchCoefficients (i : A.t) : Nonempty (A.PatchCoefficients i) := by
  obtain ⟨a, c, ha, hc, he⟩ := exists_smooth_metric_coefficients_on_compact g (A.p i)
    (isCompact_closedBall ((chartAt E (A.p i)) (A.p i)) (A.localInverse i).radius)
    (A.localInverse i).in_target
  exact ⟨⟨a, c, ha, hc, fun x hx => (he x (A.χcoord_support i hx)).1,
    fun x hx => (he x (A.χcoord_support i hx)).2⟩⟩

end CompactMetricAtlas


end

section
open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open scoped Manifold BoundedContinuousFunction
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M]
namespace CompactMetricAtlas
variable {g : SmoothMetric E M} {k : ℕ} {hs : Module.finrank ℝ E < 2 * (2 * (k : ℝ))}
variable (A : CompactMetricAtlas g k hs)

omit [T2Space M] in
lemma errorBound_tendsto (B : ∀ i, A.PatchCoefficients i) :
    Tendsto (A.errorBound B) atTop (𝓝 0) := by
  have hi (i : A.t) : Tendsto (fun α : ℝ =>
      (‖A.patchErrorTail i (B i)‖ * ((A.localInverse i).bound *
        ‖metricPatchSource (E := E) (A.p i) (A.localInverse i).radius k‖)) *
        (Real.sqrt (α * (A.localInverse i).radius ^ 2))⁻¹) atTop (𝓝 0) := by
    have hm : Tendsto (fun α : ℝ => α * (A.localInverse i).radius ^ 2) atTop atTop :=
      tendsto_id.atTop_mul_const (sq_pos_of_pos (A.localInverse i).radius_pos)
    simpa only [mul_zero, Function.comp_def] using! tendsto_const_nhds.mul
      (tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp hm))
  simpa only [errorBound, Finset.sum_const_zero] using! tendsto_finsetSum Finset.univ (fun i _ => hi i)

omit [T2Space M] [CompactSpace M] in
lemma eventually_admissible : ∀ᶠ α : ℝ in atTop, ∀ i, 1 ≤ α * (A.localInverse i).radius ^ 2 := by
  apply Filter.eventually_all.mpr
  intro i
  exact (tendsto_id.atTop_mul_const (sq_pos_of_pos (A.localInverse i).radius_pos)).eventually
    (eventually_ge_atTop 1)

omit [T2Space M] in
lemma exists_parametrix_threshold (B : ∀ i, A.PatchCoefficients i) :
    ∃ a : ℝ, 1 ≤ a ∧ ∀ α ≥ a,
      (∀ i, 1 ≤ α * (A.localInverse i).radius ^ 2) ∧ A.errorBound B α ≤ 1 / 2 := by
  have he : ∀ᶠ α : ℝ in atTop, 1 ≤ α ∧
      (∀ i, 1 ≤ α * (A.localInverse i).radius ^ 2) ∧ A.errorBound B α ≤ 1 / 2 := by
    filter_upwards [eventually_ge_atTop (1 : ℝ), A.eventually_admissible,
      (A.errorBound_tendsto B).eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))]
      with α hα ha he
    exact ⟨hα, ha, he.le⟩
  obtain ⟨a, ha⟩ := eventually_atTop.mp he
  exact ⟨a, (ha a le_rfl).1, fun α hα => (ha α hα).2⟩

end CompactMetricAtlas


end

section
open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open Set Filter Manifold Bundle MeasureTheory NNReal
open scoped Topology ContDiff ENNReal
open scoped Manifold BoundedContinuousFunction
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M]
namespace CompactMetricAtlas
variable {g : SmoothMetric E M} {k : ℕ} {hs : Module.finrank ℝ E < 2 * (2 * (k : ℝ))}
variable (A : CompactMetricAtlas g k hs)

omit [T2Space M] in
lemma realValue_C2 (u : A.realH (2 * ((k + 1 : ℕ) : ℝ))) :
    ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) 2 (A.realValue (2 * ((k + 1 : ℕ) : ℝ)) u) :=
  Complex.reCLM.contMDiff.comp (A.representative_C2 u)

end CompactMetricAtlas

end

open Set Filter Function Manifold
open scoped Topology ContDiff BoundedContinuousFunction
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [CompactSpace M] [T2Space M]
omit [MeasurableSpace E] [BorelSpace E] [CompactSpace M] [T2Space M] in
lemma chart_derivative_ne_zero_transfer {u : M → ℝ}
    (hu : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) 2 u)
    (p q x : M) (hpx : x ∈ (chartAt E p).source) (hqx : x ∈ (chartAt E q).source)
    (hd : fderiv ℝ (u ∘ (chartAt E q).symm) ((chartAt E q) x) ≠ 0) :
    fderiv ℝ (u ∘ (chartAt E p).symm) ((chartAt E p) x) ≠ 0 := by
  intro hz
  apply hd
  apply ContinuousLinearMap.ext
  intro v
  rw [← (Module.finBasis ℝ E).sum_repr v]
  simp only [map_sum,map_smul]
  have hi (i) := fderiv_inChart_change_C2 hu p q ((chartAt E q).map_source hqx)
    (by simpa only [(chartAt E q).left_inv hqx] using hpx) i
  have hi0 (i) : fderiv ℝ (u ∘ (chartAt E q).symm) ((chartAt E q) x)
      (Module.finBasis ℝ E i) = 0 := by
    rw [hi]
    simp only [chartTransition,Function.comp_apply,(chartAt E q).left_inv hqx,hz,zero_apply,
      zero_mul,Finset.sum_const_zero]
  simp only [hi0,smul_zero,Finset.sum_const_zero,zero_apply]
namespace CompactMetricAtlas
variable {g : SmoothMetric E M} {k : ℕ} {hs : Module.finrank ℝ E < 2*(2*(k:ℝ))}
variable (A : CompactMetricAtlas g k hs)
omit [T2Space M] in
lemma localization_real_germ (i : A.t) {x : M} (hx : x ∈ tsupport (A.η i))
    (u : A.realH (2*((k+1:ℕ):ℝ)))
    (ht : Module.finrank ℝ E < 2*(2*((k+1:ℕ):ℝ))) :
    (fun y => (sobolevRepresentative ht (A.cutoffLocalization (A.p i) (A.χ i)
      (A.chart_χ i) (A.smooth_χ i) (k+1) u) y).re) =ᶠ[𝓝 ((chartAt E (A.p i)) x)]
      A.realValue (2*((k+1:ℕ):ℝ)) u ∘ (chartAt E (A.p i)).symm := by
  have hc := chartLocalize_eventually_eq (A.p i) (A.χ i)
    (A.representative (2*((k+1:ℕ):ℝ)) u) (A.chart_η i hx)
    ((A.one_χ i).filter_mono (nhds_le_nhdsSet hx))
  filter_upwards [hc] with y hy
  rw [A.cutoffLocalization_representative]
  exact congrArg Complex.re hy

omit [CompactSpace M] [T2Space M] in
lemma highIndex_bound_one : Module.finrank ℝ E < 2*(A.highIndex-1) := by
  have h := hs
  dsimp [highIndex]; push_cast; linarith

omit [T2Space M] in
lemma localizedFirstJet_continuous (i : A.t) :
    Continuous (fun z : A.realH A.highIndex × E => A.localizedFirstJet i z.1 z.2) := by
  let L : A.realH A.highIndex →L[ℝ] FourierSobolevSpace E ℂ A.highIndex :=
    A.cutoffLocalization (A.p i) (A.χ i) (A.chart_χ i) (A.smooth_χ i) (k+1) ∘L
      (A.realH A.highIndex).subtypeL
  have h := (continuous_real_sobolev_firstJet A.highIndex_bound_one A.highIndex_bound).comp
    ((L.continuous.comp continuous_fst).prodMk continuous_snd)
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  rfl

omit [T2Space M] in
lemma localizedFirstJet_ne_zero (i : A.t) (u : A.realH A.highIndex)
    (hreg : ∀ x, A.realValue A.highIndex u x = 0 →
      fderiv ℝ (A.realValue A.highIndex u ∘ (chartAt E x).symm) ((chartAt E x) x) ≠ 0)
    {x : M} (hx : x ∈ tsupport (A.η i)) :
    A.localizedFirstJet i u ((chartAt E (A.p i)) x) ≠ 0 := by
  have hg := A.localization_real_germ i hx u A.highIndex_bound
  intro hz
  have hf : A.realValue A.highIndex u x = 0 := by
    have hh := congrArg Prod.fst hz
    change A.localizedRealValue i u ((chartAt E (A.p i)) x) = 0 at hh
    rw [localizedRealValue,hg.eq_of_nhds,Function.comp_apply,
      (chartAt E (A.p i)).left_inv (A.chart_η i hx)] at hh
    exact hh
  apply chart_derivative_ne_zero_transfer (A.realValue_C2 u) (A.p i) x x
    (A.chart_η i hx) (mem_chart_source E x) (hreg x hf)
  rw [← hg.fderiv_eq]
  exact congrArg Prod.snd hz

omit [T2Space M] in
lemma eventually_localizedFirstJet_ne_zero (i : A.t) (u : A.realH A.highIndex)
    (hreg : ∀ x, A.realValue A.highIndex u x = 0 →
      fderiv ℝ (A.realValue A.highIndex u ∘ (chartAt E x).symm) ((chartAt E x) x) ≠ 0) :
    ∀ᶠ v in 𝓝 u, ∀ y ∈ (chartAt E (A.p i)) '' tsupport (A.η i),
      A.localizedFirstJet i v y ≠ 0 := by
  have hK : IsCompact ((chartAt E (A.p i)) '' tsupport (A.η i)) :=
    (isClosed_tsupport (A.η i)).isCompact.image_of_continuousOn
      ((chartAt E (A.p i)).continuousOn.mono (A.chart_η i))
  apply hK.eventually_forall_of_forall_eventually
  rintro y ⟨x,hx,rfl⟩
  have hc : ContinuousAt (fun z : A.realH A.highIndex × E => A.localizedFirstJet i z.1 z.2)
      (u,(chartAt E (A.p i)) x) := (A.localizedFirstJet_continuous i).continuousAt
  exact hc.eventually (isOpen_ne.mem_nhds (A.localizedFirstJet_ne_zero i u hreg hx))

omit [T2Space M] in
lemma regular_of_localizedFirstJet (v : A.realH A.highIndex)
    (hv : ∀ i, ∀ y ∈ (chartAt E (A.p i)) '' tsupport (A.η i),
      A.localizedFirstJet i v y ≠ 0) :
    ∀ x, A.realValue A.highIndex v x = 0 →
      fderiv ℝ (A.realValue A.highIndex v ∘ (chartAt E x).symm) ((chartAt E x) x) ≠ 0 := by
  classical
  intro x hx
  obtain ⟨i,_,hi⟩ := Finset.exists_ne_zero_of_sum_ne_zero
    (show (∑ i, A.η i x) ≠ 0 from (A.sum_η x).trans_ne one_ne_zero)
  have his : x ∈ tsupport (A.η i) := subset_tsupport _ hi
  have hg := A.localization_real_germ i his v A.highIndex_bound
  have hn : fderiv ℝ (A.realValue A.highIndex v ∘ (chartAt E (A.p i)).symm)
      ((chartAt E (A.p i)) x) ≠ 0 := by
    intro hz
    apply hv i _ ⟨x,his,rfl⟩
    apply Prod.ext
    · change A.localizedRealValue i v ((chartAt E (A.p i)) x) = 0
      rw [localizedRealValue,hg.eq_of_nhds,Function.comp_apply,
        (chartAt E (A.p i)).left_inv (A.chart_η i his)]
      exact hx
    · exact hg.fderiv_eq.trans hz
  exact chart_derivative_ne_zero_transfer (A.realValue_C2 v) x (A.p i) x
    (mem_chart_source E x) (A.chart_η i his) hn

omit [T2Space M] in
theorem eventually_regular_realValue (u : A.realH A.highIndex)
    (hreg : ∀ x, A.realValue A.highIndex u x = 0 →
      fderiv ℝ (A.realValue A.highIndex u ∘ (chartAt E x).symm) ((chartAt E x) x) ≠ 0) :
    ∀ᶠ v in 𝓝 u, ∀ x, A.realValue A.highIndex v x = 0 →
      fderiv ℝ (A.realValue A.highIndex v ∘ (chartAt E x).symm) ((chartAt E x) x) ≠ 0 := by
  filter_upwards [Filter.eventually_all.mpr (fun i => A.eventually_localizedFirstJet_ne_zero i u hreg)] with v hv
  exact A.regular_of_localizedFirstJet v hv
end CompactMetricAtlas

end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Spectrum_SphericalSimpleEigenpairOpen
attribute [-instance] _root_.OAI.YauCounterexamples.circle_dimension_fact _root_.OAI.YauCounterexamples.threeChartedSpace _root_.OAI.YauCounterexamples.threeIsManifold _root_.OAI.YauCounterexamples.threeProductChartedSpace _root_.OAI.YauCounterexamples.threeProductIsManifold
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples


open Set Filter Function Manifold Bundle TopologicalSpace
open scoped Topology ContDiff BoundedContinuousFunction ENNReal NNReal
variable {P : Type*} [TopologicalSpace P]
lemma spherical_simple_eigenpair_open (q : P → SmoothMetric (Euclidean 3) (Sphere 3))
    (hq : ∀ r i j, ContinuousSmoothFamilyOn (fun a y => metricCoefficients (q a) r y i j)
      (chartAt (Euclidean 3) r).target) (a₀ : P)
    (lam : ℝ) (hlam : 0 < lam) (u : Sphere 3 → ℝ)
    (hu : ContMDiff 𝓘(ℝ,Euclidean 3) 𝓘(ℝ,ℝ) ∞ u) (hu0 : u ≠ 0)
    (hue : ∀ x, -laplaceBeltrami (q a₀) u x = lam*u x)
    (hsimple : ∀ v, ContMDiff 𝓘(ℝ,Euclidean 3) 𝓘(ℝ,ℝ) ∞ v →
      (∀ x, -laplaceBeltrami (q a₀) v x = lam*v x) → ∃ c : ℝ, v = fun x => c*u x)
    (hreg : ∀ x, u x=0 → fderiv ℝ (u ∘ (chartAt (Euclidean 3) x).symm)
      ((chartAt (Euclidean 3) x) x) ≠ 0)
    {J : Type*} [Fintype J] (Q : J → Set (Fin 3 → ℝ)) (d : J → ℝ)
    (ψ : (Fin 3 → ℝ) → Sphere 3) (hψ : Continuous ψ)
    (L : ℝ≥0∞) (hL : L < SignTests.signCertificate Q d (u ∘ ψ))
    {B D : ℝ} (hB : B < lam) (hD : lam < D) :
    ∀ᶠ a in 𝓝 a₀, ∃ e : ℝ, ∃ v : Sphere 3 → ℝ,
      B < e ∧ e < D ∧ ContMDiff 𝓘(ℝ,Euclidean 3) 𝓘(ℝ,ℝ) ∞ v ∧ v ≠ 0 ∧
      (∀ x, -laplaceBeltrami (q a) v x = e*v x) ∧
      (∀ x, v x=0 → fderiv ℝ (v ∘ (chartAt (Euclidean 3) x).symm)
        ((chartAt (Euclidean 3) x) x) ≠ 0) ∧
      L < SignTests.signCertificate Q d (v ∘ ψ) := by
  classical
  have hs : Module.finrank ℝ (Euclidean 3) < 2*(2*(2:ℝ)) := by norm_num [Euclidean]
  let A := (nonempty_compactMetricAtlas (q a₀) 2 hs).some
  let I := (nonempty_metricIntegralAtlas (E:=Euclidean 3) (M:=Sphere 3)).some
  let C : ∀ i, A.PatchCoefficients i := fun i => (A.nonempty_patchCoefficients i).some
  obtain ⟨α,hα1,hα⟩ := A.exists_parametrix_threshold C
  have hα0 : 0 < α := zero_lt_one.trans_le hα1
  obtain ⟨e,w,he,hw,hce,hcw,hpair⟩ := A.actual_simple_eigenpair_persistence I C α hα0
    (hα α le_rfl).1 (hα α le_rfl).2 lam (ne_of_gt (add_pos hα0 hlam))
    u hu hu0 hue hsimple q a₀ rfl (fun i => hq (A.p i))
  have hwr : ∀ᶠ a in 𝓝 a₀, ∀ x, A.realValue A.highIndex (w a) x=0 →
      fderiv ℝ (A.realValue A.highIndex (w a) ∘ (chartAt (Euclidean 3) x).symm)
        ((chartAt (Euclidean 3) x) x) ≠ 0 :=
    hcw.eventually (A.eventually_regular_realValue (w a₀) (by simpa only [hw] using hreg))
  let f (v : A.realH A.highIndex) : (Fin 3 → ℝ) → ℝ := A.realValue A.highIndex v ∘ ψ
  have hf : LowerSemicontinuous (fun v => SignTests.signCertificate Q d (f v)) := by
    apply SignTests.lowerSemicontinuous_signCertificate
    · intro v
      exact ((A.realRepresentative A.highIndex v).continuous.comp hψ).measurable
    · intro y
      exact (A.realRepresentative A.highIndex).continuous.eval_const (ψ y)
  have hwl : ∀ᶠ a in 𝓝 a₀, L < SignTests.signCertificate Q d (f (w a)) :=
    hcw.eventually (hf (w a₀) L (by simpa only [f,hw] using hL))
  have heb : ∀ᶠ a in 𝓝 a₀, B < e a := hce.eventually (lt_mem_nhds (he ▸ hB))
  have hed : ∀ᶠ a in 𝓝 a₀, e a < D := hce.eventually (gt_mem_nhds (he ▸ hD))
  filter_upwards [hpair,hwr,hwl,heb,hed] with a ha hr hl hb hd
  exact ⟨e a,A.realValue A.highIndex (w a),hb,hd,ha.1,ha.2.1,ha.2.2,hr,hl⟩

end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Estimates_SphericalPinFormNorm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples


section
open Set Filter Function Manifold Bundle TopologicalSpace BoxIntegral
open scoped Topology ContDiff Distributions ENNReal NNReal
lemma spherical_largeWitness_eventually_oai {P : Type*} [TopologicalSpace P]
    (q : P → SmoothMetric (Euclidean 3) (Sphere 3))
    (hq : ∀ r i j, ContinuousSmoothFamilyOn (fun a y => metricCoefficients (q a) r y i j)
      (chartAt (Euclidean 3) r).target) (a₀ : P) (k : ℕ) (hk : 3≤k)
    (e : ℝ) (he : 0<e) (u : Sphere 3 → ℝ)
    (hu : ContMDiff 𝓘(ℝ,Euclidean 3) 𝓘(ℝ,ℝ) ∞ u) (hu0 : u≠0)
    (hue : ∀ x, -laplaceBeltrami (q a₀) u x=e*u x)
    (hreg : SphericalRegular u) (hsimple : SphericalSimple (q a₀) u e)
    (A B : ℝ) (hB : B<e) (hD : e<2*(k:ℝ)^2) (hscore : SphericalSignAbove u (A*(k:ℝ))) :
    ∀ᶠ a in 𝓝 a₀, SphericalLargeWitness (q a) A B := by
  classical
  obtain ⟨partition,hpart,d,hd,hscore⟩ := hscore
  have hev := spherical_simple_eigenpair_open q hq a₀ e he u hu hu0 hue hsimple hreg
    (fun j : {J : Box (Fin 3) // J ∈ partition.boxes} => Box.Ioo j.val) d
    ((chartAt (Euclidean 3) sourcePole).symm ∘ normalWaveEquiv)
    ((sphere_chart_symm_continuous sourcePole).comp normalWaveEquiv.continuous)
    (ENNReal.ofReal (A*(k:ℝ))) hscore hB hD
  filter_upwards [hev] with a ha
  obtain ⟨e,v,heb,hed,hv,hv0,hve,hvr,hvl⟩ := ha
  exact ⟨k,hk,e,v,heb,hed,hv,hv0,hve,hvr,partition,hpart,d,hd,hvl⟩
end


open Set Filter Function Manifold Bundle TopologicalSpace BoxIntegral
open scoped Topology ContDiff Distributions ENNReal NNReal

end YauCounterexamples
end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.YauCounterexamples.spherical_largeWitness_eventually_oai.{u_1} := @OAI.YauCounterexamples.spherical_largeWitness_eventually_oai.{u_1}
