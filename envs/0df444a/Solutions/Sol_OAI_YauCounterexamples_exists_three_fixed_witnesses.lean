-- Prove2me | solution 1 for OAI.YauCounterexamples.exists_three_fixed_witnesses
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T13:42:47.467682+00:00
-- url     : https://prove2.me/submissions/ba0f09e4-4aed-4598-b32f-905c886878ec

import Mathlib
import Definitions.Def_SmoothYau
import Definitions.Def_OAIQ070A011
import Theorems.Thm_OAI_YauCounterexamples_CompactMetricAtlas_actual_simple_eigenpair_persistence
import Theorems.Thm_OAI_YauCounterexamples_exists_three_open_model
import Theorems.Thm_OAI_YauCounterexamples_exists_three_simple_stage
import Theorems.Thm_OAI_YauCounterexamples_fixed_metric_diagonal
import Theorems.Thm_OAI_YauCounterexamples_nonempty_compactMetricAtlas

section
-- module Solutions.OAIQ070_YAU.SmoothYau_DifferentialEq_HmoDualNorm
attribute [-instance] _root_.OAI.YauCounterexamples.circle_dimension_fact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
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
open Set Filter Metric
open scoped Topology InnerProductSpace
namespace YauCounterexamples
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
lemma positiveFormOn_iff_unit (P : Submodule ℝ E) (T : CoordinateForm E) :
    positiveFormOn P T ↔ ∀ v ∈ P, ‖v‖ = 1 → 0 < T v v := by
  constructor
  · intro h v hv hn
    exact h v hv (norm_ne_zero_iff.mp (by rw [hn]; norm_num))
  · intro h v hv hv0
    have hn : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv0
    let w := ‖v‖⁻¹ • v
    have hw : ‖w‖ = 1 := by simp [w, norm_smul, hn]
    have hp := h w (P.smul_mem _ hv) hw
    have he : ‖v‖ • w = v := by simp [w, smul_smul, hn]
    have heq : T v v = ‖v‖^2 * T w w := by
      conv_lhs => rw [← he]
      simp only [map_smul, smul_apply, smul_eq_mul]
      ring
    rw [heq]
    exact mul_pos (sq_pos_of_ne_zero hn) hp

attribute [local instance] OAI.YauCounterexamples.hmoDualNorm
attribute [local instance] OAI.YauCounterexamples.hmoDualSpace
local instance hmoFormNorm_rbf629e_1 : NormedAddCommGroup (CoordinateForm E) := inferInstance
local instance hmoFormSpace_rbf629e_1 : NormedSpace ℝ (CoordinateForm E) := inferInstance
local instance hmoDerivNorm_rbf629e_1 : NormedAddCommGroup (E →L[ℝ] CoordinateForm E) := inferInstance
local instance hmoDerivSpace_rbf629e_1 : NormedSpace ℝ (E →L[ℝ] CoordinateForm E) := inferInstance
theorem isOpen_positiveFormOn (P : Submodule ℝ E) :
    IsOpen {T : CoordinateForm E | positiveFormOn P T} := by
  let S : Set E := {v | v ∈ P ∧ ‖v‖ = 1}
  have hS : IsCompact S := by
    have he : S = (P : Set E) ∩ sphere (0 : E) 1 := by
      ext v
      simp only [S, mem_ofPred_eq, mem_inter_iff, mem_sphere_zero_iff_norm]
      rfl
    rw [he]
    exact (isCompact_sphere 0 1).inter_left P.closed_of_finiteDimensional
  let : CompactSpace S := isCompact_iff_compactSpace.mp hS
  let B : Set (CoordinateForm E × S) := {p | p.1 p.2 p.2 ≤ 0}
  have hT : Continuous (fun p : CoordinateForm E × S => p.1) := continuous_fst
  have hv : Continuous (fun p : CoordinateForm E × S => (p.2 : E)) :=
    continuous_subtype_val.comp continuous_snd
  have hB : IsClosed B := isClosed_le ((hT.clm_apply hv).clm_apply hv) continuous_const
  have hC : IsClosed (Prod.fst '' B) := isClosedMap_fst_of_compactSpace _ hB
  convert hC.isOpen_compl using 1
  all_goals try with_reducible_and_instances rfl
  ext T
  rw [mem_ofPred_eq, positiveFormOn_iff_unit]
  simp only [mem_compl_iff, mem_image, B, mem_ofPred_eq]
  constructor
  · intro h
    rintro ⟨q,hq,hqT⟩
    subst T
    exact (not_le_of_gt (h q.2 q.2.property.1 q.2.property.2)) hq
  · intro h v hv hn
    by_contra hh
    apply h
    exact ⟨(T,⟨v,hv,hn⟩),not_lt.mp hh,rfl⟩

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
-- module Solutions.OAIQ070_YAU.SmoothYau_Smoothness_ChartTensorCoordLocal1
attribute [-instance] _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_acg _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_mod _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_nacg _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_ns _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_snacg _root_.OAI.YauCounterexamples.MetricIntegralAtlas.volumeMeasure_finite _root_.OAI.YauCounterexamples.MetricIntegralAtlas.volumeMeasure_openPos _root_.OAI.YauCounterexamples.circle_dimension_fact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples
section
open Set Filter Function
open scoped Topology ContDiff
variable {P E F G : Type*} [TopologicalSpace P]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

namespace ContinuousSmoothFamilyOn
variable {f : P → E → F} {U : Set E}
lemma value (hf : ContinuousSmoothFamilyOn f U) :
    ContinuousOn (fun z : P × E => f z.1 z.2) (univ ×ˢ U) := by
  have hc := (continuousMultilinearCurryFin0 ℝ E F).continuous.continuousOn.comp
    (hf.jets 0) (mapsTo_univ _ _)
  simpa only [Function.comp_def,continuousMultilinearCurryFin0_apply,iteratedFDeriv_zero_apply] using hc

lemma postcomp (hf : ContinuousSmoothFamilyOn f U) (g : F → G)
    (hg : ∀ p x, x ∈ U → ContDiffAt ℝ ∞ g (f p x)) :
    ContinuousSmoothFamilyOn (fun p x => g (f p x)) U := by
  classical
  refine ⟨fun p x hx => (hg p x hx).comp x (hf.smooth p x hx),fun n z hz => ?_⟩
  have hq : ∀ k, ContinuousWithinAt (fun z : P × E => iteratedFDeriv ℝ k g (f z.1 z.2))
      (univ ×ˢ U) z := fun k =>
    ((hg z.1 z.2 hz.2).continuousAt_iteratedFDeriv (ENat.natCast_le_of_coe_top_le_withTop le_rfl k)).comp_continuousWithinAt (f := fun w : P × E => f w.1 w.2) (hf.value z hz)
  have hc : ContinuousWithinAt (fun z : P × E =>
      (ftaylorSeries ℝ g (f z.1 z.2)).taylorComp (ftaylorSeries ℝ (f z.1) z.2) n)
      (univ ×ˢ U) z := by
    apply tendsto_finsetSum
    intro c _
    change ContinuousWithinAt (fun z : P × E =>
      (c.compAlongOrderedFinpartitionL ℝ E F G (iteratedFDeriv ℝ c.length g (f z.1 z.2)))
        (fun j => iteratedFDeriv ℝ (c.partSize j) (f z.1) z.2)) _ z
    exact ((c.compAlongOrderedFinpartitionL ℝ E F G).continuous.continuousAt.comp_continuousWithinAt
      (hq c.length)).eval (continuousWithinAt_pi.mpr (fun j => hf.jets (c.partSize j) z hz))
  apply hc.congr_of_eventuallyEq _ ?_
  · filter_upwards [self_mem_nhdsWithin] with w hw
    exact iteratedFDeriv_comp (hg w.1 w.2 hw.2) (hf.smooth w.1 w.2 hw.2) (ENat.natCast_le_of_coe_top_le_withTop le_rfl n)
  · exact iteratedFDeriv_comp (hg z.1 z.2 hz.2) (hf.smooth z.1 z.2 hz.2) (ENat.natCast_le_of_coe_top_le_withTop le_rfl n)

lemma prodMk {g : P → E → G} (hf : ContinuousSmoothFamilyOn f U)
    (hg : ContinuousSmoothFamilyOn g U) :
    ContinuousSmoothFamilyOn (fun p x => (f p x,g p x)) U := by
  refine ⟨fun p x hx => (hf.smooth p x hx).prodMk (hg.smooth p x hx),fun n => ?_⟩
  have hc := (ContinuousMultilinearMap.prodL ℝ (fun _ : Fin n => E) F G).continuous.continuousOn.comp
    ((hf.jets n).prodMk (hg.jets n)) (mapsTo_univ _ _)
  apply hc.congr
  intro z hz
  exact iteratedFDeriv_prodMk (hf.smooth z.1 z.2 hz.2) (hg.smooth z.1 z.2 hz.2) (ENat.natCast_le_of_coe_top_le_withTop le_rfl n)

lemma const (g : E → F) (hg : ∀ x ∈ U, ContDiffAt ℝ ∞ g x) :
    ContinuousSmoothFamilyOn (fun _ : P => g) U := by
  refine ⟨fun _ => hg,fun n z hz => ?_⟩
  exact ((hg z.2 hz.2).continuousAt_iteratedFDeriv (ENat.natCast_le_of_coe_top_le_withTop le_rfl n)).comp_continuousWithinAt (f := Prod.snd)
    continuous_snd.continuousWithinAt

lemma scalar_const (a : P → F) (ha : Continuous a) :
    ContinuousSmoothFamilyOn (fun p (_ : E) => a p) U := by
  refine ⟨fun _ _ _ => contDiffAt_const,fun n => ?_⟩
  cases n with
  | zero =>
    simpa only [iteratedFDeriv_zero_eq_comp,Function.comp_def] using
      (continuousMultilinearCurryFin0 ℝ E F).symm.continuous.comp (ha.comp continuous_fst) |>.continuousOn
  | succ n => simp only [iteratedFDeriv_succ_const]; exact continuousOn_const

lemma add {g : P → E → F} (hf : ContinuousSmoothFamilyOn f U)
    (hg : ContinuousSmoothFamilyOn g U) : ContinuousSmoothFamilyOn (fun p x => f p x+g p x) U :=
  (hf.prodMk hg).postcomp (fun z : F × F => z.1+z.2) (fun _ _ _ => by fun_prop)

lemma mul {f g : P → E → ℝ} (hf : ContinuousSmoothFamilyOn f U)
    (hg : ContinuousSmoothFamilyOn g U) : ContinuousSmoothFamilyOn (fun p x => f p x*g p x) U :=
  (hf.prodMk hg).postcomp (fun z : ℝ × ℝ => z.1*z.2) (fun _ _ _ => by fun_prop)

end ContinuousSmoothFamilyOn
end


section
open Set Filter Function Metric TopologicalSpace
open scoped Topology ContDiff Distributions BoundedContinuousFunction
open Set Filter Function Metric TopologicalSpace
open scoped Topology ContDiff Distributions BoundedContinuousFunction
open Set Filter Function TopologicalSpace
open scoped Topology ContDiff Distributions BoundedContinuousFunction
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] (K : Compacts E)
lemma compactSmooth_continuousJets (n : ℕ) : Continuous
    (fun z : 𝓓_{K}(E,F) × E => iteratedFDeriv ℝ n z.1 z.2) := by
  have hc := ((ContDiffMapSupportedIn.structureMapCLM ℝ ⊤ n).continuous.comp
    (continuous_fst : Continuous (Prod.fst : 𝓓_{K}(E,F) × E → 𝓓_{K}(E,F)))).eval continuous_snd
  change Continuous (fun z : 𝓓_{K}(E,F) × E =>
    (ContDiffMapSupportedIn.structureMapCLM ℝ ⊤ n z.1) z.2) at hc
  simpa only [ContDiffMapSupportedIn.structureMapCLM_top_apply] using hc
lemma compactSmooth_family : ContinuousSmoothFamilyOn (fun f : 𝓓_{K}(E,F) => (f:E→F)) univ :=
  ⟨fun f _ _ => f.contDiff.contDiffAt,fun n => (compactSmooth_continuousJets K n).continuousOn⟩

end


section
open Set Filter Function Manifold
open scoped Topology ContDiff SchwartzMap
namespace ContinuousSmoothFamilyOn
variable {P E F : Type*} [TopologicalSpace P]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {U : Set E}
lemma sum {ι : Type*} (s : Finset ι) (f : ι → P → E → F)
    (hf : ∀ i ∈ s, ContinuousSmoothFamilyOn (f i) U) :
    ContinuousSmoothFamilyOn (fun p x => ∑ i ∈ s, f i p x) U := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using scalar_const (P:=P) (E:=E) (U:=U) (fun _ => (0 : F)) continuous_const
  | @insert i s hi ih =>
    simpa only [Finset.sum_insert hi] using (hf i (Finset.mem_insert_self i s)).add
      (ih (fun j hj => hf j (Finset.mem_insert_of_mem hj)))
lemma mono {f : P → E → F} (hf : ContinuousSmoothFamilyOn f U) {V : Set E} (hV : V ⊆ U) :
    ContinuousSmoothFamilyOn f V :=
  ⟨fun p x hx => hf.smooth p x (hV hx),fun n => (hf.jets n).mono (prod_mono_right hV)⟩
lemma of_local {f : P → E → F}
    (hf : ∀ x ∈ U, ∃ V : Set E, IsOpen V ∧ x ∈ V ∧ ContinuousSmoothFamilyOn f V) :
    ContinuousSmoothFamilyOn f U := by
  constructor
  · intro p x hx
    obtain ⟨V,hV,hxV,hfV⟩ := hf x hx
    exact hfV.smooth p x hxV
  · intro n z hz
    obtain ⟨V,hV,hzV,hfV⟩ := hf z.2 hz.2
    exact ((hfV.jets n (z) ⟨mem_univ _,hzV⟩).continuousAt
      ((isOpen_univ.prod hV).mem_nhds ⟨mem_univ _,hzV⟩)).continuousWithinAt
lemma congr {f g : P → E → F} (hU : IsOpen U) (hf : ContinuousSmoothFamilyOn f U)
    (he : ∀ p, EqOn (g p) (f p) U) : ContinuousSmoothFamilyOn g U := by
  have heq (p : P) (x : E) (hx : x ∈ U) : g p =ᶠ[𝓝 x] f p :=
    Filter.eventuallyEq_iff_exists_mem.mpr ⟨U,hU.mem_nhds hx,he p⟩
  refine ⟨fun p x hx => (hf.smooth p x hx).congr_of_eventuallyEq (heq p x hx),fun n => ?_⟩
  apply (hf.jets n).congr
  intro z hz
  exact ((heq z.1 z.2 hz.2).iteratedFDeriv (𝕜 := ℝ) n).eq_of_nhds
end ContinuousSmoothFamilyOn

end


section
open Set Filter Function Manifold Bundle TopologicalSpace
open scoped Topology ContDiff Distributions
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ,E) ∞ M] [T2Space M]

attribute [local instance] OAI.YauCounterexamples.instNormedAddCommGroupContinuousLinearMapRealId_solutions
attribute [local instance] OAI.YauCounterexamples.instNormedSpaceRealContinuousLinearMapId_solutions
attribute [local instance] OAI.YauCounterexamples.instNormedAddCommGroupMetricForm
attribute [local instance] OAI.YauCounterexamples.instNormedSpaceRealMetricForm
attribute [local instance] OAI.YauCounterexamples.instIsTopologicalAddGroupContinuousLinearMapRealIdTangentSpaceModelWithCornersSelf_solutions
local instance instContinuousSMulRealContinuousLinearMapIdTangentSpaceModelWithCornersSelf_solutions_rbf629e_1 (x : M) : ContinuousSMul ℝ (TangentSpace 𝓘(ℝ,E) x →L[ℝ] ℝ) := inferInstance
local instance instIsTopologicalAddGroupTangentForm_rbf629e_1 (x : M) : IsTopologicalAddGroup (TangentForm (E:=E) x) := inferInstance
local instance instContinuousSMulRealTangentForm_rbf629e_1 (x : M) : ContinuousSMul ℝ (TangentForm (E:=E) x) := inferInstance
omit [FiniteDimensional ℝ E] [T2Space M] in
lemma contDiffAt_chartTrivMetricForm (g : SmoothMetric E M) (p : M) {y : E}
    (hy : y ∈ (chartAt E p).target) : ContDiffAt ℝ ∞ (chartTrivMetricForm g p) y := by
  let : ∀ x : M, ContinuousAdd (TangentSpace 𝓘(ℝ,E) x →L[ℝ] ℝ) :=
    fun x => (tensorTangentDualAdd (E:=E) x).toContinuousAdd
  have hx : (chartAt E p).symm y ∈ (chartFormTrivialization (E:=E) p).baseSet := by
    rw [chartFormTrivialization_baseSet]
    exact (chartAt E p).map_target hy
  have hg := ((chartFormTrivialization (E:=E) p).contMDiffAt_section_iff hx).mp
    (g.contMDiff ((chartAt E p).symm y))
  exact contMDiffAt_iff_contDiffAt.mp (hg.comp y
    (contMDiffAt_symm_of_mem_maximalAtlas (IsManifold.chart_mem_maximalAtlas p) hy))

variable (g : SmoothMetric E M) (p : M) (K : Compacts E)

omit [T2Space M] in
lemma isOpen_chartTensorPositive (hK : (K : Set E) ⊆ (chartAt E p).target) :
    IsOpen {H : 𝓓_{K}(E,MetricForm E) | chartTensorPositive g p K H} := by
  rw [isOpen_iff_mem_nhds]
  intro H hH
  apply K.isCompact.eventually_forall_of_forall_eventually
  intro y hy
  have hEval : Continuous (fun z : 𝓓_{K}(E,MetricForm E) × E => z.1 z.2) := by
    simpa only [univ_prod_univ,continuousOn_univ] using (compactSmooth_family (F:=MetricForm E) K).value
  have h₁ : ContinuousAt (fun z : 𝓓_{K}(E,MetricForm E) × E => chartTrivMetricForm g p z.2) (H,y) :=
    ContinuousAt.comp (f := Prod.snd) (g := chartTrivMetricForm g p) (x := (H,y))
      (contDiffAt_chartTrivMetricForm g p (hK hy)).continuousAt continuous_snd.continuousAt
  have h₂ : Continuous (fun z : 𝓓_{K}(E,MetricForm E) × E => symmetrizeMetricForm (z.1 z.2)) :=
    (symmetrizeMetricForm (E:=E)).continuous.comp hEval
  have hc := h₁.add h₂.continuousAt
  exact hc.eventually ((isOpen_positiveFormOn (⊤ : Submodule ℝ E)).mem_nhds (hH y hy))

end


section
open Set Filter Function Manifold Bundle TopologicalSpace
open scoped Topology ContDiff Distributions
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ,E) ∞ M] [T2Space M]

variable (g₀ : SmoothMetric E M) (p : M) (K : Compacts E)
variable (ht : (chartAt E p).target = univ)

omit [FiniteDimensional ℝ E] [T2Space M] in
lemma smoothMetric_ext {g h : SmoothMetric E M}
    (he : ∀ x v w, g.inner x v w = h.inner x v w) : g=h := by
  have hi : g.inner=h.inner := funext (fun x => ContinuousLinearMap.ext (fun v =>
    ContinuousLinearMap.ext (fun w => he x v w)))
  cases g
  cases h
  cases hi
  rfl

attribute [local instance] OAI.YauCounterexamples.instNormedAddCommGroupContinuousLinearMapRealId_solutions_1
attribute [local instance] OAI.YauCounterexamples.instNormedSpaceRealContinuousLinearMapId_solutions_1
attribute [local instance] OAI.YauCounterexamples.instNormedAddCommGroupMetricForm_1
attribute [local instance] OAI.YauCounterexamples.instNormedSpaceRealMetricForm_1
lemma chartTensorMetric_ofMetric (g : SmoothMetric E M)
    (he : ∀ x, x ∉ (chartAt E p).symm '' (K : Set E) → g.inner x = g₀.inner x) :
    chartTensorMetric g₀ p K (ht ▸ subset_univ _) (chartTensorOfMetric g₀ p K ht g he)
      (chartTensorOfMetric_positive g₀ p K ht g he) = g := by
  apply smoothMetric_ext
  intro x v w
  by_cases hx : x ∈ (chartAt E p).source
  · change g₀.inner x v w + chartFormPush p (fun y =>
      symmetrizeMetricForm (chartTensorOfMetric g₀ p K ht g he y)) x v w = _
    rw [chartFormPush_pairing p hx]
    rw [chartTensorOfMetric_isSymm]
    change g₀.inner x v w + (chartMetricForm g p ((chartAt E p) x) -
      chartMetricForm g₀ p ((chartAt E p) x)) _ _ = _
    have hxy : (chartAt E p).symm ((chartAt E p) x) = x := (chartAt E p).left_inv hx
    have htxy := (chartAt E p).map_source hx
    rw [← chartFormTrivialization_metric g p htxy,← chartFormTrivialization_metric g₀ p htxy]
    rw [hxy]
    rw [sub_apply,sub_apply,chartFormTrivialization_pairing p hx,chartFormTrivialization_pairing p hx]
    have hx' : x ∈ (trivializationAt E (TangentSpace 𝓘(ℝ,E)) p).baseSet := by
      simpa only [TangentBundle.trivializationAt_baseSet] using hx
    simp only [Trivialization.symm_apply_apply_mk _ hx']
    ring
  · have hn : x ∉ (chartAt E p).symm '' (K : Set E) := by
      rintro ⟨y,hy,rfl⟩
      exact hx ((chartAt E p).map_target (ht ▸ mem_univ y))
    change g₀.inner x v w + chartFormPush p (fun y =>
      symmetrizeMetricForm (chartTensorOfMetric g₀ p K ht g he y)) x v w = _
    rw [chartFormPush_eq_zero_of_not_source p hx]
    simp only [zero_apply,add_zero,← he x hn]
end


open Set Filter Function Manifold Bundle TopologicalSpace
open scoped Topology ContDiff Distributions
section ChartTensorCoordinate
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ,E) ∞ M] [T2Space M]

attribute [local instance] OAI.YauCounterexamples.chartTensorCoordLocal1
attribute [local instance] OAI.YauCounterexamples.chartTensorCoordLocal2
attribute [local instance] OAI.YauCounterexamples.chartTensorCoordLocal3
attribute [local instance] OAI.YauCounterexamples.chartTensorCoordLocal4
local instance chartTensorCoordLocal5_rbf629e_1 (x : M) : IsTopologicalAddGroup (TangentSpace 𝓘(ℝ,E) x →L[ℝ] ℝ) := inferInstance
local instance chartTensorCoordLocal6_rbf629e_1 (x : M) : ContinuousSMul ℝ (TangentSpace 𝓘(ℝ,E) x →L[ℝ] ℝ) := inferInstance
local instance chartTensorCoordLocal7_rbf629e_1 (x : M) : IsTopologicalAddGroup (TangentForm (E:=E) x) := inferInstance
local instance chartTensorCoordLocal8_rbf629e_1 (x : M) : ContinuousSMul ℝ (TangentForm (E:=E) x) := inferInstance
lemma chartMetricForm_chartTensorMetric (g : SmoothMetric E M) (p : M) (K : Compacts E)
    (hK : (K : Set E) ⊆ (chartAt E p).target) (H : 𝓓_{K}(E,MetricForm E))
    (hH : chartTensorPositive g p K H) {y : E} (hy : y ∈ (chartAt E p).target) :
    chartMetricForm (chartTensorMetric g p K hK H hH) p y =
      chartMetricForm g p y + symmetrizeMetricForm (H y) := by
  rw [← chartFormTrivialization_metric _ p hy,← chartFormTrivialization_metric g p hy]
  ext v w
  rw [chartFormTrivialization_pairing p ((chartAt E p).map_target hy),add_apply,add_apply,
    chartFormTrivialization_pairing p ((chartAt E p).map_target hy)]
  change g.inner _ _ _ + chartFormPush p (fun y => symmetrizeMetricForm (H y)) _ _ _ = _
  congr 1
  rw [← chartFormTrivialization_pairing p ((chartAt E p).map_target hy),
    chartFormPush_trivialization p ((chartAt E p).map_target hy),(chartAt E p).right_inv hy]

lemma metricCoefficient_chartTensorMetric (g : SmoothMetric E M) (p : M) (K : Compacts E)
    (hK : (K : Set E) ⊆ (chartAt E p).target) (H : 𝓓_{K}(E,MetricForm E))
    (hH : chartTensorPositive g p K H) {y : E} (hy : y ∈ (chartAt E p).target)
    (i j : CoordIndex E) :
    metricCoefficients (chartTensorMetric g p K hK H hH) p y i j =
      metricCoefficients g p y i j + symmetrizeMetricForm (H y)
        (Module.finBasis ℝ E i) (Module.finBasis ℝ E j) := by
  have h := congrArg (fun B : MetricForm E => B (Module.finBasis ℝ E i) (Module.finBasis ℝ E j))
    (chartMetricForm_chartTensorMetric g p K hK H hH hy)
  simpa only [add_apply,chartMetricForm_pairing,metricCoefficients,coordinateVector] using h

variable {P : Type*} [TopologicalSpace P]
lemma family_chartTensorMetric_main (g : SmoothMetric E M) (p : M) (K : Compacts E)
    (hK : (K : Set E) ⊆ (chartAt E p).target) (H : P → 𝓓_{K}(E,MetricForm E))
    (hH : ∀ a, chartTensorPositive g p K (H a)) (hc : Continuous H) (i j : CoordIndex E) :
    ContinuousSmoothFamilyOn
      (fun a y => metricCoefficients (chartTensorMetric g p K hK (H a) (hH a)) p y i j)
      (chartAt E p).target := by
  have hfamily := compactSmooth_family (F:=MetricForm E) K
  have hparam : ContinuousSmoothFamilyOn (fun a => (H a : E → MetricForm E)) univ := by
    refine ⟨fun a => hfamily.smooth (H a),fun degree => ?_⟩
    exact (hfamily.jets degree).comp ((hc.comp continuous_fst).prodMk continuous_snd).continuousOn
      (fun pair hpair => ⟨mem_univ _,hpair.2⟩)
  have hf := hparam.postcomp
    (fun B : MetricForm E => symmetrizeMetricForm B (Module.finBasis ℝ E i) (Module.finBasis ℝ E j))
    (fun _ _ _ => by fun_prop)
  have hb := ContinuousSmoothFamilyOn.const (P:=P) (fun y => metricCoefficients g p y i j)
    (fun y hy => (contDiffOn_metricCoefficient g p i j).contDiffAt ((chartAt E p).open_target.mem_nhds hy))
  apply (hb.add (hf.mono (subset_univ _))).congr (chartAt E p).open_target
  intro a y hy
  exact metricCoefficient_chartTensorMetric g p K hK (H a) (hH a) hy i j
end ChartTensorCoordinate

variable {P E M : Type*} [TopologicalSpace P]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M] [T2Space M]

local instance chartTensorCoordLocal13 (x : M) : IsTopologicalAddGroup (TangentSpace 𝓘(ℝ,E) x →L[ℝ] ℝ) := inferInstance

omit [T2Space M] in
lemma continuousSmoothFamily_from_chart (q : P → SmoothMetric E M) (g : SmoothMetric E M)
    (p : M) (S : Set M) (hS : IsClosed S) (hSp : S ⊆ (chartAt E p).source)
    (hq : ∀ i j, ContinuousSmoothFamilyOn (fun a y => metricCoefficients (q a) p y i j) (chartAt E p).target)
    (he : ∀ a x, x ∉ S → (q a).inner x = g.inner x) (r : M) (i j : CoordIndex E) :
    ContinuousSmoothFamilyOn (fun a y => metricCoefficients (q a) r y i j) (chartAt E r).target := by
  classical
  apply ContinuousSmoothFamilyOn.of_local
  intro y hy
  by_cases hp : (chartAt E r).symm y ∈ (chartAt E p).source
  · obtain ⟨V,hV,hVo,hyV⟩ := mem_nhds_iff.mp (chart_overlap_nhds p r hy hp)
    have ht : ∀ z ∈ V, ContDiffAt ℝ ∞ (chartTransition p r) z :=
      fun z hz => contDiffAt_chartTransition p r (hV hz).1 (hV hz).2
    have hf (k l : CoordIndex E) : ContinuousSmoothFamilyOn
        (fun a z => metricCoefficients (q a) p (chartTransition p r z) k l) V := by
      have hmap : MapsTo (chartTransition p r) V (chartAt E p).target :=
        fun point hpoint => (chartAt E p).map_source (hV hpoint).2
      refine ⟨fun param point hpoint =>
        ((hq k l).smooth param _ (hmap hpoint)).comp point (ht point hpoint),
        fun degree pair hpair => ?_⟩
      have htransition : ContinuousOn (chartTransition p r) V :=
        fun point hpoint => (ht point hpoint).continuousAt.continuousWithinAt
      have hcomp : ContinuousOn (fun pair : P × E => (pair.1,chartTransition p r pair.2))
          (univ ×ˢ V) := continuousOn_fst.prodMk
        (htransition.comp continuousOn_snd (fun point hpoint => hpoint.2))
      have houter (order : ℕ) : ContinuousWithinAt
          (fun pair : P × E => iteratedFDeriv ℝ order
            (fun point => metricCoefficients (q pair.1) p point k l) (chartTransition p r pair.2))
          (univ ×ˢ V) pair :=
        (((hq k l).jets order).comp hcomp
          (fun point hpoint => ⟨mem_univ _,hmap hpoint.2⟩)) pair hpair
      have hinner (order : ℕ) : ContinuousWithinAt
          (fun pair : P × E => iteratedFDeriv ℝ order (chartTransition p r) pair.2)
          (univ ×ˢ V) pair :=
        ((ht pair.2 hpair.2).continuousAt_iteratedFDeriv
          (ENat.natCast_le_of_coe_top_le_withTop le_rfl order)).comp_continuousWithinAt
          continuous_snd.continuousWithinAt
      have hjet : ContinuousWithinAt (fun pair : P × E =>
          (ftaylorSeries ℝ (fun point => metricCoefficients (q pair.1) p point k l)
            (chartTransition p r pair.2)).taylorComp (ftaylorSeries ℝ (chartTransition p r) pair.2)
            degree) (univ ×ˢ V) pair := by
        apply tendsto_finsetSum
        intro partition _
        change ContinuousWithinAt (fun pair : P × E =>
          (partition.compAlongOrderedFinpartitionL ℝ E E ℝ
            (iteratedFDeriv ℝ partition.length
              (fun point => metricCoefficients (q pair.1) p point k l) (chartTransition p r pair.2)))
            (fun index => iteratedFDeriv ℝ (partition.partSize index) (chartTransition p r) pair.2)) _ pair
        exact ((partition.compAlongOrderedFinpartitionL ℝ E E ℝ).continuous.continuousAt.comp_continuousWithinAt
          (houter partition.length)).eval
            (continuousWithinAt_pi.mpr (fun index => hinner (partition.partSize index)))
      apply hjet.congr_of_eventuallyEq _ ?_
      · filter_upwards [self_mem_nhdsWithin] with point hpoint
        exact iteratedFDeriv_comp ((hq k l).smooth point.1 _ (hmap hpoint.2)) (ht point.2 hpoint.2)
          (ENat.natCast_le_of_coe_top_le_withTop le_rfl degree)
      · exact iteratedFDeriv_comp ((hq k l).smooth pair.1 _ (hmap hpair.2)) (ht pair.2 hpair.2)
          (ENat.natCast_le_of_coe_top_le_withTop le_rfl degree)
    have hT (k l : CoordIndex E) : ContinuousSmoothFamilyOn
        (fun _ : P => fun z => coordinateTransitionMatrix p r z k l) V := by
      apply ContinuousSmoothFamilyOn.const
      intro z hz
      simp only [coordinateTransitionMatrix,LinearMap.toMatrix_apply]
      change ContDiffAt ℝ ∞ (fun z => (Module.finBasis ℝ E).repr
        ((fderiv ℝ (chartTransition p r) z) (Module.finBasis ℝ E l)) k) z
      exact ((Module.finBasis ℝ E).coord k).toContinuousLinearMap.contDiff.contDiffAt.comp z
        (((ht z hz).fderiv_right (by simp)).clm_apply contDiffAt_const)
    have htensor := ContinuousSmoothFamilyOn.sum Finset.univ (fun l => fun a z =>
        (∑ k, coordinateTransitionMatrix p r z k i *
          metricCoefficients (q a) p (chartTransition p r z) k l) * coordinateTransitionMatrix p r z l j)
      (fun l _ => (ContinuousSmoothFamilyOn.sum Finset.univ _
        (fun k _ => (hT k i).mul (hf k l))).mul (hT l j))
    refine ⟨V,hVo,hyV,htensor.congr hVo ?_⟩
    intro a z hz
    exact congrArg (fun A : Matrix (CoordIndex E) (CoordIndex E) ℝ => A i j)
      (metricCoefficients_change (q a) p r (hV hz).1 (hV hz).2)
  · have hn : (chartAt E r).symm y ∉ S := fun hn => hp (hSp hn)
    have hn' := ((chartAt E r).continuousAt_symm hy).eventually (hS.isOpen_compl.mem_nhds hn)
    obtain ⟨V,hV,hVo,hyV⟩ := mem_nhds_iff.mp (inter_mem ((chartAt E r).open_target.mem_nhds hy) hn')
    refine ⟨V,hVo,hyV,?_⟩
    have hf := ContinuousSmoothFamilyOn.const (P:=P) (fun z => metricCoefficients g r z i j)
      (U:=V) (fun z hz => (contDiffOn_metricCoefficient g r i j).contDiffAt
        ((chartAt E r).open_target.mem_nhds (hV hz).1))
    apply hf.congr hVo
    intro a z hz
    exact congrArg (fun B => B (coordinateVector r z i) (coordinateVector r z j))
      (he a ((chartAt E r).symm z) (hV hz).2)
attribute [local instance] OAI.YauCounterexamples.chartTensorCoordLocal9
attribute [local instance] OAI.YauCounterexamples.chartTensorCoordLocal10
attribute [local instance] OAI.YauCounterexamples.chartTensorCoordLocal11
attribute [local instance] OAI.YauCounterexamples.chartTensorCoordLocal12
local instance chartTensorCoordLocal14_rbf629e_1 (x : M) : ContinuousSMul ℝ (TangentSpace 𝓘(ℝ,E) x →L[ℝ] ℝ) := inferInstance
local instance chartTensorCoordLocal15_rbf629e_1 (x : M) : IsTopologicalAddGroup (TangentForm (E:=E) x) := inferInstance
local instance chartTensorCoordLocal16_rbf629e_1 (x : M) : ContinuousSMul ℝ (TangentForm (E:=E) x) := inferInstance
lemma family_chartTensorMetric (g : SmoothMetric E M) (p : M) (K : Compacts E)
    (hK : (K : Set E) ⊆ (chartAt E p).target) (H : P → 𝓓_{K}(E,MetricForm E))
    (hH : ∀ a, chartTensorPositive g p K (H a)) (hc : Continuous H)
    (r : M) (i j : CoordIndex E) :
    ContinuousSmoothFamilyOn
      (fun a y => metricCoefficients (chartTensorMetric g p K hK (H a) (hH a)) r y i j)
      (chartAt E r).target := by
  apply continuousSmoothFamily_from_chart _ g p ((chartAt E p).symm '' (K : Set E))
  · exact (K.isCompact.image_of_continuousOn ((chartAt E p).continuousOn_symm.mono hK)).isClosed
  · rintro x ⟨y,hy,rfl⟩
    exact (chartAt E p).map_target (hK hy)
  · exact family_chartTensorMetric_main g p K hK H hH hc
  · intro a x hx
    change g.inner x + chartFormPush p (fun y => symmetrizeMetricForm (H a y)) x = g.inner x
    suffices hh : chartFormPush p (fun y => symmetrizeMetricForm (H a y)) x = 0 by
      rw [hh]
      ext v w
      change g.inner x v w + (0 : ℝ) = g.inner x v w
      exact add_zero _
    by_cases hxp : x ∈ (chartAt E p).source
    · apply chartFormPush_zero
      have hy : (chartAt E p) x ∉ (K : Set E) := by
        intro hy
        exact hx ⟨(chartAt E p) x,hy,(chartAt E p).left_inv hxp⟩
      simp [manifoldChartPush,hxp,(H a).zero_on_compl hy]
    · exact chartFormPush_eq_zero_of_not_source p hxp

end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Smoothness_CompactSmoothJetMap
attribute [-instance] _root_.OAI.YauCounterexamples.circle_dimension_fact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples
section
open Set Filter Function Metric TopologicalSpace
open scoped Topology ContDiff Distributions BoundedContinuousFunction
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem smooth_of_uniform_jets (u : ℕ → E → F) (hu : ∀ j, ContDiff ℝ ∞ (u j))
    (G : (m : ℕ) → E →ᵇ (E [×m]→L[ℝ] F))
    (hG : ∀ m, TendstoUniformly (fun j => iteratedFDeriv ℝ m (u j)) (G m) atTop) :
    ∃ f : E → F, ContDiff ℝ ∞ f ∧
      ∀ m, iteratedFDeriv ℝ m f = G m := by
  let f : E → F := fun x => (G 0 x).curry0
  let p : E → FormalMultilinearSeries ℝ E F := fun x m => G m x
  have hp : HasFTaylorSeriesUpTo ∞ f p := by
    refine ⟨fun _ => rfl, ?_, fun m _ => (G m).continuous⟩
    intro m hm x
    have ht : TendstoUniformly
      (fun j y => (iteratedFDeriv ℝ (m+1) (u j) y).curryLeft)
      (fun y => (G (m+1) y).curryLeft) atTop := by
      exact (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (m+1) => E) F).isometry.uniformContinuous
        |>.comp_tendstoUniformly (hG (m+1))
    exact hasFDerivAt_of_tendstoUniformly ht
      (fun j y => (hu j).ftaylorSeries.fderiv m hm y)
      (fun y => (hG m).tendsto_at y) x
  refine ⟨f,hp.contDiff,fun m => ?_⟩
  funext x
  exact (hp.eq_iteratedFDeriv (m:=m) (ENat.natCast_le_of_coe_top_le_withTop le_rfl m) x).symm


end

open Set Filter Function Metric TopologicalSpace
open scoped Topology ContDiff Distributions BoundedContinuousFunction
open Set Filter Function Metric TopologicalSpace
open scoped Topology ContDiff Distributions BoundedContinuousFunction
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] (K : Compacts E)

theorem compactSmoothJetMap_isClosed : IsClosed (range (compactSmoothJetMap (F:=F) K)) := by
  let : ∀ m : ℕ, FirstCountableTopology (E →ᵇ (E [×m]→L[ℝ] F)) := fun _ => inferInstance
  let : FirstCountableTopology ((m : ℕ) → E →ᵇ (E [×m]→L[ℝ] F)) := inferInstance
  apply IsSeqClosed.isClosed
  intro v G hv hlim
  choose u hu using hv
  have hG : ∀ m, TendstoUniformly (fun j => iteratedFDeriv ℝ m (u j)) (G m) atTop := by
    intro m
    have ht := (continuous_apply m).tendsto G |>.comp hlim
    have htu : Tendsto (fun j => ContDiffMapSupportedIn.structureMapCLM ℝ ⊤ m (u j))
        atTop (𝓝 (G m)) := by
      convert ht using 1
      all_goals try with_reducible_and_instances rfl
      funext j
      exact congrArg (fun w => w m) (hu j)
    simpa only [ContDiffMapSupportedIn.structureMapCLM_top_apply] using
      BoundedContinuousFunction.tendsto_iff_tendstoUniformly.mp htu
  obtain ⟨f,hf,hfj⟩ := smooth_of_uniform_jets (fun j => u j) (fun j => (u j).contDiff) G hG
  have hzero : EqOn f 0 Kᶜ := by
    intro x hx
    have hconst : ∀ j, iteratedFDeriv ℝ 0 (u j) x = 0 := by
      intro j
      ext z
      simp only [iteratedFDeriv_zero_apply]
      exact (u j).zero_on_compl hx
    have hGX : G 0 x = 0 := tendsto_nhds_unique ((hG 0).tendsto_at x)
      (by simpa only [hconst] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : E [×0]→L[ℝ] F)) atTop (𝓝 0)))
    have hh := congrArg (fun h : E → E [×0]→L[ℝ] F => h x) (hfj 0)
    rw [hGX] at hh
    have he := congrArg (fun p : E [×0]→L[ℝ] F => p (fun _ => 0)) hh
    simpa using he
  refine ⟨⟨f,hf,hzero⟩,?_⟩
  funext m
  apply BoundedContinuousFunction.ext
  intro x
  rw [compactSmoothJetMap, ContinuousLinearMap.pi_apply,
    ContDiffMapSupportedIn.structureMapCLM_top_apply]
  exact congrArg (fun h : E → E [×m]→L[ℝ] F => h x) (hfj m)

variable [CompleteSpace F]

theorem compactSmooth_complete : CompleteSpace 𝓓_{K}(E,F) := by
  apply (ContDiffMapSupportedIn.isUniformEmbedding_pi_structureMapCLM (𝕜:=ℝ)
    (n:=⊤) (K:=K)).isUniformInducing.completeSpace
  exact (compactSmoothJetMap_isClosed (F:=F) K).isComplete



end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_SphereMetric_FourThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples


section
open Set Filter Function Manifold Bundle TopologicalSpace
open scoped Topology ContDiff BoundedContinuousFunction ENNReal NNReal
variable {P : Type*} [TopologicalSpace P]
lemma three_simple_eigenpair_open (q : P → SmoothMetric ThreeModel ThreeManifold)
    (hq : ∀ r i j, ContinuousSmoothFamilyOn (fun a y => metricCoefficients (q a) r y i j)
      (chartAt ThreeModel r).target) (a₀ : P)
    (lam : ℝ) (hlam : 0 < lam) (u : ThreeManifold → ℝ)
    (hu : ContMDiff 𝓘(ℝ,ThreeModel) 𝓘(ℝ,ℝ) ∞ u) (hu0 : u ≠ 0)
    (hue : ∀ x, -laplaceBeltrami (q a₀) u x = lam*u x)
    (hsimple : ∀ v, ContMDiff 𝓘(ℝ,ThreeModel) 𝓘(ℝ,ℝ) ∞ v →
      (∀ x, -laplaceBeltrami (q a₀) v x = lam*v x) → ∃ c : ℝ, v = fun x => c*u x)
    (hreg : ∀ x, u x=0 → fderiv ℝ (u ∘ (chartAt ThreeModel x).symm)
      ((chartAt ThreeModel x) x) ≠ 0)
    {J : Type*} [Fintype J] (Q : J → Set (Fin 3 → ℝ)) (d : J → ℝ)
    (ψ : (Fin 3 → ℝ) → ThreeManifold) (hψ : Continuous ψ)
    (L : ℝ≥0∞) (hL : L < SignTests.signCertificate Q d (u ∘ ψ))
    {B D : ℝ} (hB : B < lam) (hD : lam < D) :
    ∀ᶠ a in 𝓝 a₀, ∃ e : ℝ, ∃ v : ThreeManifold → ℝ,
      B < e ∧ e < D ∧ ContMDiff 𝓘(ℝ,ThreeModel) 𝓘(ℝ,ℝ) ∞ v ∧ v ≠ 0 ∧
      (∀ x, -laplaceBeltrami (q a) v x = e*v x) ∧
      (∀ x, v x=0 → fderiv ℝ (v ∘ (chartAt ThreeModel x).symm)
        ((chartAt ThreeModel x) x) ≠ 0) ∧
      L < SignTests.signCertificate Q d (v ∘ ψ) := by
  classical
  have hs : Module.finrank ℝ ThreeModel < 2*(2*(2:ℝ)) := by norm_num [threeModel_finrank]
  let A := (nonempty_compactMetricAtlas (q a₀) 2 hs).some
  let I := (nonempty_metricIntegralAtlas (E:=ThreeModel) (M:=ThreeManifold)).some
  let C : ∀ i, A.PatchCoefficients i := fun i => (A.nonempty_patchCoefficients i).some
  obtain ⟨α,hα1,hα⟩ := A.exists_parametrix_threshold C
  have hα0 : 0 < α := zero_lt_one.trans_le hα1
  obtain ⟨e,w,he,hw,hce,hcw,hpair⟩ := A.actual_simple_eigenpair_persistence I C α hα0
    (hα α le_rfl).1 (hα α le_rfl).2 lam (ne_of_gt (add_pos hα0 hlam))
    u hu hu0 hue hsimple q a₀ rfl (fun i => hq (A.p i))
  have hwr : ∀ᶠ a in 𝓝 a₀, ∀ x, A.realValue A.highIndex (w a) x=0 →
      fderiv ℝ (A.realValue A.highIndex (w a) ∘ (chartAt ThreeModel x).symm)
        ((chartAt ThreeModel x) x) ≠ 0 :=
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
end


open Set Filter Manifold Bundle Function
open scoped Topology ContDiff

end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_SphereMetric_ExistsThreeScalarProducer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples
section
open Set Filter Function Manifold Metric
open scoped Topology ContDiff
lemma threeNormalInv_continuous : Continuous threeNormalInv :=
  (continuousOn_univ.mp (by simpa only [three_chart_target] using (chartAt ThreeModel threeProfileCenter).continuousOn_symm)).comp threeNormalEquiv.continuous
end


open Set Filter Manifold Metric MeasureTheory BoxIntegral
open scoped Topology ContDiff ENNReal


end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_SphereMetric_ThreeFixedFormNorm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples


section
open Set Filter Function Manifold Bundle TopologicalSpace BoxIntegral Metric
open scoped Topology ContDiff Distributions
attribute [local instance] OAI.YauCounterexamples.threeAmbientFormNorm
attribute [local instance] OAI.YauCounterexamples.threeAmbientFormSpace
lemma threePositiveSet_isOpen (R : ℝ) : IsOpen (threePositiveSet R) :=
  isOpen_chartTensorPositive threeBackgroundMetric threeProfileCenter (threeTensorSupport R)
    ((three_chart_target threeProfileCenter).symm ▸ subset_univ _)
lemma threeTensorMetric_of (R : ℝ) (g : SmoothMetric ThreeModel ThreeManifold)
    (he : ThreeExterior g (R/2)) :
    threeTensorMetric R ⟨threeTensorOf R g he,threeTensorOf_positive R g he⟩=g :=
  chartTensorMetric_ofMetric threeBackgroundMetric threeProfileCenter (threeTensorSupport R)
    (three_chart_target threeProfileCenter) g (threeExterior_support le_rfl he)
lemma threeTensorMetric_family (R : ℝ) (r : ThreeManifold) (i j : CoordIndex ThreeModel) :
    ContinuousSmoothFamilyOn (fun H y => metricCoefficients (threeTensorMetric R H) r y i j)
      (chartAt ThreeModel r).target :=
  family_chartTensorMetric threeBackgroundMetric threeProfileCenter (threeTensorSupport R)
    ((three_chart_target threeProfileCenter).symm ▸ subset_univ _) Subtype.val
    (fun H => H.property) continuous_subtype_val r i j
end


section
open Set Filter Function Manifold Bundle TopologicalSpace BoxIntegral
open scoped Topology ContDiff Distributions ENNReal NNReal
lemma three_largeWitness_eventually (R : ℝ) {P : Type*} [TopologicalSpace P]
    (q : P → SmoothMetric ThreeModel ThreeManifold)
    (hq : ∀ r i j, ContinuousSmoothFamilyOn (fun a y => metricCoefficients (q a) r y i j)
      (chartAt ThreeModel r).target) (a₀ : P) (k : ℕ) (hk : 3 ≤ k)
    (e : ℝ) (he : 0<e) (u : ThreeManifold → ℝ)
    (hu : ContMDiff 𝓘(ℝ,ThreeModel) 𝓘(ℝ,ℝ) ∞ u) (hu0 : u≠0)
    (hue : ∀ x, -laplaceBeltrami (q a₀) u x=e*u x)
    (hreg : ThreeRegular u) (hsimple : ThreeSimple (q a₀) u e)
    (A B : ℝ) (hB : B<e) (hD : e<4*(k:ℝ)^2) (hscore : ThreeSignAbove R u (A*(k:ℝ))) :
    ∀ᶠ a in 𝓝 a₀, ThreeLargeWitness R (q a) A B := by
  classical
  obtain ⟨I,hI,partition,hpart,d,hd,hscore⟩ := hscore
  have hev := three_simple_eigenpair_open q hq a₀ e he u hu hu0 hue hsimple hreg
    (fun j : {J : Box (Fin 3) // J ∈ partition.boxes} => Box.Ioo j.val) d
    (threeNormalInv ∘ normalWaveEquiv)
    (threeNormalInv_continuous.comp normalWaveEquiv.continuous)
    (ENNReal.ofReal (A*(k:ℝ))) hscore hB hD
  filter_upwards [hev] with a ha
  obtain ⟨e,v,heb,hed,hv,hv0,hve,hvr,hvl⟩ := ha
  exact ⟨k,hk,e,v,heb,hed,hv,hv0,hve,hvr,I,hI,partition,hpart,d,hd,hvl⟩
end


open Set Filter Function Manifold Bundle TopologicalSpace BoxIntegral
open scoped Topology ContDiff Distributions ENNReal NNReal
local instance threeFixedContinuousSMul : ContinuousSMul ℝ ThreeModel := IsBoundedSMul.continuousSMul
local instance threeFixedFormSpace_rbf629e_1 : NormedSpace ℝ (MetricForm ThreeModel) := inferInstanceAs (NormedSpace ℝ (ThreeModel →L[ℝ] ThreeModel →L[ℝ] ℝ))
local instance threeFixedFormComplete : CompleteSpace (MetricForm ThreeModel) := by
  let : CompleteSpace (ThreeModel →L[ℝ] ℝ) := ContinuousLinearMap.instCompleteSpace
  exact ContinuousLinearMap.instCompleteSpace

local instance threeFixedFormNorm_rbf629e_1 : NormedAddCommGroup (MetricForm ThreeModel) := inferInstanceAs (NormedAddCommGroup (ThreeModel →L[ℝ] ThreeModel →L[ℝ] ℝ))
theorem exists_three_fixed_witnesses_oai :
    ∃ R : ℝ, 0<R ∧ ∃ g : SmoothMetric ThreeModel ThreeManifold,
      ∀ n : ℕ, ThreeLargeWitness R g ((n:ℝ)+1) ((n:ℝ)+1) := by
  classical
  obtain ⟨R,hR,N,hN,h0N,hstage⟩ := exists_three_simple_stage
  let : MetricSpace (ThreeTensor R) := compactSmoothMetricSpace (threeTensorSupport R)
  let : CompleteSpace (ThreeTensor R) := compactSmooth_complete (threeTensorSupport R)
  obtain ⟨O,hO,h0O,hON⟩ := exists_three_open_model R N hN
  let P : ℕ → Set (ThreeTensor R) := fun _ =>
    {H | ∃ g : SmoothMetric ThreeModel ThreeManifold, ∃ r : ℝ, 0 < r ∧ ∃ hrR : r<R/2,
      ∃ he : ThreeExterior g r, H=threeTensorOf R g (he.mono hrR.le) ∧ H∈O}
  let W : ℕ → Set (ThreeTensor R) := fun n =>
    {H | ∃ hp : H∈threePositiveSet R,
      ThreeLargeWitness R (threeTensorMetric R ⟨H,hp⟩) ((n:ℝ)+1) ((n:ℝ)+1)}
  have hstep : ∀ n, ∀ H∈P n, ∀ U : Set (ThreeTensor R), IsOpen U → H∈U →
      ∃ K∈P (n+1), K∈U ∧ ∃ V : Set (ThreeTensor R), IsOpen V ∧ K∈V ∧ V⊆W n := by
    intro n H hH U hU hHU
    obtain ⟨g,r,hr,hrR,he,rfl,hgO⟩ := hH
    let e := he.mono hrR.le
    obtain ⟨hp,hgN⟩ := hON _ hgO
    have hmetric : threeTensorMetric R ⟨threeTensorOf R g e,hp⟩=g := threeTensorMetric_of R g e
    rw [hmetric] at hgN
    obtain ⟨k,hkM,hk3,h,c,hc,hcR,eh,hhU,u,hu,hu0,hue,hreg,hsimple,hscore⟩ :=
      hstage g hgN r hr hrR he ((n:ℝ)+1) (by positivity) (n+3)
        (U∩O) (hU.inter hO) ⟨hHU,hgO⟩
    let eh' := eh.mono hcR.le
    let K := threeTensorOf R h eh'
    let z : ThreePositiveTensor R := ⟨K,threeTensorOf_positive R h eh'⟩
    have hqz : threeTensorMetric R z=h := threeTensorMetric_of R h eh'
    have hkpos : (0:ℝ)<k := by exact_mod_cast (show 0<k by omega)
    have hkreal : (n:ℝ)+3 ≤ k := by exact_mod_cast hkM
    have hk3real : (3:ℝ) ≤ k := by exact_mod_cast hk3
    have hepos : 0<productFrequency k := by dsimp [productFrequency]; positivity
    have heB : (n:ℝ)+1<productFrequency k := by dsimp [productFrequency]; nlinarith
    have heD : productFrequency k<4*(k:ℝ)^2 := by dsimp [productFrequency]; nlinarith
    have hev := three_largeWitness_eventually R (threeTensorMetric R)
      (threeTensorMetric_family R) z k hk3 (productFrequency k) hepos u hu hu0
      (by simpa only [hqz] using hue) hreg (by simpa only [hqz] using hsimple)
      ((n:ℝ)+1) ((n:ℝ)+1) heB heD hscore
    obtain ⟨V,hV,hVo,hzV⟩ := mem_nhds_iff.mp hev
    refine ⟨K,⟨h,c,hc,hcR,eh,rfl,hhU.2⟩,hhU.1,Subtype.val '' V,
      (threePositiveSet_isOpen R).isOpenMap_subtype_val V hVo,⟨z,hzV,rfl⟩,?_⟩
    rintro H ⟨v,hv,rfl⟩
    exact ⟨v.property,hV hv⟩
  have hzP : (0:ThreeTensor R)∈P 0 := by
    refine ⟨threeBackgroundMetric,R/4,by positivity,by linarith,(fun _ _ => rfl),?_,h0O⟩
    exact (threeTensorOf_zero R).symm
  obtain ⟨H,hHO,hHW⟩ := fixed_metric_diagonal P W hstep 0 hzP hO h0O
  obtain ⟨hp,hgN⟩ := hON H hHO
  refine ⟨R,hR,threeTensorMetric R ⟨H,hp⟩,?_⟩
  intro n
  exact (hHW n).choose_spec

end YauCounterexamples
end

end OAI
end

theorem solution : type_of% @OAI.YauCounterexamples.exists_three_fixed_witnesses_oai := @OAI.YauCounterexamples.exists_three_fixed_witnesses_oai
