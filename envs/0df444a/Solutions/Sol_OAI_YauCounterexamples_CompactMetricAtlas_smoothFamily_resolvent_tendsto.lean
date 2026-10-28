-- Prove2me | solution 1 for OAI.YauCounterexamples.CompactMetricAtlas.smoothFamily_resolvent_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T12:57:18.630757+00:00
-- url     : https://prove2.me/submissions/9c19d199-a133-4347-855b-9f5b08cdf5af

import Mathlib
import Definitions.Def_SmoothYau
import Definitions.Def_OAIQ070A009

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Smoothness_ContDiffPartialIteratedFDeriv
attribute [-instance] _root_.OAI.YauCounterexamples.circle_dimension_fact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open FourierTransform TemperedDistribution MeasureTheory
open scoped SchwartzMap ENNReal Real Laplacian BoundedContinuousFunction
open MeasureTheory FourierTransform TemperedDistribution
open scoped SchwartzMap BoundedContinuousFunction Real ENNReal ContDiff
open MeasureTheory
open scoped ENNReal
open Set Filter
open scoped SchwartzMap ContDiff Topology
namespace YauCounterexamples
section SmoothFamily
variable {A E F : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

lemma contDiff_partial_iteratedFDeriv (f : A → E → F)
    (hf : ContDiff ℝ ∞ (Function.uncurry f)) (n : ℕ) :
    ContDiff ℝ ∞ (fun p : A × E => iteratedFDeriv ℝ n (f p.1) p.2) := by
  induction n with
  | zero =>
    simpa only [iteratedFDeriv_zero_eq_comp, Function.comp_apply, Function.uncurry_def, ContinuousLinearEquiv.coe_coe] using!
      ((continuousMultilinearCurryFin0 ℝ E F).symm.toContinuousLinearEquiv.contDiff.comp hf)
  | succ n ih =>
    have hh : ContDiff ℝ ∞ (fun z : (A × E) × E => iteratedFDeriv ℝ n (f z.1.1) z.2) :=
      ih.comp (contDiff_fst.fst.prodMk contDiff_snd)
    have hd : ContDiff ℝ ∞ (fun z : A × E => fderiv ℝ (iteratedFDeriv ℝ n (f z.1)) z.2) :=
      hh.fderiv contDiff_snd (by simp)
    simpa only [iteratedFDeriv_succ_eq_comp_left, Function.comp_apply, ContinuousLinearEquiv.coe_coe] using!
      ((continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (n + 1) => E) F).symm.toContinuousLinearEquiv.contDiff.comp hd)

end SmoothFamily
section CompactFamily
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem tendsto_schwartz_of_common_support
    (f : ℝ → 𝓢(E, F)) (hf : ContDiff ℝ ∞ (fun p : ℝ × E => f p.1 p.2))
    (K : Set E) (hK : IsCompact K) (hsupp : ∀ r, tsupport (f r) ⊆ K)
    (hzero : f 0 = 0) : Tendsto f (𝓝 0) (𝓝 0) := by
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  rw [(schwartz_withSeminorms ℝ E F).tendsto_nhds]
  rintro ⟨k, n⟩ ε hε
  have hc : Continuous (fun p : ℝ × K => ‖(p.2 : E)‖ ^ k *
      ‖iteratedFDeriv ℝ n (f p.1) (p.2 : E)‖) := by
    exact ((continuous_subtype_val.comp continuous_snd).norm.pow k).mul
      (((contDiff_partial_iteratedFDeriv (fun r x => f r x) hf n).continuous.comp
        (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))).norm)
  have hu := Continuous.tendstoUniformly
    (fun r (x : K) => ‖(x : E)‖ ^ k * ‖iteratedFDeriv ℝ n (f r) (x : E)‖) hc 0
  have he : ∀ᶠ r in 𝓝 (0 : ℝ), ∀ x : K,
      ‖(x : E)‖ ^ k * ‖iteratedFDeriv ℝ n (f r) (x : E)‖ < ε / 2 := by
    have hu' := (Metric.tendstoUniformly_iff.mp hu) (ε / 2) (by positivity)
    filter_upwards [hu'] with r hr
    intro x
    simpa [hzero, dist_comm, Real.dist_eq, abs_of_nonneg (by positivity :
      0 ≤ ‖(x : E)‖ ^ k * ‖iteratedFDeriv ℝ n (f r) (x : E)‖)] using hr x
  filter_upwards [he] with r hr
  simp only [sub_zero, SchwartzMap.schwartzSeminormFamily_apply]
  apply lt_of_le_of_lt (SchwartzMap.seminorm_le_bound ℝ k n (f r) (by positivity) ?_)
    (half_lt_self hε)
  intro x
  by_cases hx : x ∈ K
  · exact (hr ⟨x, hx⟩).le
  · have hz : iteratedFDeriv ℝ n (f r) x = 0 := by
      apply image_eq_zero_of_notMem_tsupport
      exact fun h => hx (hsupp r (tsupport_iteratedFDeriv_subset n h))
    simp only [hz, norm_zero, mul_zero]
    positivity

end CompactFamily

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
lemma χcoord_target (i : A.t) : tsupport (A.χcoord i) ⊆ (chartAt E (A.p i)).target :=
  (A.χcoord_support i).trans (A.localInverse i).in_target

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
lemma realH_closed (s : ℝ) : IsClosed (A.realH s : Set (A.H s)) := by
  change IsClosed {u | ∀ x, (A.representative s u x).im = 0}
  simp only [Set.ofPred_forall]
  apply isClosed_iInter
  intro x
  apply isClosed_eq _ continuous_const
  exact Complex.continuous_im.comp ((BoundedContinuousFunction.lipschitz_eval_const x).continuous.comp
    (A.representative s).continuous)

instance realH_completeSpace (s : ℝ) : CompleteSpace (A.realH s) :=
  (A.realH_closed s).completeSpace_coe

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
lemma realValue_sub (s : ℝ) (u v : A.realH s) (x : M) :
    A.realValue s (u - v) x = A.realValue s u x - A.realValue s v x := by
  simp [realValue]

omit [T2Space M] in
lemma realValue_inclusion (u : A.realH (2 * ((k + 1 : ℕ) : ℝ))) (x : M) :
    A.realValue (2 * (k : ℝ)) (A.realInclusion u) x =
      A.realValue (2 * ((k + 1 : ℕ) : ℝ)) u x := by
  change (A.representative _ (A.inclusion u) x).re = _
  rw [A.inclusion_representative]
  rfl

lemma realResolvent_value (B : ∀ i, A.PatchCoefficients i) (α : ℝ) (hα0 : 0 < α)
    (hα : ∀ i, 1 ≤ α * (A.localInverse i).radius ^ 2)
    (he : A.errorBound B α ≤ 1 / 2) (u : A.realH (2 * (k : ℝ))) (x : M) :
    α * A.realValue (2 * ((k + 1 : ℕ) : ℝ)) (A.realResolvent B α hα0 hα he u) x -
      laplaceBeltrami g (A.realValue (2 * ((k + 1 : ℕ) : ℝ))
        (A.realResolvent B α hα0 hα he u)) x = A.realValue (2 * (k : ℝ)) u x := by
  change α * (A.representative _ (A.resolvent B α hα he u) x).re -
      laplaceBeltrami g (fun y => (A.representative _ (A.resolvent B α hα he u) y).re) x =
        (A.representative (2 * (k : ℝ)) u.val x).re
  have h := congrArg Complex.re (A.resolvent_equation B α hα he u x)
  simpa only [Complex.sub_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero, complexLaplaceBeltrami, Complex.add_re, Complex.mul_re,
    Complex.I_re, Complex.I_im, Complex.ofReal_im, mul_zero, mul_one, sub_zero,
    add_zero, Function.comp_def] using h

end CompactMetricAtlas

end

open Set Filter Function Manifold
open scoped Topology ContDiff BoundedContinuousFunction

end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Estimates_CoefficientPerturbationTendsto
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
open Set Filter Function
open scoped Topology
open Set Filter Function
open scoped ContDiff Topology Manifold BoundedContinuousFunction
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M]
namespace CompactMetricAtlas
variable {g : SmoothMetric E M} {k : ℕ} {hs : Module.finrank ℝ E < 2 * (2 * (k : ℝ))}
variable (A : CompactMetricAtlas g k hs) (q : SmoothMetric E M)

omit [T2Space M] in
lemma varyingRealLaplacian_value (B : ∀ i, A.VaryingPatchCoefficients q i)
    (u : A.realH (2 * ((k + 1 : ℕ) : ℝ))) (x : M) :
    A.realValue (2 * (k : ℝ)) (A.varyingRealLaplacian q B u) x =
      laplaceBeltrami q (A.realValue (2 * ((k + 1 : ℕ) : ℝ)) u) x := by
  change (A.representative _ (A.varyingLaplacianCLM q B u) x).re = _
  rw [A.varyingLaplacianCLM_representative]
  rfl

omit [T2Space M] in
lemma varyingShift_value (B : ∀ i, A.VaryingPatchCoefficients q i) (α : ℝ)
    (u : A.realH (2 * ((k + 1 : ℕ) : ℝ))) (x : M) :
    A.realValue (2 * (k : ℝ)) (A.varyingShift q B α u) x =
      α * A.realValue (2 * ((k + 1 : ℕ) : ℝ)) u x -
        laplaceBeltrami q (A.realValue (2 * ((k + 1 : ℕ) : ℝ)) u) x := by
  simp only [varyingShift, sub_apply, smul_apply,
    A.realValue_sub, A.realValue_smul, A.realValue_inclusion, A.varyingRealLaplacian_value]

end CompactMetricAtlas

end

open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open Set Filter Manifold Bundle MeasureTheory NNReal
open scoped Topology ContDiff ENNReal
open Set Filter Topology NNReal
open Set Filter Module
open scoped Topology
open Set Filter Function
open scoped Topology
open Set Filter Function
open scoped Topology ContDiff Manifold BoundedContinuousFunction SchwartzMap
section CoefficientOperatorContinuity
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

lemma coefficientPerturbation_tendsto_at {ι P : Type*} [Fintype ι] {l : Filter P}
    (b : ι → E) {s : ℝ} (hs : Module.finrank ℝ E < 2 * s)
    (a : P → ι → ι → FourierSobolevSpace E ℂ s) (c : P → ι → FourierSobolevSpace E ℂ s)
    (a₀ : ι → ι → FourierSobolevSpace E ℂ s) (c₀ : ι → FourierSobolevSpace E ℂ s)
    (ha : ∀ i j, Tendsto (fun p => a p i j) l (𝓝 (a₀ i j)))
    (hc : ∀ i, Tendsto (fun p => c p i) l (𝓝 (c₀ i))) :
    Tendsto (fun p => coefficientPerturbation b hs (a p) (c p)) l
      (𝓝 (coefficientPerturbation b hs a₀ c₀)) := by
  have hmul {f : P → FourierSobolevSpace E ℂ s} {f₀ : FourierSobolevSpace E ℂ s}
      (hf : Tendsto f l (𝓝 f₀))
      (D : FourierSobolevSpace E ℂ (s + 2) →L[ℂ] FourierSobolevSpace E ℂ s) :
      Tendsto (fun p => (sobolevProduct hs (f p)) ∘L D) l
        (𝓝 ((sobolevProduct hs f₀) ∘L D)) := by
    have hh : Continuous (fun v : FourierSobolevSpace E ℂ s => (sobolevProduct hs v) ∘L D) := by
      fun_prop
    exact hh.continuousAt.tendsto.comp hf
  exact (tendsto_finsetSum Finset.univ (fun i _ =>
    tendsto_finsetSum Finset.univ (fun j _ => hmul (ha i j) _))).add
      (tendsto_finsetSum Finset.univ (fun i _ => hmul (hc i) _))
end CoefficientOperatorContinuity
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M]
namespace CompactMetricAtlas
variable {g : SmoothMetric E M} {k : ℕ} {hs : Module.finrank ℝ E < 2 * (2 * (k : ℝ))}
variable (A : CompactMetricAtlas g k hs)

attribute [local instance] OAI.YauCounterexamples.CompactMetricAtlas.H_nacg
attribute [local instance] OAI.YauCounterexamples.CompactMetricAtlas.H_ns
omit [T2Space M] in

theorem varyingLaplacianCLM_tendsto {P : Type*} {l : Filter P}
    (q : P → SmoothMetric E M) (q₀ : SmoothMetric E M)
    (C : ∀ p i, A.VaryingPatchCoefficients (q p) i)
    (C₀ : ∀ i, A.VaryingPatchCoefficients q₀ i)
    (ha : ∀ i j m, Tendsto (fun p => schwartzToSobolev (2 * (k : ℝ))
      (A.metricCoefficientSchwartz i ((C p i).a j m) ((C p i).smooth_a j m))) l
      (𝓝 (schwartzToSobolev (2 * (k : ℝ))
        (A.metricCoefficientSchwartz i ((C₀ i).a j m) ((C₀ i).smooth_a j m)))))
    (hc : ∀ i j, Tendsto (fun p => schwartzToSobolev (2 * (k : ℝ))
      (A.metricCoefficientSchwartz i ((C p i).c j) ((C p i).smooth_c j))) l
      (𝓝 (schwartzToSobolev (2 * (k : ℝ))
        (A.metricCoefficientSchwartz i ((C₀ i).c j) ((C₀ i).smooth_c j))))) :
    Tendsto (fun p => A.varyingLaplacianCLM (q p) (C p)) l
      (𝓝 (A.varyingLaplacianCLM q₀ C₀)) := by
  apply tendsto_finsetSum Finset.univ
  intro i _
  have hpert := coefficientPerturbation_tendsto_at (Module.finBasis ℝ E) hs _ _ _ _ (ha i) (hc i)
  have hres : Continuous (fun D : FourierSobolevSpace E ℂ (2 * (k : ℝ) + 2) →L[ℂ]
      FourierSobolevSpace E ℂ (2 * (k : ℝ)) => D.restrictScalars ℝ) :=
    (ContinuousLinearMap.restrictScalarsIsometry ℂ _ _ ℝ ℝ).continuous
  have hout : Continuous (fun D : FourierSobolevSpace E ℂ (2 * ((k + 1 : ℕ) : ℝ)) →L[ℝ]
      FourierSobolevSpace E ℂ (2 * (k : ℝ)) =>
      A.lift (A.p i) (A.η i) (A.chart_η i) (A.smooth_η i) k ∘L D ∘L
        A.cutoffLocalization (A.p i) (A.χ i) (A.chart_χ i) (A.smooth_χ i) (k + 1)) := by
    fun_prop
  exact hout.continuousAt.tendsto.comp (hres.continuousAt.tendsto.comp hpert)

omit [T2Space M] in
lemma varyingRealLaplacian_norm_sub_le (q q₀ : SmoothMetric E M)
    (C : ∀ i, A.VaryingPatchCoefficients q i) (C₀ : ∀ i, A.VaryingPatchCoefficients q₀ i) :
    ‖A.varyingRealLaplacian q C - A.varyingRealLaplacian q₀ C₀‖ ≤
      ‖A.varyingLaplacianCLM q C - A.varyingLaplacianCLM q₀ C₀‖ := by
  apply ContinuousLinearMap.opNorm_le_bound (A.varyingRealLaplacian q C - A.varyingRealLaplacian q₀ C₀) (norm_nonneg _)
  intro v
  exact (A.varyingLaplacianCLM q C - A.varyingLaplacianCLM q₀ C₀).le_opNorm v.val

omit [T2Space M] in
lemma varyingRealLaplacian_tendsto {P : Type*} {l : Filter P}
    (q : P → SmoothMetric E M) (q₀ : SmoothMetric E M)
    (C : ∀ p i, A.VaryingPatchCoefficients (q p) i)
    (C₀ : ∀ i, A.VaryingPatchCoefficients q₀ i)
    (h : Tendsto (fun p => A.varyingLaplacianCLM (q p) (C p)) l
      (𝓝 (A.varyingLaplacianCLM q₀ C₀))) :
    Tendsto (fun p => A.varyingRealLaplacian (q p) (C p)) l
      (𝓝 (A.varyingRealLaplacian q₀ C₀)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero] at h ⊢
  exact squeeze_zero (fun _ => norm_nonneg _) (fun p =>
    A.varyingRealLaplacian_norm_sub_le (q p) q₀ (C p) C₀) h

omit [T2Space M] in
lemma varyingShift_tendsto {P : Type*} {l : Filter P}
    (q : P → SmoothMetric E M) (q₀ : SmoothMetric E M)
    (C : ∀ p i, A.VaryingPatchCoefficients (q p) i)
    (C₀ : ∀ i, A.VaryingPatchCoefficients q₀ i) (α : ℝ)
    (h : Tendsto (fun p => A.varyingLaplacianCLM (q p) (C p)) l
      (𝓝 (A.varyingLaplacianCLM q₀ C₀))) :
    Tendsto (fun p => A.varyingShift (q p) (C p) α) l (𝓝 (A.varyingShift q₀ C₀ α)) :=
  tendsto_const_nhds.sub (A.varyingRealLaplacian_tendsto q q₀ C C₀ h)
end CompactMetricAtlas


end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Estimates_PreconditionedInverse
attribute [-instance] _root_.OAI.YauCounterexamples.circle_dimension_fact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open Set Filter Manifold Bundle MeasureTheory NNReal
open scoped Topology ContDiff ENNReal
open Set Filter Topology NNReal
open Set Filter Module
open scoped Topology
open Set Filter Function
open scoped Topology
namespace YauCounterexamples
variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]

omit [CompleteSpace X] in
lemma preconditionedInverse_base (R : X →L[ℝ] Y) (L : Y →L[ℝ] X)
    (h : L ∘L R = 1) : preconditionedInverse R L = R := by
  simp only [preconditionedInverse, h, Ring.inverse_one]
  rfl

lemma continuousAt_preconditionedInverse (R : X →L[ℝ] Y) (L : Y →L[ℝ] X)
    (h : IsUnit (L ∘L R)) : ContinuousAt (preconditionedInverse R) L := by
  have hm : Continuous (fun T : Y →L[ℝ] X => T ∘L R) := by fun_prop
  have hi : ContinuousAt Ring.inverse (L ∘L R) := by
    obtain ⟨u, hu⟩ := h
    rw [← hu]
    exact NormedRing.inverse_continuousAt u
  have hI : Tendsto (fun T : Y →L[ℝ] X => Ring.inverse (T ∘L R)) (𝓝 L)
      (𝓝 (Ring.inverse (L ∘L R))) := hi.tendsto.comp hm.continuousAt.tendsto
  have hout : Continuous (fun D : X →L[ℝ] X => R ∘L D) := by fun_prop
  exact hout.continuousAt.tendsto.comp hI

lemma eventuallyIsUnit_preconditioned (R : X →L[ℝ] Y) (L : Y →L[ℝ] X)
    (h : IsUnit (L ∘L R)) : ∀ᶠ T in 𝓝 L, IsUnit (T ∘L R) := by
  have hm : Continuous (fun T : Y →L[ℝ] X => T ∘L R) := by fun_prop
  exact hm.continuousAt.eventually (Units.isOpen.mem_nhds h)

lemma preconditionedInverse_tendsto {P : Type*} {l : Filter P}
    (R : X →L[ℝ] Y) (L : Y →L[ℝ] X) (h : L ∘L R = 1)
    (T : P → Y →L[ℝ] X) (hT : Tendsto T l (𝓝 L)) :
    Tendsto (fun p => preconditionedInverse R (T p)) l (𝓝 R) := by
  have hi : IsUnit (L ∘L R) := h ▸ isUnit_one
  simpa only [preconditionedInverse_base R L h, Function.comp_def] using
    (continuousAt_preconditionedInverse R L hi).tendsto.comp hT
end YauCounterexamples

end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Smoothness_JointMetricDet
attribute [-instance] _root_.OAI.YauCounterexamples.MetricIntegralAtlas.volumeMeasure_finite _root_.OAI.YauCounterexamples.MetricIntegralAtlas.volumeMeasure_openPos _root_.OAI.YauCounterexamples.circle_dimension_fact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Function Manifold
open scoped Topology ContDiff BoundedContinuousFunction SchwartzMap
namespace YauCounterexamples

section CutoffFamily
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

lemma contDiff_joint_cutoff {χ : E → ℂ} (hχ : ContDiff ℝ ∞ χ)
    {f : ℝ × E → ℂ}
    (hf : ∀ t y, y ∈ tsupport χ → ContDiffAt ℝ ∞ f (t,y)) :
    ContDiff ℝ ∞ (fun z : ℝ × E => χ z.2 * f z) := by
  rw [← contMDiff_iff_contDiff]
  apply contMDiff_of_tsupport
  intro z hz
  have hzχ : z ∈ tsupport (fun z : ℝ × E => χ z.2) :=
    tsupport_mul_subset_left hz
  have hy : z.2 ∈ tsupport χ :=
    tsupport_comp_subset_preimage χ continuous_snd hzχ
  rw [contMDiffAt_iff_contDiffAt]
  exact (hχ.contDiffAt.comp z contDiffAt_snd).mul (hf z.1 z.2 hy)

lemma tendsto_schwartz_family (f : ℝ → 𝓢(E,ℂ))
    (hf : ContDiff ℝ ∞ (fun z : ℝ × E => f z.1 z.2))
    (K : Set E) (hK : IsCompact K) (hsupp : ∀ t, tsupport (f t) ⊆ K) :
    Tendsto f (𝓝 0) (𝓝 (f 0)) := by
  have h0 : (fun t => f t-f 0) 0 = 0 := sub_self _
  have hj : ContDiff ℝ ∞ (fun z : ℝ × E => (f z.1-f 0) z.2) :=
    hf.sub ((f 0).smooth'.comp contDiff_snd)
  have hs (t : ℝ) : tsupport (f t-f 0) ⊆ K := by
    exact (tsupport_sub (f t) (f 0)).trans (union_subset (hsupp t) (hsupp 0))
  have hh := tendsto_schwartz_of_common_support (fun t => f t-f 0) hj K hK hs h0
  simpa only [sub_add_cancel,zero_add] using hh.add
    (tendsto_const_nhds : Tendsto (fun _ : ℝ => f 0) (𝓝 0) (𝓝 (f 0)))
end CutoffFamily

variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [T2Space M] [CompactSpace M]
namespace CompactMetricAtlas
variable {g : SmoothMetric E M} {k : ℕ} {hs : Module.finrank ℝ E < 2*(2*(k:ℝ))}
variable (A : CompactMetricAtlas g k hs)

omit [T2Space M] in
lemma metricCoefficientSchwartz_common_support (i : A.t) (f : E → ℝ) (hf : ContDiff ℝ ∞ f) :
    tsupport (A.metricCoefficientSchwartz i f hf) ⊆ tsupport (A.χcoord i) :=
  tsupport_mul_subset_left

omit [T2Space M] in
lemma varyingCoefficientSchwartz_a_value (q : SmoothMetric E M) (i : A.t)
    (C : A.VaryingPatchCoefficients q i) (j l : CoordIndex E) (y : E) :
    A.metricCoefficientSchwartz i (C.a j l) (C.smooth_a j l) y =
      A.χcoord i y * ((metricCoefficients q (A.p i) y)⁻¹ j l : ℂ) := by
  change A.χcoord i y * (C.a j l y : ℂ) = _
  by_cases hy : A.χcoord i y = 0
  · simp [hy]
  · rw [C.eq_a y (subset_tsupport _ hy)]

omit [T2Space M] in
lemma varyingCoefficientSchwartz_c_value (q : SmoothMetric E M) (i : A.t)
    (C : A.VaryingPatchCoefficients q i) (j : CoordIndex E) (y : E) :
    A.metricCoefficientSchwartz i (C.c j) (C.smooth_c j) y =
      A.χcoord i y * (metricFirstCoefficient q (A.p i) j y : ℂ) := by
  change A.χcoord i y * (C.c j y : ℂ) = _
  by_cases hy : A.χcoord i y = 0
  · simp [hy]
  · rw [C.eq_c y (subset_tsupport _ hy)]

omit [T2Space M] in
theorem smoothFamily_varyingLaplacian_tendsto (q : ℝ → SmoothMetric E M)
    (hq : ∀ i t y, y ∈ (chartAt E (A.p i)).target → ∀ j l,
      ContDiffAt ℝ ∞ (fun z : ℝ × E => metricCoefficients (q z.1) (A.p i) z.2 j l) (t,y))
    (C : ∀ t i, A.VaryingPatchCoefficients (q t) i) :
    Tendsto (fun t => A.varyingLaplacianCLM (q t) (C t)) (𝓝 0)
      (𝓝 (A.varyingLaplacianCLM (q 0) (C 0))) := by
  apply A.varyingLaplacianCLM_tendsto q (q 0) C (C 0)
  · intro i j l
    apply (schwartzToSobolev (2*(k:ℝ))).continuous.tendsto _ |>.comp
    apply tendsto_schwartz_family _ _ (tsupport (A.χcoord i)) (A.compact_χcoord i)
      (fun t => A.metricCoefficientSchwartz_common_support i _ _)
    simp_rw [A.varyingCoefficientSchwartz_a_value]
    apply contDiff_joint_cutoff (A.smooth_χcoord i)
    intro t y hy
    exact Complex.ofRealCLM.contDiff.contDiffAt.comp _
      (joint_metricInverse q (A.p i) (hq i) t (A.χcoord_target i hy) j l)
  · intro i j
    apply (schwartzToSobolev (2*(k:ℝ))).continuous.tendsto _ |>.comp
    apply tendsto_schwartz_family _ _ (tsupport (A.χcoord i)) (A.compact_χcoord i)
      (fun t => A.metricCoefficientSchwartz_common_support i _ _)
    simp_rw [A.varyingCoefficientSchwartz_c_value]
    apply contDiff_joint_cutoff (A.smooth_χcoord i)
    intro t y hy
    exact Complex.ofRealCLM.contDiff.contDiffAt.comp _
      (joint_metricFirstCoefficient q (A.p i) (hq i) t (A.χcoord_target i hy) j)
end CompactMetricAtlas
end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Spectrum_VaryingSpectralResolventBase
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
open Set Filter Function
open scoped Topology
open Set Filter Function
open scoped ContDiff Topology Manifold BoundedContinuousFunction
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M]
namespace CompactMetricAtlas
variable {g : SmoothMetric E M} {k : ℕ} {hs : Module.finrank ℝ E < 2 * (2 * (k : ℝ))}
variable (A : CompactMetricAtlas g k hs)

lemma varyingShift_base_comp_resolvent (B : ∀ i, A.PatchCoefficients i) (α : ℝ) (hα0 : 0 < α)
    (hα : ∀ i, 1 ≤ α * (A.localInverse i).radius ^ 2)
    (he : A.errorBound B α ≤ 1 / 2) (C : ∀ i, A.VaryingPatchCoefficients g i) :
    A.varyingShift g C α ∘L A.realResolvent B α hα0 hα he = 1 := by
  apply ContinuousLinearMap.ext
  intro u
  apply A.realRepresentative_injective _ hs
  ext x
  change A.realValue _ (A.varyingShift g C α (A.realResolvent B α hα0 hα he u)) x = _
  rw [A.varyingShift_value]
  exact A.realResolvent_value B α hα0 hα he u x

theorem varyingResolvent_tendsto {P : Type*} {l : Filter P}
    (B : ∀ i, A.PatchCoefficients i) (α : ℝ) (hα0 : 0 < α)
    (hα : ∀ i, 1 ≤ α * (A.localInverse i).radius ^ 2)
    (he : A.errorBound B α ≤ 1 / 2) (C₀ : ∀ i, A.VaryingPatchCoefficients g i)
    (q : P → SmoothMetric E M) (C : ∀ p i, A.VaryingPatchCoefficients (q p) i)
    (hC : Tendsto (fun p => A.varyingShift (q p) (C p) α) l (𝓝 (A.varyingShift g C₀ α))) :
    (∀ᶠ p in l, IsUnit (A.varyingShift (q p) (C p) α ∘L A.realResolvent B α hα0 hα he)) ∧
      Tendsto (fun p => A.varyingResolvent B α hα0 hα he (q p) (C p)) l
        (𝓝 (A.realResolvent B α hα0 hα he)) := by
  have hb := A.varyingShift_base_comp_resolvent B α hα0 hα he C₀
  exact ⟨hC.eventually (eventuallyIsUnit_preconditioned _ _ (hb ▸ isUnit_one)),
    preconditionedInverse_tendsto _ _ hb _ hC⟩
end CompactMetricAtlas

end


section
open Set Filter Function Manifold Bundle
open scoped Topology ContDiff BoundedContinuousFunction
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [CompactSpace M] [T2Space M]

namespace CompactMetricAtlas
variable {g : SmoothMetric E M} {k : ℕ} {hs : Module.finrank ℝ E < 2*(2*(k:ℝ))}
variable (A : CompactMetricAtlas g k hs)

theorem smoothFamily_resolvent_tendsto_oai
    (B : ∀ i, A.PatchCoefficients i) (α : ℝ) (hα0 : 0 < α)
    (hα : ∀ i, 1 ≤ α*(A.localInverse i).radius^2) (he : A.errorBound B α ≤ 1/2)
    (q : ℝ → SmoothMetric E M) (hq0 : q 0 = g)
    (hq : ∀ i t y, y ∈ (chartAt E (A.p i)).target → ∀ j l,
      ContDiffAt ℝ ∞ (fun z : ℝ × E => metricCoefficients (q z.1) (A.p i) z.2 j l) (t,y))
    (C : ∀ t i, A.VaryingPatchCoefficients (q t) i) :
    (∀ᶠ t in 𝓝 (0:ℝ), IsUnit (A.varyingShift (q t) (C t) α ∘L A.realResolvent B α hα0 hα he)) ∧
    Tendsto (fun t => A.varyingSpectralResolvent B α hα0 hα he (q t) (C t)) (𝓝 (0:ℝ))
      (𝓝 (A.realSpectralResolvent B α hα0 hα he)) := by
  let C₀ : ∀ i, A.VaryingPatchCoefficients g i := hq0 ▸ C 0
  have hc := A.smoothFamily_varyingLaplacian_tendsto q hq C
  have hbase : A.varyingLaplacianCLM (q 0) (C 0) = A.varyingLaplacianCLM g C₀ := by
    subst g
    rfl
  rw [hbase] at hc
  obtain ⟨hunit,hlim⟩ := A.varyingResolvent_tendsto B α hα0 hα he C₀ q C
    (A.varyingShift_tendsto q g C C₀ α hc)
  have hcont : Continuous (fun R : A.realH (2*(k:ℝ)) →L[ℝ] A.realH (2*((k+1:ℕ):ℝ)) =>
      A.realInclusion ∘L R) := by fun_prop
  exact ⟨hunit,hcont.tendsto _ |>.comp hlim⟩
end CompactMetricAtlas
end


open Set Filter Function Manifold Bundle
open scoped Topology ContDiff BoundedContinuousFunction

end YauCounterexamples
end

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.YauCounterexamples.CompactMetricAtlas.smoothFamily_resolvent_tendsto_oai.{u_1, u_2} := @OAI.YauCounterexamples.CompactMetricAtlas.smoothFamily_resolvent_tendsto_oai.{u_1, u_2}
