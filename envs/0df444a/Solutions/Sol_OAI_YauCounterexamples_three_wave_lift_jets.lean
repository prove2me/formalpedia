-- Prove2me | solution 1 for OAI.YauCounterexamples.three_wave_lift_jets
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T13:39:26.990321+00:00
-- url     : https://prove2.me/submissions/c9a68771-5f2f-4b27-a50b-20a8540e18a8

import Mathlib
import Definitions.Def_SmoothYau
import Definitions.Def_OAIQ070A010
import Theorems.Thm_OAI_YauCounterexamples_threeWaveLift_laplacian

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Limits_ManifoldChartPush
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
open Set Filter Manifold
open scoped Topology ContDiff
namespace YauCounterexamples
variable {E V M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M]

omit [NormedSpace ℝ E] [NormedSpace ℝ V] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] in
lemma manifoldChartPush_apply (p : M) (f : E → V) {y : E}
    (hy : y ∈ (chartAt E p).target) :
    manifoldChartPush p f ((chartAt E p).symm y) = f y := by
  simp only [manifoldChartPush, Set.indicator_of_mem ((chartAt E p).map_target hy),
    Function.comp_apply, (chartAt E p).right_inv hy]

end YauCounterexamples

end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Spectrum_JointLocalLaplacian
attribute [-instance] _root_.OAI.YauCounterexamples.MetricIntegralAtlas.volumeMeasure_finite _root_.OAI.YauCounterexamples.MetricIntegralAtlas.volumeMeasure_openPos _root_.OAI.YauCounterexamples.circle_dimension_fact
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

lemma contDiffAt_metricFlux {u : M → ℝ}
    (hu : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ u) (g : SmoothMetric E M)
    (p : M) {y : E} (hy : y ∈ (chartAt E p).target) (i : CoordIndex E) :
    ContDiffAt ℝ ∞ (fun z => metricFlux g u p z i) y := by
  have hd := (contDiffOn_metricDensity g p).contDiffAt ((chartAt E p).open_target.mem_nhds hy)
  apply hd.mul
  apply ContDiffAt.sum
  intro j _
  have ha := (contDiffOn_metricInverse g p i j).contDiffAt ((chartAt E p).open_target.mem_nhds hy)
  have hv := (contDiffAt_inChart hu p hy).fderiv_right (m := ∞) (by simp)
  exact ha.mul (hv.clm_apply contDiffAt_const)

lemma contDiffAt_localLaplacian {u : M → ℝ}
    (hu : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ u) (g : SmoothMetric E M)
    (p : M) {y : E} (hy : y ∈ (chartAt E p).target) :
    ContDiffAt ℝ ∞ (localLaplacian g u p) y := by
  have hd := (contDiffOn_metricDensity g p).contDiffAt ((chartAt E p).open_target.mem_nhds hy)
  have hn : Real.sqrt (metricCoefficients g p y).det ≠ 0 :=
    (Real.sqrt_pos.mpr (metricCoefficients_det_pos g p hy)).ne'
  apply (hd.inv hn).mul
  apply ContDiffAt.sum
  intro i _
  exact ((contDiffAt_metricFlux hu g p hy i).fderiv_right (m := ∞) (by simp)).clm_apply contDiffAt_const

lemma contMDiff_laplaceBeltrami {u : M → ℝ}
    (hu : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ u) (g : SmoothMetric E M) :
    ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ (laplaceBeltrami g u) := by
  intro x
  rw [contMDiffAt_iff_source]
  simp only [mfld_simps, contMDiffWithinAt_univ, contMDiffAt_iff_contDiffAt]
  have hx := (chartAt E x).map_source (mem_chart_source E x)
  apply (contDiffAt_localLaplacian hu g x hx).congr_of_eventuallyEq
  filter_upwards [(chartAt E x).open_target.mem_nhds hx] with y hy
  have he := laplaceBeltrami_inChart hu g x ((chartAt E x).symm y) ((chartAt E x).map_target hy)
  simpa only [Function.comp_apply, (chartAt E x).right_inv hy] using he

end

open Set Filter Function Manifold
open scoped Topology ContDiff BoundedContinuousFunction

end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Smoothness_CompactMetricInverseJets
attribute [-instance] _root_.OAI.YauCounterexamples.circle_dimension_fact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples
section
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
open Set Filter MeasureTheory Metric
open scoped Topology ENNReal NNReal
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
open Set Filter Function
open scoped Topology ContDiff
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

lemma compact_raw_jet_bound {O K : Set E} (hO : IsOpen O) (hK : IsCompact K)
    (hKO : K ⊆ O) {f : E → F} (hf : ContDiffOn ℝ ∞ f O) (h : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ j ≤ h, ∀ x ∈ K, ‖iteratedFDeriv ℝ j f x‖ ≤ C := by
  have hb (j : ℕ) : ∃ C : ℝ, ∀ x ∈ K, ‖iteratedFDeriv ℝ j f x‖ ≤ C := by
    apply hK.exists_bound_of_continuousOn
    intro x hx
    exact (((hf.contDiffAt (hO.mem_nhds (hKO hx))).continuousAt_iteratedFDeriv
      (le_of_lt (WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top j))))).continuousWithinAt
  choose B hB using hb
  let C := 1+∑ j ∈ Finset.range (h+1), max 0 (B j)
  have hC : 1 ≤ C := by
    dsimp [C]
    exact le_add_of_nonneg_right (Finset.sum_nonneg (fun _ _ => le_max_left _ _))
  refine ⟨C,hC,?_⟩
  intro j hj x hx
  calc
    _ ≤ B j := hB j x hx
    _ ≤ max 0 (B j) := le_max_right _ _
    _ ≤ ∑ j ∈ Finset.range (h+1), max 0 (B j) :=
      Finset.single_le_sum (fun k _ => le_max_left _ _) (Finset.mem_range.mpr (by omega))
    _ ≤ C := by dsimp [C]; linarith


end

open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open Set Filter Manifold Bundle MeasureTheory NNReal
open scoped Topology ContDiff ENNReal
open Set Filter Topology NNReal
open Set Filter Module
open scoped Topology
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff Manifold
open Set Filter Function
open scoped Topology ContDiff Manifold Matrix
open Set Filter Function
open scoped Topology ContDiff Manifold Matrix
open Set Filter Function
open scoped Topology ContDiff Manifold Matrix
open Set Filter
open scoped Topology
open Set Filter Function MeasureTheory FourierTransform TemperedDistribution
open scoped Topology SchwartzMap ENNReal Real Laplacian BoundedContinuousFunction
open Set Filter Function
open scoped Topology ContDiff Manifold
open Set Filter Manifold Bundle Matrix
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff Manifold InnerProductSpace


end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Smoothness_ChartJetBoundGlobalValue
attribute [-instance] _root_.OAI.YauCounterexamples.circle_dimension_fact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples
section
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Matrix
open scoped Topology Matrix.Norms.Elementwise
open Set Filter Function
open scoped Topology ContDiff Manifold
variable {E F M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M] [T2Space M]

omit [FiniteDimensional ℝ E] [T2Space M] in
lemma contDiffOn_chartTransition_for_jets (p q : M) :
    ContDiffOn ℝ ∞ ((chartAt E p).symm.trans (chartAt E q))
      ((chartAt E p).symm.trans (chartAt E q)).source := by
  intro y hy
  have hy' : y ∈ (chartAt E p).target ∧ (chartAt E p).symm y ∈ (chartAt E q).source := hy
  exact (contMDiffAt_iff_contDiffAt.mp
    ((contMDiffAt_of_mem_maximalAtlas (IsManifold.chart_mem_maximalAtlas q) hy'.2).comp y
      (contMDiffAt_symm_of_mem_maximalAtlas (IsManifold.chart_mem_maximalAtlas p) hy'.1))).contDiffWithinAt

theorem compact_chart_jet_transfer (p q : M) {L : Set M} (hL : IsCompact L)
    (hLp : L ⊆ (chartAt E p).source) {K : Set E} (hK : IsCompact K)
    (hKq : K ⊆ (chartAt E q).target) (m : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (U : M → F) (f : E → F), ContDiff ℝ ∞ f →
      tsupport U ⊆ L → (∀ z ∈ (chartAt E p).target, U ((chartAt E p).symm z)=f z) →
      ∀ y ∈ K, ∀ j ≤ m, ∀ B : ℝ, 0 ≤ B →
        (∀ i ≤ j, ‖iteratedFDeriv ℝ i f (chartAt E p ((chartAt E q).symm y))‖ ≤ B) →
        ‖iteratedFDeriv ℝ j (U ∘ (chartAt E q).symm) y‖ ≤ C*B := by
  let c := chartAt E p
  let d := chartAt E q
  let T := (d.symm '' K) ∩ L
  have hT : IsCompact T := (hK.image_of_continuousOn (d.continuousOn_symm.mono hKq)).inter_right hL.isClosed
  have hTd : T ⊆ d.source := by
    rintro x ⟨⟨y,hy,rfl⟩,_⟩
    exact d.map_target (hKq hy)
  let S := d '' T
  have hS : IsCompact S := hT.image_of_continuousOn (d.continuousOn.mono hTd)
  let e := d.symm.trans c
  have hSe : S ⊆ e.source := by
    rintro y ⟨x,hx,rfl⟩
    refine ⟨d.map_source (hTd hx),?_⟩
    change d.symm (d x) ∈ c.source
    rw [d.left_inv (hTd hx)]
    exact hLp hx.2
  obtain ⟨ψ,hψ,heψ⟩ := smooth_extension_near_compact hS e.open_source hSe
    (contDiffOn_chartTransition_for_jets q p)
  obtain ⟨D,hD,hDj⟩ := compact_raw_jet_bound isOpen_univ hK (subset_univ _)
    hψ.contDiffOn m
  let C : ℝ := (m.factorial : ℝ)*D^m+1
  have hCp : 0 < C := by dsimp [C]; positivity
  refine ⟨C,hCp,?_⟩
  intro U f hf hUs hUf y hy j hj B hB hfj
  by_cases hx : d.symm y ∈ L
  · have hyS : y ∈ S := ⟨d.symm y,⟨⟨y,hy,rfl⟩,hx⟩,d.right_inv (hKq hy)⟩
    have hey := hSe hyS
    have heψy : (e : E → E) =ᶠ[𝓝 y] ψ := heψ.filter_mono (nhds_le_nhdsSet hyS)
    have heq : U ∘ d.symm =ᶠ[𝓝 y] f ∘ ψ := by
      filter_upwards [e.open_source.mem_nhds hey,heψy] with z hz hzz
      have hcz : d.symm z ∈ c.source := hz.2
      change U (d.symm z)=f (ψ z)
      rw [←hzz]
      change U (d.symm z)=f (c (d.symm z))
      rw [←hUf _ (c.map_source hcz),c.left_inv hcz]
    rw [(heq.iteratedFDeriv ℝ j).eq_of_nhds]
    have hb : ∀ i ≤ j, ‖iteratedFDeriv ℝ i f (ψ y)‖ ≤ B := by
      intro i hi
      rw [←heψy.eq_of_nhds]
      exact hfj i hi
    have hd : ∀ i, 1 ≤ i → i ≤ j → ‖iteratedFDeriv ℝ i ψ y‖ ≤ D^i := by
      intro i hi hij
      exact (hDj i (hij.trans hj) y hy).trans (by simpa using pow_le_pow_right₀ hD hi)
    have hbound := norm_iteratedFDeriv_comp_le hf hψ
      (le_of_lt (WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top j))) y hb hd
    apply hbound.trans
    have hfact : (j.factorial : ℝ) ≤ m.factorial := by exact_mod_cast Nat.factorial_le hj
    have hp := pow_le_pow_right₀ hD hj
    have hmul := mul_le_mul hfact hp (pow_nonneg (zero_le_one.trans hD) _) (Nat.cast_nonneg _)
    calc
      _ = ((j.factorial : ℝ)*D^j)*B := by ring
      _ ≤ ((m.factorial : ℝ)*D^m)*B := mul_le_mul_of_nonneg_right hmul hB
      _ ≤ C*B := mul_le_mul_of_nonneg_right (by dsimp [C]; linarith) hB
  · have hn : d.symm y ∉ tsupport U := fun h => hx (hUs h)
    have he : U ∘ d.symm =ᶠ[𝓝 y] (fun _ => (0:F)) :=
      (notMem_tsupport_iff_eventuallyEq.mp hn).comp_tendsto (d.continuousAt_symm (hKq hy)).tendsto
    rw [(he.iteratedFDeriv ℝ j).eq_of_nhds]
    simpa using mul_nonneg hCp.le hB


end

open Set Filter Function Manifold
open scoped Topology ContDiff

end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Spectrum_PinningFactorGradient
attribute [-instance] _root_.OAI.YauCounterexamples.MetricIntegralAtlas.volumeMeasure_finite _root_.OAI.YauCounterexamples.MetricIntegralAtlas.volumeMeasure_openPos _root_.OAI.YauCounterexamples.circle_dimension_fact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples
section
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Matrix
open scoped Topology Matrix.Norms.Elementwise
open Set Filter Manifold
open scoped Topology ContDiff
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ,E) ∞ M]

lemma laplaceBeltrami_congr_nhds (g : SmoothMetric E M) {u v : M → ℝ} {x : M}
    (hu : u =ᶠ[𝓝 x] v) : laplaceBeltrami g u x=laplaceBeltrami g v x := by
  let c := chartAt E x
  have hx := c.map_source (mem_chart_source E x)
  have ht : Tendsto c.symm (𝓝 (c x)) (𝓝 x) := by
    simpa only [c.left_inv (mem_chart_source E x)] using (c.continuousAt_symm hx).tendsto
  have hu' := (hu.comp_tendsto ht).fderiv (𝕜:=ℝ)
  have he (i : CoordIndex E) :
      (fun y => Real.sqrt (metricCoefficients g x y).det * ∑ j,
        (metricCoefficients g x y)⁻¹ i j * fderiv ℝ (u ∘ c.symm) y (Module.finBasis ℝ E j))
      =ᶠ[𝓝 (c x)]
      (fun y => Real.sqrt (metricCoefficients g x y).det * ∑ j,
        (metricCoefficients g x y)⁻¹ i j * fderiv ℝ (v ∘ c.symm) y (Module.finBasis ℝ E j)) := by
    filter_upwards [hu'] with y hy
    rw [hy]
  unfold laplaceBeltrami
  change (Real.sqrt (metricCoefficients g x (c x)).det)⁻¹ * ∑ i, _ = _
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  exact congrArg (fun T : E →L[ℝ] ℝ => T (Module.finBasis ℝ E i)) (he i).fderiv_eq

lemma laplaceBeltrami_tsupport (g : SmoothMetric E M) (u : M → ℝ) :
    tsupport (laplaceBeltrami g u) ⊆ tsupport u := by
  apply closure_minimal _ isClosed_closure
  intro x hx
  by_contra hn
  have he := laplaceBeltrami_congr_nhds g (notMem_tsupport_iff_eventuallyEq.mp hn)
  have hz : laplaceBeltrami g (fun _ : M => (0:ℝ)) x=0 := by
    simp [laplaceBeltrami,Function.comp_def]
  exact hx (he.trans hz)

lemma laplaceResidual_tsupport (g : SmoothMetric E M) (u : M → ℝ) (Λ : ℝ) :
    tsupport (fun x => laplaceBeltrami g u x+Λ*u x) ⊆ tsupport u := by
  apply (tsupport_add _ _).trans
  apply union_subset (laplaceBeltrami_tsupport g u)
  exact tsupport_mul_subset_right (f := fun _ : M => Λ) (g := u)

variable [T2Space M]

theorem compact_chart_weighted_jet_transfer (p q : M) {L : Set M} (hL : IsCompact L)
    (hLp : L ⊆ (chartAt E p).source) {K : Set E} (hK : IsCompact K)
    (hKq : K ⊆ (chartAt E q).target) (m : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (U : M → ℝ) (f : E → ℝ), ContDiff ℝ ∞ f →
      tsupport U ⊆ L → (∀ z ∈ (chartAt E p).target, U ((chartAt E p).symm z)=f z) →
      ∀ (B : ℕ → M → ℝ), (∀ j x, 0 ≤ B j x) →
      (∀ x ∈ L, ∀ j ≤ m, ∀ i ≤ j,
        ‖iteratedFDeriv ℝ i f (chartAt E p x)‖ ≤ B j x) →
      ∀ y ∈ K, ∀ j ≤ m,
        ‖iteratedFDeriv ℝ j (U ∘ (chartAt E q).symm) y‖ ≤ C*B j ((chartAt E q).symm y) := by
  obtain ⟨C,hC,hT⟩ := compact_chart_jet_transfer (F := ℝ) p q hL hLp hK hKq m
  refine ⟨C,hC,?_⟩
  intro U f hf hs he B hB hb y hy j hj
  by_cases hx : (chartAt E q).symm y ∈ L
  · exact hT U f hf hs he y hy j hj _ (hB j _) (fun i hi => hb _ hx j hj i hi)
  · have hn : (chartAt E q).symm y ∉ tsupport U := fun h => hx (hs h)
    have hzero : U ∘ (chartAt E q).symm =ᶠ[𝓝 y] (fun _ => (0:ℝ)) :=
      (notMem_tsupport_iff_eventuallyEq.mp hn).comp_tendsto
        ((chartAt E q).continuousAt_symm (hKq hy)).tendsto
    rw [(hzero.iteratedFDeriv ℝ j).eq_of_nhds]
    simpa using mul_nonneg hC.le (hB j ((chartAt E q).symm y))


end



open Set Filter Function Manifold Metric
open scoped Topology ContDiff

end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_SphereMetric_ThreeRobustProfileNormedSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples


section
open Set Filter Function Manifold Metric MeasureTheory BoxIntegral
open scoped Topology ContDiff InnerProductSpace
lemma threeNormalGlue_tsupport (C : ℝ) {f : NormalWaveSpace → ℝ}
    (hc : HasCompactSupport (fun y => f y-C)) {K : Set NormalWaveSpace}
    (hK : tsupport (fun y => f y-C) ⊆ K) :
    tsupport (fun p => threeNormalGlue C f p-C) ⊆ threeNormalInv '' K := by
  have he : (fun p => threeNormalGlue C f p-C)=
      manifoldChartPush threeProfileCenter ((fun y => f y-C) ∘ threeNormalEquiv.symm) := by
    funext p; simp [threeNormalGlue]
  rw [he]
  intro p hp
  obtain ⟨y,hy,rfl⟩ := manifoldChartPush_tsupport _
    (hc.comp_homeomorph threeNormalEquiv.symm.toHomeomorph)
    (by rw [three_chart_target]; exact subset_univ _) hp
  rw [tsupport_comp_eq_preimage _ threeNormalEquiv.symm.toHomeomorph] at hy
  refine ⟨threeNormalEquiv.symm y,hK hy,?_⟩
  simp [threeNormalInv]
end


open Set Filter Function Manifold Metric MeasureTheory BoxIntegral
open scoped Topology ContDiff InnerProductSpace

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
lemma threeWaveLift_apply (u : NormalWaveSpace → ℝ) (y : NormalWaveSpace) :
    threeWaveLift u (threeNormalInv y)=u y := by
  dsimp [threeWaveLift,threeNormalInv]
  rw [manifoldChartPush_apply _ _ (by rw [three_chart_target]; trivial)]
  simp
lemma threeWaveLift_tsupport {u : NormalWaveSpace → ℝ} (hc : HasCompactSupport u)
    {K : Set NormalWaveSpace} (hs : tsupport u⊆K) :
    tsupport (threeWaveLift u)⊆threeNormalInv '' K := by
  have he : threeWaveLift u=(fun p => threeNormalGlue 0 u p-0) := by
    funext p; simp [threeWaveLift,threeNormalGlue]
  rw [he]
  exact threeNormalGlue_tsupport 0 (by simpa using hc) (by simpa using hs)
lemma threeNormalInv_continuous : Continuous threeNormalInv :=
  (continuousOn_univ.mp (by simpa only [three_chart_target] using (chartAt ThreeModel threeProfileCenter).continuousOn_symm)).comp threeNormalEquiv.continuous
lemma threeNormalInv_image_source (K : Set NormalWaveSpace) :
    threeNormalInv '' K⊆(chartAt ThreeModel threeProfileCenter).source := by
  rintro p ⟨y,hy,rfl⟩
  exact (chartAt ThreeModel threeProfileCenter).map_target (by rw [three_chart_target]; trivial)

lemma linearEquiv_comp_jets_bound {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (L : F ≃L[ℝ] E) (m : ℕ) :
    ∃ C>0, ∀ (u : E → ℝ), ContDiff ℝ ∞ u → ∀ x : F, ∀ j  ≤  m, ∀ B : ℝ,
      0 ≤ B → ‖iteratedFDeriv ℝ j u (L x)‖ ≤ B → ‖iteratedFDeriv ℝ j (u ∘ L) x‖ ≤ C*B := by
  let c := max 1 ‖L.toContinuousLinearMap‖
  refine ⟨c^m, pow_pos (zero_lt_one.trans_le (le_max_left _ _)) _,?_⟩
  intro u hu x j hj B hB hb
  change ‖iteratedFDeriv ℝ j (u ∘ L.toContinuousLinearMap) x‖ ≤ _
  rw [L.toContinuousLinearMap.iteratedFDeriv_comp_right hu x (le_of_lt (WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top j)))]
  have hn := (iteratedFDeriv ℝ j u (L x)).norm_compContinuousLinearMap_le (fun _ : Fin j => L.toContinuousLinearMap)
  simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fin] at hn
  have hp : ‖L.toContinuousLinearMap‖^j ≤ c^m :=
    (pow_le_pow_left₀ (norm_nonneg _) (le_max_right _ _) _).trans (pow_le_pow_right₀ (le_max_left _ _) hj)
  exact hn.trans ((mul_le_mul hb hp (by positivity) hB).trans_eq (mul_comm _ _))

attribute [local instance] OAI.YauCounterexamples.threeLiftNormedSpace
local instance threeLiftContinuousSMul_r7ae1c1_1 : ContinuousSMul ℝ ThreeModel :=
  IsBoundedSMul.continuousSMul
theorem three_wave_lift_jets_oai (g : SmoothMetric ThreeModel ThreeManifold)
    (p : ThreeManifold) {K : Set ThreeModel} (hK : IsCompact K) (r : ℝ) (m : ℕ) :
    ∃ C>0, ∀ (u : NormalWaveSpace → ℝ), ContDiff ℝ ∞ u → HasCompactSupport u →
      tsupport u⊆closedBall 0 r →
      ∀ (B : ℕ → ThreeManifold → ℝ), (∀ j q, 0 ≤ B j q) →
      ∀ (R : ThreeManifold → ℝ), (∀ q, 0 ≤ R q) → ∀ Λ : ℝ,
      (∀ x : NormalWaveSpace, ∀ j  ≤  m, ∀ i  ≤  j,
        ‖iteratedFDeriv ℝ i u x‖ ≤ B j (threeNormalInv x)) →
      (∀ x : NormalWaveSpace, ∀ j  ≤  m,
        ‖iteratedFDeriv ℝ j (fun y => laplaceBeltrami (threeNormalMetricOf g) u y+Λ*u y) x‖ ≤ R (threeNormalInv x)) →
      ∀ y∈K, ∀ j  ≤  m,
        ‖iteratedFDeriv ℝ j (threeWaveLift u ∘ (chartAt ThreeModel p).symm) y‖ ≤ C*B j ((chartAt ThreeModel p).symm y) ∧
        ‖iteratedFDeriv ℝ j ((fun q => laplaceBeltrami g (threeWaveLift u) q+Λ*threeWaveLift u q) ∘
          (chartAt ThreeModel p).symm) y‖ ≤ C*R ((chartAt ThreeModel p).symm y) := by
  let L : Set ThreeManifold := threeNormalInv '' closedBall 0 r
  have hL : IsCompact L := (isCompact_closedBall _ _).image threeNormalInv_continuous
  have hLs : L⊆(chartAt ThreeModel threeProfileCenter).source := threeNormalInv_image_source _
  obtain ⟨C,hC,htransfer⟩ := compact_chart_weighted_jet_transfer threeProfileCenter p hL hLs hK
    (by rw [three_chart_target]; exact subset_univ _) m
  obtain ⟨D,hD,hlin⟩ := linearEquiv_comp_jets_bound threeNormalEquiv.symm m
  refine ⟨C*D,mul_pos hC hD,?_⟩
  intro u hu hc hs B hB R hR Λ hj hres y hy j hjm
  have hUs : tsupport (threeWaveLift u)⊆L := threeWaveLift_tsupport hc hs
  have he (z : ThreeModel) : threeNormalInv (threeNormalEquiv.symm z)=(chartAt ThreeModel threeProfileCenter).symm z := by
    simp [threeNormalInv]
  have hUe (z : ThreeModel) : threeWaveLift u ((chartAt ThreeModel threeProfileCenter).symm z)=(u ∘ threeNormalEquiv.symm) z := by
    rw [←he,threeWaveLift_apply]; rfl
  have hUj (q : ThreeManifold) (hq : q∈L) (j : ℕ) (hjm : j ≤ m) (i : ℕ) (hij : i ≤ j) :
      ‖iteratedFDeriv ℝ i (u ∘ threeNormalEquiv.symm) (chartAt ThreeModel threeProfileCenter q)‖  ≤  D*B j q := by
    apply hlin u hu _ i (hij.trans hjm) _ (hB _ _)
    have hh := hj (threeNormalEquiv.symm (chartAt ThreeModel threeProfileCenter q)) j hjm i hij
    simpa only [he,(chartAt ThreeModel threeProfileCenter).left_inv (hLs hq)] using hh
  have hRf : ContDiff ℝ ∞ (fun x => laplaceBeltrami (threeNormalMetricOf g) u x+Λ*u x) := by
    rw [←contMDiff_iff_contDiff]
    exact (contMDiff_laplaceBeltrami (contMDiff_iff_contDiff.mpr hu) _).add
      (contMDiff_const.mul (contMDiff_iff_contDiff.mpr hu))
  constructor
  · simpa only [mul_assoc] using htransfer _ _ (hu.comp threeNormalEquiv.symm.contDiff) hUs
      (fun z _ => hUe z) (fun j q => D*B j q) (fun j q => mul_nonneg hD.le (hB j q)) hUj y hy j hjm
  · have hRs : tsupport (fun q => laplaceBeltrami g (threeWaveLift u) q+Λ*threeWaveLift u q)⊆L :=
      (laplaceResidual_tsupport g _ Λ).trans hUs
    have hh := htransfer (fun q => laplaceBeltrami g (threeWaveLift u) q+Λ*threeWaveLift u q)
      ((fun x => laplaceBeltrami (threeNormalMetricOf g) u x+Λ*u x) ∘ threeNormalEquiv.symm)
      (hRf.comp threeNormalEquiv.symm.contDiff) hRs (fun z _ => by
        rw [←he z,threeWaveLift_laplacian g hu hc,threeWaveLift_apply]; rfl)
      (fun _ q => D*R q) (fun _ q => mul_nonneg hD.le (hR q))
      (fun q hq j hjm i hij => by
        apply hlin _ hRf _ i (hij.trans hjm) _ (hR q)
        have hh := hres (threeNormalEquiv.symm (chartAt ThreeModel threeProfileCenter q)) i (hij.trans hjm)
        simpa only [he,(chartAt ThreeModel threeProfileCenter).left_inv (hLs hq)] using hh) y hy j hjm
    simpa only [mul_assoc] using hh
end


open Set Filter Manifold Metric MeasureTheory BoxIntegral
open scoped Topology ContDiff ENNReal


end YauCounterexamples
end

end OAI
end

theorem solution : type_of% @OAI.YauCounterexamples.three_wave_lift_jets_oai := @OAI.YauCounterexamples.three_wave_lift_jets_oai
