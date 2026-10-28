-- Prove2me | solution 1 for OAI.YauCounterexamples.spherical_pin_near
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T13:25:16.306199+00:00
-- url     : https://prove2.me/submissions/d8832269-4f30-4804-b531-1df32dce374c

import Mathlib
import Definitions.Def_SmoothYau
import Definitions.Def_OAIQ070A010
import Theorems.Thm_OAI_YauCounterexamples_exists_annular_simple_pinned_family
import Theorems.Thm_OAI_YauCounterexamples_pinnedMetric_laplacian

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Spectrum_SphereProjection
attribute [-instance] _root_.OAI.YauCounterexamples.circle_dimension_fact _root_.OAI.YauCounterexamples.threeChartedSpace _root_.OAI.YauCounterexamples.threeIsManifold _root_.OAI.YauCounterexamples.threeProductChartedSpace _root_.OAI.YauCounterexamples.threeProductIsManifold
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
open Set Filter Manifold BoxIntegral Metric
open scoped Topology ContDiff InnerProductSpace

lemma sphericalRadius_nonneg (a b : Euclidean 4) (q : Sphere 3) :
    0 ≤ sphericalRadius a b q := Real.sqrt_nonneg _

lemma sphericalRadius_sq (a b : Euclidean 4) (q : Sphere 3) :
    (sphericalRadius a b q)^2 =
      (inner ℝ a (q : Euclidean 4))^2+(inner ℝ b (q : Euclidean 4))^2 :=
  Real.sq_sqrt (add_nonneg (sq_nonneg _) (sq_nonneg _))

lemma source_axes_orthonormal : inner ℝ sourceAxisOne sourceAxisOne = 1 ∧
    inner ℝ sourceAxisTwo sourceAxisTwo = 1 ∧ inner ℝ sourceAxisOne sourceAxisTwo = 0 := by
  norm_num [sourceAxisOne,sourceAxisTwo,EuclideanSpace.inner_single_left,PiLp.single_apply]


end

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
open Set Filter Function Module Manifold
open scoped Topology ContDiff InnerProductSpace Matrix



end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Smoothness_ChartTensorCoordLocal1
attribute [-instance] _root_.OAI.YauCounterexamples.circle_dimension_fact
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

end ContinuousSmoothFamilyOn
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
lemma neg {f : P → E → F} (hf : ContinuousSmoothFamilyOn f U) :
    ContinuousSmoothFamilyOn (fun p x => -f p x) U :=
  hf.postcomp (fun z : F => -z) (fun _ _ _ => contDiffAt_id.neg)
lemma sub {f g : P → E → F} (hf : ContinuousSmoothFamilyOn f U)
    (hg : ContinuousSmoothFamilyOn g U) : ContinuousSmoothFamilyOn (fun p x => f p x-g p x) U := by
  simpa only [sub_eq_add_neg] using hf.add hg.neg
end ContinuousSmoothFamilyOn

end


open Set Filter Function Manifold Bundle TopologicalSpace
open scoped Topology ContDiff Distributions

end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Smoothness_ContinuousCompactSmoothJets
attribute [-instance] _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_acg _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_mod _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_nacg _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_ns _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_snacg _root_.OAI.YauCounterexamples.MetricIntegralAtlas.volumeMeasure_finite _root_.OAI.YauCounterexamples.MetricIntegralAtlas.volumeMeasure_openPos _root_.OAI.YauCounterexamples.circle_dimension_fact
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
open scoped Topology ContDiff Matrix.Norms.Elementwise
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

lemma metricMatrixFormCLM_apply (A : Matrix (CoordIndex E) (CoordIndex E) ℝ) :
    metricMatrixFormCLM A = (metricMatrixForm A : CoordinateForm E) := rfl


end


open Set Filter Function Manifold Bundle TopologicalSpace
open scoped Topology ContDiff Distributions BoundedContinuousFunction Matrix.Norms.Elementwise
section CompactSmoothContinuity
variable {P E F : Type*} [TopologicalSpace P]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
lemma continuous_compactSmooth_of_jets (K : Compacts E) (f : P → 𝓓_{K}(E,F))
    (hf : ∀ n, Continuous (fun z : P × E => iteratedFDeriv ℝ n (f z.1) z.2)) : Continuous f := by
  rw [continuous_iff_continuousAt]
  intro a₀
  rw [ContinuousAt,(ContDiffMapSupportedIn.withSeminorms ℝ E F ⊤ K).tendsto_nhds]
  intro n ε hε
  have hj : Continuous (fun z : P × E => iteratedFDeriv ℝ n (f z.1-f a₀) z.2) := by
    have he : (fun z : P × E => iteratedFDeriv ℝ n (f z.1-f a₀) z.2) =
        (fun z : P × E => iteratedFDeriv ℝ n (f z.1) z.2-iteratedFDeriv ℝ n (f a₀) z.2) := by
      funext z
      exact iteratedFDeriv_sub_apply
        ((f z.1).contDiff.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl n)).contDiffAt
        ((f a₀).contDiff.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl n)).contDiffAt
    rw [he]
    exact (hf n).sub (((f a₀).contDiff.continuous_iteratedFDeriv
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl n)).comp continuous_snd)
  have he : ∀ᶠ a in 𝓝 a₀, ∀ y ∈ (K : Set E),
      ‖iteratedFDeriv ℝ n (f a-f a₀) y‖ < ε/2 := by
    apply K.isCompact.eventually_forall_of_forall_eventually
    intro y hy
    exact hj.norm.continuousAt.eventually (gt_mem_nhds (by simpa using half_pos hε))
  filter_upwards [he] with a ha
  apply lt_of_le_of_lt ?_ (half_lt_self hε)
  apply (ContDiffMapSupportedIn.seminorm_top_le_iff ℝ (half_pos hε).le _ _).mpr
  intro y hy
  exact (ha y hy).le
end CompactSmoothContinuity
namespace ContinuousSmoothFamilyOn
variable {P E F ι : Type*} [TopologicalSpace P]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [Fintype ι]
lemma pi {f : P → E → ι → F} {U : Set E}
    (hf : ∀ i, ContinuousSmoothFamilyOn (fun p x => f p x i) U) :
    ContinuousSmoothFamilyOn f U := by
  classical
  have hh := sum Finset.univ (fun i p x => Pi.single i (f p x i)) (fun i _ =>
    (hf i).postcomp (ContinuousLinearMap.single ℝ (fun _ : ι => F) i)
      (fun _ _ _ => (ContinuousLinearMap.single ℝ (fun _ : ι => F) i).contDiff.contDiffAt))
  have he : (fun p x => ∑ i, Pi.single i (f p x i)) = f := by
    funext p x i
    simp
  rwa [he] at hh
end ContinuousSmoothFamilyOn
variable {P E M : Type*} [TopologicalSpace P]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ,E) ∞ M] [T2Space M]
attribute [local instance] OAI.YauCounterexamples.compactSmoothContinuityInst1
attribute [local instance] OAI.YauCounterexamples.compactSmoothContinuityInst2
attribute [local instance] OAI.YauCounterexamples.compactSmoothContinuityInst3
attribute [local instance] OAI.YauCounterexamples.compactSmoothContinuityInst4
omit [T2Space M] in
lemma continuous_chartTensorOfMetric (g₀ : SmoothMetric E M) (p : M) (K : Compacts E)
    (ht : (chartAt E p).target = univ) (q : P → SmoothMetric E M)
    (he : ∀ a x, x ∉ (chartAt E p).symm '' (K : Set E) → (q a).inner x=g₀.inner x)
    (hq : ∀ i j, ContinuousSmoothFamilyOn (fun a y => metricCoefficients (q a) p y i j) univ) :
    Continuous (fun a => chartTensorOfMetric g₀ p K ht (q a) (he a)) := by
  apply continuous_compactSmooth_of_jets
  have hf : ContinuousSmoothFamilyOn (fun a y => metricCoefficients (q a) p y) univ :=
    ContinuousSmoothFamilyOn.pi (fun i => ContinuousSmoothFamilyOn.pi (hq i))
  have hfm := hf.postcomp (metricMatrixFormCLM (E:=E)) (fun _ _ _ => (metricMatrixFormCLM (E:=E)).contDiff.contDiffAt)
  have hfb : ContinuousSmoothFamilyOn (fun (_ : P) y => chartMetricForm g₀ p y) univ :=
    ContinuousSmoothFamilyOn.const (P:=P) (chartMetricForm g₀ p) (fun y _ =>
    (chartMetricForm_contDiffOn g₀ p).contDiffAt (ht ▸ univ_mem))
  intro n
  change Continuous (fun z : P × E => iteratedFDeriv ℝ n
    (fun y => chartMetricForm (q z.1) p y-chartMetricForm g₀ p y) z.2)
  simpa only [univ_prod_univ,continuousOn_univ,chartMetricForm,metricMatrixFormCLM_apply] using (hfm.sub hfb).jets n

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
-- module Solutions.OAIQ070_YAU.SmoothYau_Smoothness_IteratedFDerivCompClm
attribute [-instance] _root_.OAI.YauCounterexamples.circle_dimension_fact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set Filter NormedSpace
open scoped Topology
open Set Filter
open scoped Topology ContDiff
namespace YauCounterexamples
variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
lemma iteratedFDeriv_comp_clm_at (L : F →L[ℝ] E) {f : E → G} {x : F} (n : ℕ)
    (hf : ContDiffAt ℝ n f (L x)) :
    iteratedFDeriv ℝ n (f ∘ L) x =
      (iteratedFDeriv ℝ n f (L x)).compContinuousLinearMap (fun _ => L) := by
  obtain ⟨U,hU,hu⟩ := hf.contDiffOn le_rfl (by simp)
  obtain ⟨V,hVU,hVo,hx⟩ := mem_nhds_iff.mp hU
  have he := L.iteratedFDerivWithin_comp_right (hu.mono hVU) hVo.uniqueDiffOn
    (hVo.preimage L.continuous).uniqueDiffOn hx (le_refl (n : WithTop ℕ∞))
  rw [iteratedFDerivWithin_of_isOpen n hVo hx,
    iteratedFDerivWithin_of_isOpen n (hVo.preimage L.continuous) hx] at he
  exact he

lemma partial_iteratedFDeriv (f : ℝ × E → F) (t : ℝ) (x : E) (n : ℕ)
    (hf : ContDiffAt ℝ n f (t,x)) :
    iteratedFDeriv ℝ n (fun y => f (t,y)) x =
      (iteratedFDeriv ℝ n f (t,x)).compContinuousLinearMap
        (fun _ => ContinuousLinearMap.inr ℝ ℝ E) := by
  let L := ContinuousLinearMap.inr ℝ ℝ E
  let q : ℝ × E → F := fun z => f ((t,0)+z)
  have hq : ContDiffAt ℝ n q (L x) := by
    have hg : ContDiffAt ℝ n (fun z : ℝ × E => (t,0)+z) (L x) := by fun_prop
    exact (show ContDiffAt ℝ n f ((t,0)+L x) by simpa [L] using hf).comp (L x) hg
  have hj := iteratedFDeriv_comp_clm_at L n hq
  simpa [q,L,Function.comp_def,iteratedFDeriv_comp_add_left] using hj

lemma continuousAt_partial_iteratedFDeriv (f : ℝ × E → F) {z : ℝ × E} (n : ℕ)
    (hf : ContDiffAt ℝ ∞ f z) :
    ContinuousAt (fun w : ℝ × E => iteratedFDeriv ℝ n (fun y => f (w.1,y)) w.2) z := by
  have hc := (ContinuousMultilinearMap.continuous_precomp
    (fun _ : Fin n => ContinuousLinearMap.inr ℝ ℝ E)).continuousAt.comp
      (hf.continuousAt_iteratedFDeriv (k := n) (ENat.natCast_le_of_coe_top_le_withTop le_rfl n))
  apply hc.congr_of_eventuallyEq
  filter_upwards [(hf.of_le (show (n : WithTop ℕ∞) ≤ ∞ from ENat.natCast_le_of_coe_top_le_withTop le_rfl n)).eventually (by simp)] with w hw
  exact partial_iteratedFDeriv f w.1 w.2 n hw

end YauCounterexamples

end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Geometry_PinnedMetricJointGradientPair
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
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set Filter NormedSpace
open scoped Topology
open Set Filter Manifold Bundle
open scoped Topology ContDiff
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ,E) ∞ M]

lemma pinnedMetric_inner (g : SmoothMetric E M)
    (K : ∀ x : M, TangentSpace 𝓘(ℝ,E) x →L[ℝ] TangentSpace 𝓘(ℝ,E) x)
    (hK : ContMDiff 𝓘(ℝ,E) ((𝓘(ℝ,E)).prod 𝓘(ℝ,E →L[ℝ] E)) ∞
      (fun x => TotalSpace.mk' (E →L[ℝ] E) x (K x))) (t : ℝ)
    (x : M) (v w : TangentSpace 𝓘(ℝ,E) x) :
    (pinnedMetric g K hK t).inner x v w =
      g.inner x ((NormedSpace.exp ((-t/2) • (show E →L[ℝ] E from K x))) v)
        ((NormedSpace.exp ((-t/2) • (show E →L[ℝ] E from K x))) w) := rfl

lemma pinnedMetric_unchanged (g : SmoothMetric E M)
    (K : ∀ x : M, TangentSpace 𝓘(ℝ,E) x →L[ℝ] TangentSpace 𝓘(ℝ,E) x)
    (hK : ContMDiff 𝓘(ℝ,E) ((𝓘(ℝ,E)).prod 𝓘(ℝ,E →L[ℝ] E)) ∞
      (fun x => TotalSpace.mk' (E →L[ℝ] E) x (K x))) (t : ℝ) (x : M) (hx : K x = 0) :
    (pinnedMetric g K hK t).inner x = g.inner x := by
  ext v w
  rw [pinnedMetric_inner,hx]
  change g.inner x ((NormedSpace.exp ((-t/2) • (0 : E →L[ℝ] E))) (show E from v))
    ((NormedSpace.exp ((-t/2) • (0 : E →L[ℝ] E))) (show E from w)) = _
  rw [smul_zero, NormedSpace.exp_zero]
  rfl


end


open Set Filter Function Manifold Bundle MeasureTheory
open scoped Topology ContDiff Matrix BoundedContinuousFunction

end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Spectrum_PinnedMetricContinuousSmoothFamily
attribute [-instance] _root_.OAI.YauCounterexamples.MetricIntegralAtlas.volumeMeasure_finite _root_.OAI.YauCounterexamples.MetricIntegralAtlas.volumeMeasure_openPos _root_.OAI.YauCounterexamples.circle_dimension_fact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Function Manifold Bundle
open scoped Topology ContDiff
namespace YauCounterexamples
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ,E) ∞ M]
lemma pinnedMetric_continuousSmoothFamily (g : SmoothMetric E M)
    {u : M → ℝ} {U : Set M} (K : pinningTensorSpace g u U)
    (p : M) (i j : CoordIndex E) :
    ContinuousSmoothFamilyOn
      (fun t y => metricCoefficients (pinnedMetric g K.val K.property.1 t) p y i j)
      (chartAt E p).target := by
  refine ⟨?_,fun n z hz => ?_⟩
  · intro t y hy
    exact (contDiffOn_metricCoefficient (pinnedMetric g K.val K.property.1 t) p i j).contDiffAt
      ((chartAt E p).open_target.mem_nhds hy)
  · exact (continuousAt_partial_iteratedFDeriv _ n
      (pinnedMetric_joint_coefficients g K.val K.property.1 p i j z.1 hz.2)).continuousWithinAt
lemma pinnedMetric_preserves_eigenfunction (g : SmoothMetric E M)
    {u : M → ℝ} {U : Set M} (K : pinningTensorSpace g u U)
    (hu : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ u) {lam : ℝ}
    (he : ∀ x, -laplaceBeltrami g u x=lam*u x) (t : ℝ) :
    ∀ x, -laplaceBeltrami (pinnedMetric g K.val K.property.1 t) u x=lam*u x := by
  intro x
  rw [pinnedMetric_laplacian g K.val K.property.1 K.property.2.1 K.property.2.2.1 hu K.property.2.2.2.1]
  exact he x
lemma pinnedMetric_exterior (g : SmoothMetric E M)
    {u : M → ℝ} {U : Set M} (K : pinningTensorSpace g u U) (t : ℝ)
    (x : M) (hx : x ∉ U) : (pinnedMetric g K.val K.property.1 t).inner x=g.inner x :=
  pinnedMetric_unchanged g K.val K.property.1 t x (K.property.2.2.2.2 x hx)
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
open Set Filter Function Manifold Bundle
open scoped Topology ContDiff BoundedContinuousFunction
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [CompactSpace M] [T2Space M]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompactSpace M] [T2Space M] in
lemma smoothMetric_eq_of_inner_eq (g h : SmoothMetric E M) (he : g.inner = h.inner) : g = h := by
  cases g
  cases h
  cases he
  rfl

omit [MeasurableSpace E] [BorelSpace E] [CompactSpace M] [T2Space M] in
lemma pinnedMetric_at_zero (g : SmoothMetric E M)
    (K : ∀ x : M, TangentSpace 𝓘(ℝ,E) x →L[ℝ] TangentSpace 𝓘(ℝ,E) x)
    (hK : ContMDiff 𝓘(ℝ,E) (𝓘(ℝ,E).prod 𝓘(ℝ,E →L[ℝ] E)) ∞
      (fun x => TotalSpace.mk' (E →L[ℝ] E) x (K x))) : pinnedMetric g K hK 0 = g := by
  have hh : (pinnedMetric g K hK 0).inner = g.inner := by
    funext x
    ext a b
    simp only [pinnedMetric_inner, neg_zero, zero_div]
    erw [zero_smul, NormedSpace.exp_zero]
    rfl
  exact smoothMetric_eq_of_inner_eq _ _ hh

end


open Set Filter Function Manifold Bundle
open scoped Topology ContDiff BoundedContinuousFunction

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
open scoped Topology ContDiff Distributions
lemma sphericalRadius_sq_planar (q : Sphere 3) :
    (sphericalRadius sourceAxisOne sourceAxisTwo q)^2 =
      Complex.normSq (planarLinear sourceAxisOne sourceAxisTwo q) := by
  rw [sphericalRadius_sq]
  simp [planarLinear,Complex.normSq_apply,pow_two]
end


open Set Filter Function Manifold Bundle TopologicalSpace BoxIntegral
open scoped Topology ContDiff Distributions ENNReal NNReal
local instance sphericalPinFormNorm_ra4fc41_1 : NormedAddCommGroup (MetricForm (Euclidean 3)) := inferInstanceAs (NormedAddCommGroup (Euclidean 3 →L[ℝ] Euclidean 3 →L[ℝ] ℝ))
local instance sphericalPinFormSpace_ra4fc41_1 : NormedSpace ℝ (MetricForm (Euclidean 3)) := inferInstanceAs (NormedSpace ℝ (Euclidean 3 →L[ℝ] Euclidean 3 →L[ℝ] ℝ))
theorem spherical_pin_near_oai
    (g₀ : SmoothMetric (Euclidean 3) (Sphere 3)) (hg₀ : IsRound g₀)
    (g : SmoothMetric (Euclidean 3) (Sphere 3)) {b c : ℝ}
    (hb0 : 0<b) (hbc : b < c) (hc : c<3/10)
    (hext : sphericalExterior g₀ g b) (k : ℕ) (hk3 : 3≤k)
    (u : Sphere 3 → ℝ) (hu : ContMDiff 𝓘(ℝ,Euclidean 3) 𝓘(ℝ,ℝ) ∞ u) (hu0 : u≠0)
    (hue : ∀ q, -laplaceBeltrami g u q=sphereFrequency k*u q)
    (hout : ∀ q, b < sphericalRadius sourceAxisOne sourceAxisTwo q → u q=roundPower sourceAxisOne sourceAxisTwo k q)
    (U : Set SphericalTensor) (hU : IsOpen U)
    (hgU : sphericalTensorOf g₀ g (sphericalExterior_mono (hbc.trans hc).le hext) ∈ U) :
    ∃ h : SmoothMetric (Euclidean 3) (Sphere 3), ∃ he : sphericalExterior g₀ h c,
      sphericalTensorOf g₀ h (sphericalExterior_mono hc.le he) ∈ U ∧
      (∀ q, -laplaceBeltrami h u q=sphereFrequency k*u q) ∧
      SphericalSimple h u (sphereFrequency k) := by
  classical
  have hc0 : 0 < c := hb0.trans hbc
  let I := (nonempty_metricIntegralAtlas (E:=Euclidean 3) (M:=Sphere 3)).some
  let caxis : Euclidean 4 := EuclideanSpace.single 2 1
  have haxis : inner ℝ caxis caxis=1 ∧ inner ℝ sourceAxisOne caxis=0 ∧
      inner ℝ sourceAxisTwo caxis=0 := by
    norm_num [caxis,sourceAxisOne,sourceAxisTwo,EuclideanSpace.inner_single_left,PiLp.single_apply]
    all_goals (try exact ⟨by decide, by decide⟩)
  have hbl : 0 < b^2 := sq_pos_of_pos hb0
  have hblc : b^2 < c^2 := by nlinarith
  have hc1 : c^2<1 := by nlinarith
  obtain ⟨K,hKsimple⟩ := exists_annular_simple_pinned_family I g sourceAxisOne sourceAxisTwo caxis
    source_axes_orthonormal.1 source_axes_orthonormal.2.1 haxis.1
    source_axes_orthonormal.2.2 haxis.2.1 haxis.2.2 k (by omega) hbl hblc hc1
    ⟨u,hu⟩ hu0 hue
    (fun q hq _ => hout q (by rw [← sphericalRadius_sq_planar] at hq; nlinarith [sphericalRadius_nonneg sourceAxisOne sourceAxisTwo q]))
    (fun q hq _ X Y => by
      have hqb : b < sphericalRadius sourceAxisOne sourceAxisTwo q := by
        rw [← sphericalRadius_sq_planar] at hq
        nlinarith [sphericalRadius_nonneg sourceAxisOne sourceAxisTwo q]
      exact (congrArg (fun T => T X Y) (hext q hqb)).trans (hg₀ q X Y))
  let qp (z : ℝ) := pinnedMetric g K.val K.property.1 z
  have heqp (z : ℝ) : sphericalExterior g₀ (qp z) c := by
    intro q hq
    have hn : q ∉ {p : Sphere 3 | b^2 < Complex.normSq (planarLinear sourceAxisOne sourceAxisTwo p) ∧
        Complex.normSq (planarLinear sourceAxisOne sourceAxisTwo p) < c^2} := by
      intro hh
      change b^2 < Complex.normSq (planarLinear sourceAxisOne sourceAxisTwo q) ∧
        Complex.normSq (planarLinear sourceAxisOne sourceAxisTwo q) < c^2 at hh
      rw [← sphericalRadius_sq_planar] at hh
      nlinarith [hh.2]
    exact (pinnedMetric_exterior g K z q hn).trans (hext q (hbc.trans hq))
  let eqp (z : ℝ) := sphericalExterior_support hc.le (heqp z)
  have hcont : Continuous (fun z => chartTensorOfMetric g₀ sourcePole sphericalTensorSupport
      (sphere_chart_target sourcePole) (qp z) (eqp z)) := by
    apply continuous_chartTensorOfMetric
    intro i j
    simpa only [sphere_chart_target] using pinnedMetric_continuousSmoothFamily g K sourcePole i j
  have hzero : qp 0=g := pinnedMetric_at_zero g K.val K.property.1
  have hmem : ∀ᶠ z in 𝓝 (0:ℝ), chartTensorOfMetric g₀ sourcePole sphericalTensorSupport
      (sphere_chart_target sourcePole) (qp z) (eqp z) ∈ U :=
    hcont.continuousAt.eventually (hU.mem_nhds (by simpa only [hzero,sphericalTensorOf] using hgU))
  obtain ⟨z,hzU,hzs⟩ := ((hmem.filter_mono nhdsWithin_le_nhds).and hKsimple).exists
  refine ⟨qp z,heqp z,hzU,?_,hzs⟩
  exact pinnedMetric_preserves_eigenfunction g K hu hue z

end YauCounterexamples
end

end OAI
end

theorem solution : type_of% @OAI.YauCounterexamples.spherical_pin_near_oai := @OAI.YauCounterexamples.spherical_pin_near_oai
