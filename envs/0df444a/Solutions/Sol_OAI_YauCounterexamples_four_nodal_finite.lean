-- Prove2me | solution 1 for OAI.YauCounterexamples.four_nodal_finite
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T12:33:10.741781+00:00
-- url     : https://prove2.me/submissions/33bc7124-a458-43be-8001-18e5aa09d18b

import Mathlib
import Definitions.Def_SmoothYau
import Definitions.Def_OAIQ070A007
import Definitions.Def_OAIQ070A008

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Geometry_InverseChartIntrinsicLipschitz
attribute [-instance] _root_.OAI.YauCounterexamples.circle_dimension_fact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Metric Manifold MeasureTheory Bundle
open scoped Topology ContDiff NNReal ENNReal
namespace YauCounterexamples
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) 1 M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,E) x)]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace 𝓘(ℝ,E) x)]
attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace normedSpaceTangentSpaceVectorSpace

lemma inverse_chart_intrinsic_lipschitz (p : M) :
    ∃ r > (0 : ℝ), ∃ C : ℝ≥0, 0 < C ∧
      ball (extChartAt 𝓘(ℝ,E) p p) r ⊆ (extChartAt 𝓘(ℝ,E) p).target ∧
      ∀ y ∈ ball (extChartAt 𝓘(ℝ,E) p p) r, ∀ z ∈ ball (extChartAt 𝓘(ℝ,E) p p) r,
        riemannianEDist 𝓘(ℝ,E) ((extChartAt 𝓘(ℝ,E) p).symm y) ((extChartAt 𝓘(ℝ,E) p).symm z)
          ≤ C * edist y z := by
  let c := extChartAt 𝓘(ℝ,E) p
  let d (y : E) : E →L[ℝ] TangentSpace 𝓘(ℝ,E) (c.symm y) :=
    mfderiv[Set.range 𝓘(ℝ,E)] c.symm y
  obtain ⟨C,hCpos,hC⟩ := eventually_enorm_mfderivWithin_symm_extChartAt_lt 𝓘(ℝ,E) p
  obtain ⟨r,hr,hrsub'⟩ : ∃ r > 0, ball (c p) r ∩ range 𝓘(ℝ,E) ⊆
      c.target ∩ {y | ‖d y‖ₑ < C} :=
    mem_nhdsWithin_iff.mp (inter_mem (extChartAt_target_mem_nhdsWithin p) hC)
  have hrsub : ball (c p) r ⊆ c.target ∩ {y | ‖d y‖ₑ < C} := by
    simpa using hrsub'
  refine ⟨r,hr,C,hCpos,fun y hy => (hrsub hy).1,?_⟩
  intro y hy z hz
  let η := ContinuousAffineMap.lineMap (R := ℝ) y z
  let γ := c.symm ∘ η
  have hη : Icc 0 1 ⊆ η ⁻¹' (c.target ∩ {w | ‖d w‖ₑ < C}) := by
    simp only [← image_subset_iff, ContinuousAffineMap.coe_lineMap_eq, ← segment_eq_image_lineMap, η]
    exact ((convex_ball _ _).segment_subset hy hz).trans hrsub
  simp only [preimage_inter, subset_inter_iff] at hη
  have hηs : ContMDiffOn 𝓘(ℝ,ℝ) 𝓘(ℝ,E) 1 η (Icc 0 1) := by
    apply ContMDiff.contMDiffOn
    rw [contMDiff_iff_contDiff]
    exact ContinuousAffineMap.contDiff _
  have hdist : riemannianEDist 𝓘(ℝ,E) (c.symm y) (c.symm z) ≤ pathELength 𝓘(ℝ,E) γ 0 1 := by
    apply riemannianEDist_le_pathELength _ _ _ zero_le_one
    · exact (contMDiffOn_extChartAt_symm p).comp hηs hη.1
    · simp [γ,η,ContinuousAffineMap.coe_lineMap_eq]
    · simp [γ,η,ContinuousAffineMap.coe_lineMap_eq]
  apply hdist.trans
  rw [← lintegral_fderiv_lineMap_eq_edist, pathELength_eq_lintegral_mfderivWithin_Icc,
    ← lintegral_const_mul' _ _ ENNReal.coe_ne_top]
  apply setLIntegral_mono' measurableSet_Icc (fun t ht => ?_)
  have hc : mfderiv[Icc 0 1] γ t =
      (mfderiv[Set.range 𝓘(ℝ,E)] c.symm (η t)).comp (mfderiv[Icc 0 1] η t) := by
    apply mfderivWithin_comp
    · exact mdifferentiableWithinAt_extChartAt_symm (hη.1 ht)
    · exact hηs.mdifferentiableOn one_ne_zero t ht
    · exact hη.1.trans (preimage_mono (extChartAt_target_subset_range p))
    · rw [uniqueMDiffWithinAt_iff_uniqueDiffWithinAt]
      exact uniqueDiffOn_Icc zero_lt_one t ht
  have hcv : mfderiv[Icc 0 1] γ t 1 =
      (mfderiv[Set.range 𝓘(ℝ,E)] c.symm (η t)) (mfderiv[Icc 0 1] η t 1) := congr($hc 1)
  rw [hcv]
  apply (ContinuousLinearMap.le_opENorm _ _).trans
  gcongr
  · exact (hη.2 ht).le
  · simp only [mfderivWithin_eq_fderivWithin]
    exact le_of_eq rfl
end YauCounterexamples

end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_NodalMeasure_CompactRegularLevelIntrinsicFinite
attribute [-instance] _root_.OAI.YauCounterexamples.circle_dimension_fact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples



section
open Set Filter Function Metric MeasureTheory
open scoped Topology ContDiff NNReal ENNReal
variable {E N : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [EMetricSpace N] [MeasurableSpace N] [BorelSpace N]

theorem regular_level_local_finite {f : E → ℝ} {x : E}
    (hf : ContDiffAt ℝ 1 f x) (hd : fderiv ℝ f x ≠ 0)
    {φ : E → N} {B : Set E} (hB : B ∈ 𝓝 x) {C : ℝ≥0}
    (hφ : LipschitzOnWith C φ B) :
    ∃ O ∈ 𝓝 x, Measure.hausdorffMeasure (Module.finrank ℝ E - 1 : ℕ)
      (φ '' {y | y ∈ O ∧ f y = f x}) < (∞ : ℝ≥0∞) := by
  let L := fderiv ℝ f x
  have hL : L.range = ⊤ := by
    apply LinearMap.range_eq_top.mpr
    apply surjective_of_nonzero_of_finrank_eq_one (K := ℝ) (f := L.toLinearMap) (by simp)
    intro hh
    apply hd
    ext y
    exact DFunLike.congr_fun hh y
  have hs : HasStrictFDerivAt f L x := hf.hasStrictFDerivAt one_ne_zero
  let e := hs.implicitToOpenPartialHomeomorph f L hL
  let g := hs.implicitFunction f L hL (f x)
  have hdx : HasStrictFDerivAt g L.ker.subtypeL 0 := hs.to_implicitFunction hL
  have hg0 : g 0 = x := hs.implicitFunction_apply_image hL
  obtain ⟨K,V,hV,hgV⟩ := hdx.exists_lipschitzOnWith
  have hN : V ∩ g ⁻¹' B ∈ 𝓝 (0 : L.ker) :=
    inter_mem hV (hdx.continuousAt.tendsto (hg0 ▸ hB))
  obtain ⟨r,hr,hrsub⟩ := Metric.mem_nhds_iff.mp hN
  let S := ball (0 : L.ker) r
  have hSg : MapsTo g S B := fun y hy => (hrsub hy).2
  have hgS : LipschitzOnWith K g S := hgV.mono (fun y hy => (hrsub hy).1)
  have he : x ∈ e.source := hs.mem_implicitToOpenPartialHomeomorph_source hL
  have he0 : e x = (f x,0) := hs.implicitToOpenPartialHomeomorph_self hL
  have hpre : e ⁻¹' (Set.univ ×ˢ S) ∈ 𝓝 x := by
    apply (e.continuousAt he).tendsto
    rw [he0]
    exact IsOpen.mem_nhds (isOpen_univ.prod isOpen_ball) ⟨mem_univ _,mem_ball_self hr⟩
  let O := e.source ∩ e ⁻¹' (Set.univ ×ˢ S)
  have hO : O ∈ 𝓝 x := inter_mem (e.open_source.mem_nhds he) hpre
  refine ⟨O,hO,?_⟩
  have hsub : φ '' {y | y ∈ O ∧ f y = f x} ⊆ (φ ∘ g) '' S := by
    rintro _ ⟨y,hy,rfl⟩
    refine ⟨(e y).2,hy.1.2.2,?_⟩
    change φ (g (e y).2) = φ y
    congr 1
    change e.symm (f x,(e y).2) = y
    rw [← hy.2]
    change e.symm (e y) = y
    exact e.left_inv hy.1.1
  have hdim : Module.finrank ℝ L.ker = Module.finrank ℝ E - 1 := by
    have hh := LinearMap.finrank_range_add_finrank_ker L.toLinearMap
    rw [hL] at hh
    simp only [finrank_top, Module.finrank_self] at hh
    omega
  let : MeasurableSpace L.ker := borel L.ker
  let : BorelSpace L.ker := ⟨rfl⟩
  have hfinite : Measure.hausdorffMeasure (Module.finrank ℝ E - 1 : ℕ) S < (∞ : ℝ≥0∞) := by
    rw [← hdim]
    exact lt_of_le_of_lt (measure_mono ball_subset_closedBall) (isCompact_closedBall (0 : L.ker) r).measure_lt_top
  apply lt_of_le_of_lt (measure_mono hsub)
  apply lt_of_le_of_lt ((hφ.comp hgS hSg).hausdorffMeasure_image_le (by positivity))
  rw [ENNReal.rpow_natCast]
  exact ENNReal.mul_lt_top (ENNReal.pow_lt_top ENNReal.coe_lt_top) hfinite

end



open Set Filter Metric Manifold MeasureTheory Bundle
open scoped Topology ContDiff NNReal ENNReal
open Set Filter Function Metric MeasureTheory
open scoped Topology ContDiff NNReal ENNReal
open Set Filter Function Metric Manifold Bundle MeasureTheory
open scoped Topology ContDiff NNReal ENNReal
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [EMetricSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,E) x)]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace 𝓘(ℝ,E) x)]
  [IsRiemannianManifold 𝓘(ℝ,E) M] [MeasurableSpace M] [BorelSpace M]
attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace normedSpaceTangentSpaceVectorSpace

theorem compact_regular_level_intrinsic_finite {u : M → ℝ}
    (hu : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ u) {K : Set M} (hK : IsCompact K)
    (hreg : ∀ x ∈ K, u x = 0 →
      fderiv ℝ (u ∘ (chartAt E x).symm) (chartAt E x x) ≠ 0) :
    Measure.hausdorffMeasure (Module.finrank ℝ E - 1 : ℕ) (K ∩ {x | u x = 0}) < (∞ : ℝ≥0∞) := by
  let Z := K ∩ {x | u x = 0}
  have hZ : IsCompact Z := hK.inter_right (isClosed_eq hu.continuous continuous_const)
  apply hZ.measure_lt_top_of_nhdsWithin
  intro x hx
  let c := chartAt E x
  have hxs : x ∈ c.source := mem_chart_source E x
  have hxt : c x ∈ c.target := c.map_source hxs
  have hcU : ContDiffAt ℝ 1 (u ∘ c.symm) (c x) := by
    apply (contMDiffAt_iff_contDiffAt.mp ((hu (c.symm (c x))).comp (c x)
      (contMDiffAt_symm_of_mem_maximalAtlas (IsManifold.chart_mem_maximalAtlas x) hxt))).of_le
    exact ENat.natCast_le_of_coe_top_le_withTop le_rfl 1
  obtain ⟨r,hr,C,_,_,hCL⟩ := inverse_chart_intrinsic_lipschitz (E := E) x
  have hCL' : LipschitzOnWith C c.symm (ball (c x) r) := by
    intro y hy z hz
    rw [IsRiemannianManifold.out (I := 𝓘(ℝ,E))]
    exact hCL y hy z hz
  obtain ⟨O,hO,hfin⟩ := regular_level_local_finite hcU (hreg x hx.1 hx.2)
    (ball_mem_nhds (c x) hr) hCL'
  let V := c.source ∩ c ⁻¹' O
  have hV : V ∈ 𝓝 x := inter_mem (c.open_source.mem_nhds hxs) ((c.continuousAt hxs).tendsto hO)
  refine ⟨V ∩ Z, by simpa only [inter_comm] using inter_mem_nhdsWithin Z hV, ?_⟩
  apply lt_of_le_of_lt (measure_mono ?_) hfin
  intro y hy
  refine ⟨c y,⟨hy.1.2,?_⟩,c.left_inv hy.1.1⟩
  simp only [Function.comp_apply, c.left_inv hy.1.1, c.left_inv hxs]
  exact hy.2.2.trans hx.2.symm


end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_ProductMetric_FourWaveThreeSmul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples
section
open Set Filter Manifold Bundle Function Matrix
open scoped Topology ContDiff Matrix.Norms.Elementwise
lemma four_chart_symm_three (p : FourManifold) (y : FourModel) :
    fourToThree ((chartAt FourModel p).symm y)=
      (chartAt ThreeModel (fourToThree p)).symm (fourProjThree y) := by rfl
lemma four_chart_three (p q : FourManifold) :
    fourProjThree (chartAt FourModel p q)=chartAt ThreeModel (fourToThree p) (fourToThree q) := by rfl
end


section
open Set Filter Manifold Bundle Function Matrix
open scoped Topology ContDiff Matrix.Norms.Elementwise
local instance fourLapThreeSmul : ContinuousSMul ℝ ThreeModel := IsBoundedSMul.continuousSMul
local instance fourLapFourSmul : ContinuousSMul ℝ FourModel := IsBoundedSMul.continuousSMul
lemma four_lift_regular (u : ThreeManifold → ℝ)
    (hu : ContMDiff 𝓘(ℝ,ThreeModel) 𝓘(ℝ,ℝ) ∞ u) (hr : ThreeRegular u) :
    ∀ p, (u ∘ fourToThree) p=0 →
      fderiv ℝ ((u ∘ fourToThree) ∘ (chartAt FourModel p).symm) (chartAt FourModel p p)≠0 := by
  intro p hp hh
  apply hr (fourToThree p) hp
  have hs : ContMDiff 𝓘(ℝ,ThreeModel) 𝓘(ℝ,ThreeModel) ∞ (chartAt ThreeModel (fourToThree p)).symm := by
    have h := contMDiffOn_chart_symm (I:=𝓘(ℝ,ThreeModel)) (n:=∞) (x:=fourToThree p)
    rwa [three_chart_target,contMDiffOn_univ] at h
  have hfun : (u ∘ fourToThree) ∘ (chartAt FourModel p).symm =
      (u ∘ (chartAt ThreeModel (fourToThree p)).symm) ∘ fourProjThree := by
    funext y
    simp only [Function.comp_apply,four_chart_symm_three]
  rw [hfun,fderiv_comp _ ((contMDiff_iff_contDiff.mp (hu.comp hs)).differentiable (by simp) _)
    fourProjThree.differentiableAt,fourProjThree.fderiv,four_chart_three] at hh
  apply ContinuousLinearMap.ext
  intro v
  have h := congrArg (fun L : FourModel →L[ℝ] ℝ => L (fourSplitEquiv.symm (v,0))) hh
  change fderiv ℝ (u ∘ (chartAt ThreeModel (fourToThree p)).symm)
    (chartAt ThreeModel (fourToThree p) (fourToThree p))
    (fourProjThree (fourSplitEquiv.symm (v,0))) = (0:ℝ) at h
  have hv : fourProjThree (fourSplitEquiv.symm (v,0))=v := by
    change (fourSplitEquiv (fourSplitEquiv.symm (v,0))).1=v
    rw [ContinuousLinearEquiv.apply_symm_apply]
  rw [hv] at h
  exact h
end


open Set Filter Manifold Bundle Function Matrix BoxIntegral MeasureTheory
open scoped Topology ContDiff Matrix.Norms.Elementwise ENNReal NNReal

end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_ProductMetric_SphereProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Function Manifold Bundle TopologicalSpace BoxIntegral MeasureTheory
open scoped Topology ContDiff Distributions ENNReal NNReal
namespace YauCounterexamples
lemma four_nodal_finite_oai (g : SmoothMetric FourModel FourManifold)
    (u : ThreeManifold → ℝ) (hu : ContMDiff 𝓘(ℝ,ThreeModel) 𝓘(ℝ,ℝ) ∞ u)
    (hr : ThreeRegular u) : nodalMeasure g 3 (u ∘ fourToThree) ≠ (∞ : ℝ≥0∞) := by
  let : RiemannianBundle (fun x : FourManifold => TangentSpace 𝓘(ℝ,FourModel) x) := ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle FourModel (fun x : FourManifold => TangentSpace 𝓘(ℝ,FourModel) x) :=
    ⟨⟨g.inner,g.toContinuousRiemannianMetric.continuous,fun _ _ _ => rfl⟩⟩
  let : EMetricSpace FourManifold := EMetricSpace.ofRiemannianMetric 𝓘(ℝ,FourModel) FourManifold
  let : MeasurableSpace FourManifold := borel FourManifold
  let : BorelSpace FourManifold := ⟨rfl⟩
  have hh := compact_regular_level_intrinsic_finite (hu.comp fourToThree_smooth) (K:=univ) isCompact_univ
    (fun x _ => four_lift_regular u hu hr x)
  change Measure.hausdorffMeasure 3 {x | (u ∘ fourToThree) x=0}≠(∞ : ℝ≥0∞)
  apply ne_of_lt
  simpa [FourModel,Euclidean] using hh
end YauCounterexamples
end

end OAI
end

theorem solution : type_of% @OAI.YauCounterexamples.four_nodal_finite_oai := @OAI.YauCounterexamples.four_nodal_finite_oai
