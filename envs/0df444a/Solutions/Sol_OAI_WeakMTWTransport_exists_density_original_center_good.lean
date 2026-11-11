-- Prove2me | solution 1 for OAI.WeakMTWTransport.exists_density_original_center_good
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T19:26:47.641254+00:00
-- url     : https://prove2.me/submissions/332061bf-8670-45d3-9c45-b28fa2e120c7

import Mathlib
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Range
import Mathlib.Analysis.CStarAlgebra.GelfandNaimarkSegal
import Mathlib.Analysis.CStarAlgebra.Hom
import Mathlib.Analysis.Complex.Circle
import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Normed.Algebra.Spectrum
import Mathlib.Analysis.VonNeumannAlgebra.Basic
import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Combinatorics.Young.YoungDiagram
import Mathlib.Data.List.Nodup
import Mathlib.Geometry.Manifold.IsManifold.Basic
import Mathlib.GroupTheory.FreeGroup.Basic
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
import Mathlib.MeasureTheory.Function.AbsolutelyContinuous
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.MeasureTheory.Function.UniformIntegrable
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.MeasureTheory.MeasurableSpace.Embedding
import Mathlib.MeasureTheory.Measure.FiniteMeasure
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.Probability.Kernel.Composition.MeasureComp
import Mathlib.Probability.Kernel.CondDistrib
import Mathlib.Probability.Kernel.Defs
import Mathlib.Probability.Kernel.WithDensity
import Mathlib.Topology.Algebra.LinearMapCompletion
import Definitions.Def_BiholderTransport
import Definitions.Def_OAIQ232A026
import Theorems.Thm_OAI_WeakMTWTransport_cTransform_ae_active_before_cut
import Theorems.Thm_OAI_WeakMTWTransport_cTransform_ae_normal_quadraticExpansion
import Theorems.Thm_OAI_WeakMTWTransport_exists_uniform_intrinsic_contact_bounds

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Regularity_MetricDefinitions
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory Manifold Bundle
open scoped ContDiff Manifold ENNReal NNReal Topology

namespace WeakMTWTransport
open Matrix
open scoped MatrixOrder

variable {M : Type*} [MetricSpace M]

variable [CompactSpace M] [Nonempty M]

omit [CompactSpace M] [Nonempty M] in
lemma contactGap_symm (u v : M → ℝ) (x y : M) :
    contactGap u v x y = contactGap v u y x := by
  dsimp [contactGap]
  rw [cost_symm x y]
  ring

end WeakMTWTransport
end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Contact_Subgradient
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set MeasureTheory Manifold Bundle
open scoped ContDiff Manifold ENNReal NNReal Topology

open Set Filter
open scoped Topology NNReal

namespace WeakMTWTransport
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

open MeasureTheory

lemma ae_of_locally_ae {X : Type*} [TopologicalSpace X] [SecondCountableTopology X]
    [MeasurableSpace X] (μ : Measure X) {s : Set X} {P : X → Prop}
    (hloc : ∀ x ∈ s, ∃ U : Set X, IsOpen U ∧ x ∈ U ∧
      (∀ᵐ z ∂μ, z ∈ U → P z)) :
    ∀ᵐ z ∂μ, z ∈ s → P z := by
  classical
  choose U hUo hxU hUae using fun x : s => hloc x x.2
  have hcov : s ⊆ ⋃ x : s, U x := by
    intro x hx
    exact mem_iUnion.mpr ⟨⟨x,hx⟩,hxU ⟨x,hx⟩⟩
  obtain ⟨c,hc,hcover⟩ := (IsLindelof.of_coe (s := s)).elim_countable_subcover U hUo hcov
  have hnull : μ (⋃ i ∈ c, {z | z ∈ U i ∧ ¬P z}) = 0 := by
    apply (measure_biUnion_null_iff hc).mpr
    intro i _
    simpa only [Classical.not_imp] using (ae_iff.mp (hUae i))
  apply ae_iff.mpr
  apply measure_mono_null _ hnull
  intro z hz
  have hz' : z ∈ s ∧ ¬P z := by simpa only [mem_ofPred_eq,Classical.not_imp] using hz
  obtain ⟨i,hi,hzi⟩ := mem_iUnion₂.mp (hcover hz'.1)
  exact mem_iUnion₂.mpr ⟨i,hi,hzi,hz'.2⟩

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Coordinates_ChartLipschitz
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.WeakMTWTransport.fixedJoinMiddle_apply _root_.OAI.WeakMTWTransport.normalEndpointMixedOperator_inner _root_.OAI.WeakMTWTransport.riemannianExp_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set Filter Manifold MeasureTheory Bundle Metric
open scoped Topology ContDiff ENNReal NNReal

namespace WeakMTWTransport
section ChartLipschitz
variable {n : ℕ} {M : Type*} [MetricSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace normedSpaceTangentSpaceVectorSpace

attribute [local instance] OAI.WeakMTWTransport.instNormedAddCommGroupContinuousLinearMapRealIdTangentSpaceModelModelWithCornersSelf
local instance instNormedSpaceRealContinuousLinearMapIdTangentSpaceModelModelWithCornersSelf_r076506_1 (y : Model n) (x : M) : NormedSpace ℝ
    (TangentSpace 𝓘(ℝ,Model n) y →L[ℝ] TangentSpace 𝓘(ℝ,Model n) x) :=
  ContinuousLinearMap.toNormedSpace
lemma exists_lipschitz_inverse_chart (x : M) :
    ∃ C : ℝ≥0, ∃ r>0, ball (extChartAt 𝓘(ℝ,Model n) x x) r ⊆ (extChartAt 𝓘(ℝ,Model n) x).target ∧
      LipschitzOnWith C (extChartAt 𝓘(ℝ,Model n) x).symm
        (ball (extChartAt 𝓘(ℝ,Model n) x x) r) := by
  let d := extChartAt 𝓘(ℝ,Model n) x
  have : IsContinuousRiemannianBundle (Model n) (fun z : M => TangentSpace 𝓘(ℝ,Model n) z) :=
    continuousRiemannianBundle_of_smooth (IB := 𝓘(ℝ,Model n))
  obtain ⟨C,hCpos,hC⟩ := eventually_enorm_mfderivWithin_symm_extChartAt_lt 𝓘(ℝ,Model n) x
  have hC' : ∀ᶠ y in 𝓝 (d x), ‖mfderiv 𝓘(ℝ,Model n) 𝓘(ℝ,Model n) d.symm y‖ₑ < C := by
    simpa only [ModelWithCorners.range_eq_univ,nhdsWithin_univ,mfderivWithin_univ] using hC
  have hdT : d.target∈𝓝 (d x) :=
    (isOpen_extChartAt_target x).mem_nhds (mem_extChartAt_target x)
  obtain ⟨r,hr,hboth⟩ := Metric.mem_nhds_iff.mp (inter_mem hdT hC')
  have htarget : ball (d x) r⊆d.target := fun y hy => (hboth hy).1
  have hbound : ∀ y∈ball (d x) r, ‖mfderiv 𝓘(ℝ,Model n) 𝓘(ℝ,Model n) d.symm y‖ₑ≤C :=
    fun y hy => (hboth hy).2.le
  refine ⟨C,r,hr,htarget,?_⟩
  intro u hu v hv
  let η := ContinuousAffineMap.lineMap (R := ℝ) u v
  let γ := d.symm ∘ η
  have hη : MapsTo η (Icc 0 1) (ball (d x) r) := by
    change Icc 0 1 ⊆ η ⁻¹' ball (d x) r
    rw [←image_subset_iff]
    simp only [η,ContinuousAffineMap.coe_lineMap_eq,←segment_eq_image_lineMap]
    exact (convex_ball _ _).segment_subset hu hv
  have hηT : MapsTo η (Icc 0 1) d.target := hη.mono_right htarget
  have η_smooth : ContMDiffOn 𝓘(ℝ,ℝ) 𝓘(ℝ,Model n) 1 η (Icc 0 1) :=
    (ContinuousAffineMap.contDiff η).contMDiff.contMDiffOn
  have hγ : ContMDiffOn 𝓘(ℝ,ℝ) 𝓘(ℝ,Model n) 1 γ (Icc 0 1) :=
    (contMDiffOn_extChartAt_symm (I := 𝓘(ℝ,Model n)) (n := (1:ℕ∞ω)) x).comp η_smooth hηT
  have H : riemannianEDist 𝓘(ℝ,Model n) (d.symm u) (d.symm v)≤pathELength 𝓘(ℝ,Model n) γ 0 1 := by
    apply riemannianEDist_le_pathELength _ _ _ zero_le_one
    · exact hγ
    · simp only [γ,Function.comp_apply,η,ContinuousAffineMap.coe_lineMap_eq,AffineMap.lineMap_apply_zero]
    · simp only [γ,Function.comp_apply,η,ContinuousAffineMap.coe_lineMap_eq,AffineMap.lineMap_apply_one]
  rw [←IsRiemannianManifold.out] at H
  apply H.trans
  rw [←lintegral_fderiv_lineMap_eq_edist, pathELength_eq_lintegral_mfderivWithin_Icc,
    ←lintegral_const_mul' _ _ ENNReal.coe_ne_top]
  apply setLIntegral_mono' measurableSet_Icc
  intro t ht
  have hD : mfderivWithin 𝓘(ℝ,ℝ) 𝓘(ℝ,Model n) γ (Icc 0 1) t =
      (mfderiv 𝓘(ℝ,Model n) 𝓘(ℝ,Model n) d.symm (η t)).comp (mfderivWithin 𝓘(ℝ,ℝ) 𝓘(ℝ,Model n) η (Icc 0 1) t) := by
    apply mfderiv_comp_mfderivWithin
    · exact (contMDiffWithinAt_extChartAt_symm_target (n := (1:ℕ∞ω)) x (hηT ht)).contMDiffAt
        ((isOpen_extChartAt_target x).mem_nhds (hηT ht)) |>.mdifferentiableAt (by norm_num : (1:ℕ∞ω)≠0)
    · exact η_smooth.mdifferentiableOn one_ne_zero t ht
    · rw [uniqueMDiffWithinAt_iff_uniqueDiffWithinAt]
      exact uniqueDiffOn_Icc zero_lt_one t ht
  rw [hD,ContinuousLinearMap.comp_apply]
  apply (ContinuousLinearMap.le_opENorm _ _).trans
  gcongr
  · exact hbound _ (hη ht)
  · simp only [mfderivWithin_eq_fderivWithin]
    exact le_rfl

end ChartLipschitz
end WeakMTWTransport

end

end

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Regularity_AERademacher
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.WeakMTWTransport.fixedJoinMiddle_apply _root_.OAI.WeakMTWTransport.normalEndpointMixedOperator_inner
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set Filter Manifold MeasureTheory Bundle Metric
open scoped Topology ContDiff ENNReal NNReal

namespace WeakMTWTransport
section AERademacher
variable {n : ℕ} {M : Type*} [MetricSpace M] [SecondCountableTopology M]
  [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma lipschitz_ae_mdifferentiableAt {f : M → ℝ} {K : ℝ≥0}
    (hf : LipschitzWith K f) :
    ∀ᵐ x ∂metricVolume (M := M) n, MDifferentiableAt 𝓘(ℝ,Model n) 𝓘(ℝ,ℝ) f x := by
  have hlocal : ∀ x∈(univ : Set M), ∃ U : Set M, IsOpen U ∧ x∈U ∧
      (∀ᵐ z ∂metricVolume (M := M) n, z∈U → MDifferentiableAt 𝓘(ℝ,Model n) 𝓘(ℝ,ℝ) f z) := by
    intro x _
    obtain ⟨C,r,hr,htarget,hLip⟩ := exists_lipschitz_inverse_chart (n := n) x
    let d := extChartAt 𝓘(ℝ,Model n) x
    let B := ball (d x) r
    let U := d.source ∩ d ⁻¹' B
    have hU : IsOpen U := (continuousOn_extChartAt x).isOpen_inter_preimage
      (isOpen_extChartAt_source x) isOpen_ball
    refine ⟨U,hU,⟨mem_extChartAt_source x,mem_ball_self hr⟩,?_⟩
    let μ : Measure (Model n) := Measure.hausdorffMeasure (n:ℝ)
    have hdim : Module.finrank ℝ (Model n)=n := by simp [Model]
    have : μ.IsAddHaarMeasure := by
      dsimp only [μ]
      rw [←hdim]
      first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)
    have hR := (hf.comp_lipschitzOnWith hLip).ae_differentiableWithinAt_of_mem (μ := μ)
    let N := {q : Model n | q∈B ∧ ¬DifferentiableAt ℝ (f ∘ d.symm) q}
    have hN : μ N=0 := by
      apply measure_mono_null _ (ae_iff.mp hR)
      intro q hq
      change ¬(q∈B → DifferentiableWithinAt ℝ (f ∘ d.symm) B q)
      intro hh
      exact hq.2 ((hh hq.1).differentiableAt (isOpen_ball.mem_nhds hq.1))
    have hNsub : N⊆B := fun _ h => h.1
    have hImage : (Measure.hausdorffMeasure (n:ℝ) : Measure M) (d.symm '' N)=0 := by
      apply le_antisymm _ (show (0:ℝ≥0∞)≤_ from zero_le)
      have H := (hLip.mono hNsub).hausdorffMeasure_image_le (d := (n:ℝ)) (by positivity)
      change _ ≤ (C : ℝ≥0∞)^(n:ℝ)*μ N at H
      simpa only [d,hN,mul_zero] using H
    have hImageVol : metricVolume (M := M) n (d.symm '' N)=0 := by
      simp only [metricVolume,Measure.smul_apply,smul_eq_mul,hImage,mul_zero]
    apply ae_iff.mpr
    apply measure_mono_null _ hImageVol
    intro z hz
    have hz' : z∈U ∧ ¬MDifferentiableAt 𝓘(ℝ,Model n) 𝓘(ℝ,ℝ) f z := by
      simpa only [mem_ofPred_eq,Classical.not_imp] using hz
    refine ⟨d z,⟨hz'.1.2,?_⟩,d.left_inv hz'.1.1⟩
    intro hD
    have hChart := mdifferentiableAt_extChartAt (I := 𝓘(ℝ,Model n))
      (show z∈(chartAt (Model n) x).source by simpa only [d,extChartAt_source] using hz'.1.1)
    have H := hD.hasFDerivAt.hasMFDerivAt.comp z hChart.hasMFDerivAt
    apply hz'.2
    apply (H.congr_of_eventuallyEq _).mdifferentiableAt
    filter_upwards [(isOpen_extChartAt_source x).mem_nhds hz'.1.1] with w hw
    change f w=f (d.symm (d w))
    rw [d.left_inv hw]
  simpa only [mem_univ,true_implies] using ae_of_locally_ae (metricVolume (M := M) n) hlocal

variable [CompactSpace M] [Nonempty M]
lemma cTransform_ae_mdifferentiableAt {v : M → ℝ} (hv : Continuous v) :
    ∀ᵐ x ∂metricVolume (M := M) n,
      MDifferentiableAt 𝓘(ℝ,Model n) 𝓘(ℝ,ℝ) (cTransform v) x := by
  exact lipschitz_ae_mdifferentiableAt (cTransform_lipschitz hv
    (D := ⟨Metric.diam (univ : Set M),Metric.diam_nonneg⟩) (fun x y =>
      Metric.dist_le_diam_of_mem isCompact_univ.isBounded (mem_univ x) (mem_univ y)))

end AERademacher
end WeakMTWTransport

end

end

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Contact_AEContacts
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.WeakMTWTransport.fixedJoinMiddle_apply _root_.OAI.WeakMTWTransport.normalEndpointMixedOperator_inner
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set Filter Manifold MeasureTheory Bundle Metric
open scoped Topology ContDiff ENNReal NNReal

namespace WeakMTWTransport
section AEContacts
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

omit [MeasurableSpace M] [BorelSpace M] in
lemma active_log_derivative {v : M → ℝ} (hv : Continuous v) {x : M}
    (hDiff : MDifferentiableAt 𝓘(ℝ,Model n) 𝓘(ℝ,ℝ) (cTransform v) x)
    {p : TangentSpace 𝓘(ℝ,Model n) x} (hp : p∈activeLogs (n := n) v x) :
    HasFDerivAt (fun h => cTransform v (riemannianExp x h)) (innerSL ℝ p) 0 := by
  have hID := contracted_minimizer_mem_injectivityDomain hp.1
    (show (0:ℝ)<1/2 by norm_num) (show (1/2:ℝ)<1 by norm_num)
  let f := fun h : TangentSpace 𝓘(ℝ,Model n) x =>
    (-2:ℝ)*(normalCost x ((1/2:ℝ) • p) h-normalCost x ((1/2:ℝ) • p) 0)
  have hD : HasFDerivAt f (innerSL ℝ p) 0 := by
    apply (((normalCost_hasFDerivAt_zero hID).sub_const
      (normalCost x ((1/2:ℝ) • p) 0)).const_smul (-2:ℝ)).congr_fderiv
    ext h
    simp only [smul_apply,innerSL_apply_apply,inner_neg_left,real_inner_smul_left,smul_eq_mul]
    ring
  have hU : DifferentiableAt ℝ (fun h : TangentSpace 𝓘(ℝ,Model n) x => cTransform v (riemannianExp x h)) 0 := by
    have hf : MDifferentiableAt 𝓘(ℝ,Model n) 𝓘(ℝ,ℝ) (cTransform v)
        (riemannianExp (n := n) x 0) := by simpa only [riemannianExp_zero] using hDiff
    exact (hf.comp 0 ((contMDiff_riemannianExp_fiber x).contMDiffAt.mdifferentiableAt
      (by simp))).differentiableAt
  have hMin : IsLocalMin (fun h => cTransform v (riemannianExp x h)-f h) 0 := by
    apply Filter.Eventually.of_forall
    intro h
    have hs := active_split_lower_support hv hp.1 hp.2
      (show (0:ℝ)<1/2 by norm_num) (show (1/2:ℝ)<1 by norm_num) (riemannianExp x h)
    have he : f h = -(cost (riemannianExp x h) (riemannianExp x ((1/2:ℝ) • p)) -
        cost x (riemannianExp x ((1/2:ℝ) • p))) / (1/2:ℝ) := by
      dsimp [f,normalCost]
      rw [riemannianExp_zero]
      ring
    change cTransform v (riemannianExp x 0)-f 0≤
      cTransform v (riemannianExp x h)-f h
    simp only [riemannianExp_zero,show f 0=0 by simp [f],sub_zero,he]
    linarith only [hs]
  have he := sub_eq_zero.mp (hMin.hasFDerivAt_eq_zero (hU.hasFDerivAt.sub hD))
  rw [←he]
  exact hU.hasFDerivAt

omit [MeasurableSpace M] [BorelSpace M] in
lemma contact_unique_of_mdifferentiable {v : M → ℝ} (hv : Continuous v) {x : M}
    (hDiff : MDifferentiableAt 𝓘(ℝ,Model n) 𝓘(ℝ,ℝ) (cTransform v) x)
    {y z : M} (hy : contactGap (cTransform v) v x y=0)
    (hz : contactGap (cTransform v) v x z=0) : y=z := by
  obtain ⟨p,hp,hep⟩ := exists_minimizing_vector (n := n) x y
  obtain ⟨q,hq,heq⟩ := exists_minimizing_vector (n := n) x z
  have hpA : p∈activeLogs (n := n) v x := ⟨hp,by simpa only [hep] using hy⟩
  have hqA : q∈activeLogs (n := n) v x := ⟨hq,by simpa only [heq] using hz⟩
  have H := (active_log_derivative hv hDiff hpA).unique (active_log_derivative hv hDiff hqA)
  have hpq : p=q := by
    apply ext_inner_right ℝ
    intro h
    exact congrArg (fun D : TangentSpace 𝓘(ℝ,Model n) x →L[ℝ] ℝ => D h) H
  rw [←hep,←heq,hpq]

variable [Nonempty M]
lemma cTransform_ae_unique_contact {v : M → ℝ} (hv : Continuous v) :
    ∀ᵐ x ∂metricVolume (M := M) n, ∃! y, contactGap (cTransform v) v x y=0 := by
  filter_upwards [cTransform_ae_mdifferentiableAt hv] with x hx
  obtain ⟨y,hy⟩ := cTransform_gap_zero hv x
  exact ⟨y,hy,fun z hz => contact_unique_of_mdifferentiable hv hx hz hy⟩

end AEContacts
end WeakMTWTransport

end

end

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Contact_ContactImage
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set Filter MeasureTheory Metric Manifold Bundle
open scoped Topology ContDiff ENNReal NNReal BoundedContinuousFunction

namespace WeakMTWTransport

section ContactImage
variable {M : Type*} [MetricSpace M]

lemma contactGap_swap (u v : M → ℝ) (x y : M) :
    contactGap u v x y=contactGap v u y x := by
  simp only [contactGap,cost,dist_comm y x]
  ring

end ContactImage

end WeakMTWTransport
end
end
end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Duality_CompactDual
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory Manifold Bundle
open scoped ContDiff Manifold ENNReal NNReal Topology

namespace WeakMTWTransport
open Matrix
open scoped MatrixOrder
open scoped BoundedContinuousFunction

variable {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]

lemma boundedCTransform_apply (v : M →ᵇ ℝ) (x : M) :
    boundedCTransform v x = cTransform v x := rfl

lemma boundedCTransform_nonexpansive : LipschitzWith 1 (boundedCTransform (M := M)) := by
  apply LipschitzWith.of_dist_le_mul
  intro v w
  simp only [NNReal.coe_one, one_mul]
  apply (BoundedContinuousFunction.dist_le dist_nonneg).mpr
  intro x
  rw [Real.dist_eq, abs_le]
  have hbound (a b : M →ᵇ ℝ) : cTransform a x - cTransform b x ≤ dist a b := by
    rw [sub_le_iff_le_add, cTransform_le_iff a.continuous]
    intro y
    have hg := cTransform_gap_nonneg b.continuous x y
    have hd := BoundedContinuousFunction.dist_coe_le_dist (f := a) (g := b) y
    rw [Real.dist_eq, abs_le] at hd
    dsimp [contactGap] at hg
    linarith [hd.1]
  constructor
  · have hh := hbound w v
    rw [dist_comm w v] at hh
    change -dist v w ≤ cTransform v x - cTransform w x
    linarith
  · exact hbound v w

end WeakMTWTransport
end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Duality_DualVariation
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
open Set Filter MeasureTheory Metric
open scoped Topology ENNReal NNReal BoundedContinuousFunction

namespace WeakMTWTransport
section DualVariation
variable {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]

lemma contact_gap_level_control {v : M → ℝ} (hv : Continuous v) {x y₀ : M}
    (huniq : ∀ y, contactGap (cTransform v) v x y=0 → y=y₀)
    (f : M →ᵇ ℝ) {ε : ℝ} (hε : 0<ε) :
    ∃ δ>0, ∀ y, contactGap (cTransform v) v x y≤δ → |f y₀-f y|≤ε := by
  let G := fun y => contactGap (cTransform v) v x y
  have hG : Continuous G := (continuous_const.add (continuous_cost_right x)).add hv
  let A := {y | ε≤|f y₀-f y|}
  have hA : IsCompact A := (isClosed_le continuous_const
    ((continuous_const.sub f.continuous).abs)).isCompact
  by_cases hne : A.Nonempty
  · obtain ⟨z,hz,hmin⟩ := hA.exists_isMinOn hne hG.continuousOn
    have hpos : 0<G z := by
      apply lt_of_le_of_ne (cTransform_gap_nonneg hv x z)
      intro he
      have hez := huniq z he.symm
      have H : ε≤|f y₀-f z| := hz
      rw [hez,sub_self,abs_zero] at H
      exact (not_le.mpr hε) H
    refine ⟨G z/2,half_pos hpos,fun y hy => ?_⟩
    by_contra hh
    have hm := hmin (le_of_lt (lt_of_not_ge hh))
    change G z≤G y at hm
    change G y≤G z/2 at hy
    linarith
  · refine ⟨1,by norm_num,fun y _ => ?_⟩
    by_contra hh
    exact hne ⟨y,le_of_lt (lt_of_not_ge hh)⟩

lemma boundedCTransform_perturbation_bound (v f : M →ᵇ ℝ) (t : ℝ) (x : M) :
    |boundedCTransform (v+t • f) x-boundedCTransform v x|≤|t| *‖f‖ := by
  have H := boundedCTransform_nonexpansive.norm_sub_le (v+t • f) v
  have hp := BoundedContinuousFunction.norm_coe_le_norm
    (boundedCTransform (v+t • f)-boundedCTransform v) x
  simp only [BoundedContinuousFunction.sub_apply,Real.norm_eq_abs] at hp
  apply hp.trans
  simpa only [NNReal.coe_one,one_mul,add_sub_cancel_left,norm_smul,Real.norm_eq_abs] using H

lemma boundedCTransform_perturbation_hasDerivAt (v f : M →ᵇ ℝ) {x y₀ : M}
    (hy₀ : contactGap (boundedCTransform v) v x y₀=0)
    (huniq : ∀ y, contactGap (boundedCTransform v) v x y=0 → y=y₀) :
    HasDerivAt (fun t : ℝ => boundedCTransform (v+t • f) x) (-f y₀) 0 := by
  rw [hasDerivAt_iff_isLittleO,Asymptotics.isLittleO_iff]
  intro ε hε
  obtain ⟨δ,hδ,hcontrol⟩ := contact_gap_level_control v.continuous huniq f hε
  have hden : 0<2*‖f‖+1 := by positivity
  filter_upwards [Metric.ball_mem_nhds (0:ℝ) (div_pos hδ hden)] with t ht
  have ht' : |t|<δ/(2*‖f‖+1) := by simpa only [mem_ball,Real.dist_eq,sub_zero] using ht
  have htδ : |t| *(2*‖f‖+1)<δ := (lt_div_iff₀ hden).mp ht'
  obtain ⟨y,hy⟩ := cTransform_gap_zero (v+t • f).continuous x
  have hgap := cTransform_gap_nonneg v.continuous x y
  have hbound := boundedCTransform_perturbation_bound v f t x
  have hf := BoundedContinuousFunction.norm_coe_le_norm f y
  rw [Real.norm_eq_abs] at hf
  have htf : |t*f y|≤|t| *‖f‖ := by rw [abs_mul]; exact mul_le_mul_of_nonneg_left hf (abs_nonneg t)
  have hy' : boundedCTransform (v+t • f) x + cost x y+v y+t*f y=0 := by
    simpa only [contactGap,BoundedContinuousFunction.add_apply,BoundedContinuousFunction.smul_apply,
      smul_eq_mul,add_assoc,boundedCTransform_apply] using hy
  have hsmall : contactGap (boundedCTransform v) v x y≤δ := by
    dsimp only [contactGap]
    nlinarith [(abs_le.mp hbound).1,(abs_le.mp htf).1,abs_nonneg t]
  have hc := hcontrol y hsmall
  have hrem := cTransform_gap_nonneg (v+t • f).continuous x y₀
  change 0≤boundedCTransform (v+t • f) x+cost x y₀+(v+t • f) y₀ at hrem
  simp only [BoundedContinuousFunction.add_apply,BoundedContinuousFunction.smul_apply,smul_eq_mul] at hrem
  dsimp only [contactGap] at hy₀ hgap
  change 0≤boundedCTransform v x+cost x y+v y at hgap
  have hab : |t*(f y₀-f y)|≤|t| *ε := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left hc (abs_nonneg t)
  simp only [sub_zero,zero_smul,add_zero,smul_eq_mul,Real.norm_eq_abs]
  rw [abs_le]
  constructor
  · nlinarith [mul_nonneg hε.le (abs_nonneg t)]
  · nlinarith [(abs_le.mp hab).2]

end DualVariation
end WeakMTWTransport

end

end

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Duality_AEDual
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set Filter MeasureTheory Metric
open scoped Topology ENNReal NNReal BoundedContinuousFunction

namespace WeakMTWTransport
section AEDual
variable {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [MeasurableSpace M] [BorelSpace M]

omit [MeasurableSpace M] [BorelSpace M] in
lemma boundedCTransform_perturbation_lipschitz (v f : M →ᵇ ℝ) (x : M) :
    LipschitzWith ‖f‖₊ (fun t : ℝ => boundedCTransform (v+t • f) x) := by
  apply LipschitzWith.of_dist_le_mul
  intro t s
  have hp := BoundedContinuousFunction.dist_coe_le_dist
    (f := boundedCTransform (v+t • f)) (g := boundedCTransform (v+s • f)) x
  apply hp.trans
  have H := boundedCTransform_nonexpansive.dist_le_mul (v+t • f) (v+s • f)
  simp only [NNReal.coe_one,one_mul] at H
  refine H.trans_eq ?_
  rw [dist_eq_norm,add_sub_add_left_eq_sub,← sub_smul t s f,norm_smul,Real.norm_eq_abs,Real.dist_eq]
  exact mul_comm _ _

lemma dual_minimum_integral_eq_ae (mu nu : Measure M) [IsProbabilityMeasure mu]
    [IsProbabilityMeasure nu] (v : M →ᵇ ℝ) (T : M → M)
    (hT : AEMeasurable T mu)
    (hfib : ∀ᵐ x ∂mu, contactGap (boundedCTransform v) v x (T x)=0 ∧
      ∀ y, contactGap (boundedCTransform v) v x y=0 → y=T x)
    (hmin : ∀ a b : M →ᵇ ℝ, (∀ x y, 0 ≤ contactGap a b x y) →
      dualObjective mu nu (boundedCTransform v,v)≤dualObjective mu nu (a,b))
    (f : M →ᵇ ℝ) : (∫ x, f (T x) ∂mu)=∫ y,f y ∂nu := by
  have hmeas : AEStronglyMeasurable (fun x => -f (T x)) mu :=
    (f.continuous.measurable.comp_aemeasurable hT).aestronglyMeasurable.neg
  have hdiff : ∀ᵐ x ∂mu, HasDerivAt
      (fun t : ℝ => boundedCTransform (v+t • f) x) (-f (T x)) 0 := by
    filter_upwards [hfib] with x hx
    exact boundedCTransform_perturbation_hasDerivAt v f hx.1 hx.2
  have hlip : ∀ᵐ x ∂mu, LipschitzOnWith (Real.nnabs ‖f‖)
      (fun t : ℝ => boundedCTransform (v+t • f) x) univ := by
    filter_upwards [] with x
    simpa only [show Real.nnabs ‖f‖ = ‖f‖₊ from by ext; simp] using (boundedCTransform_perturbation_lipschitz v f x).lipschitzOnWith
  obtain ⟨_,hder⟩ := hasDerivAt_integral_of_dominated_loc_of_lip
    (F := fun t x => boundedCTransform (v+t • f) x)
    (F' := fun x => -f (T x)) (bound := fun _ => ‖f‖)
    (s := univ) (mem_of_superset (Filter.univ_mem) (by simp))
    (Filter.Eventually.of_forall fun t => (boundedCTransform (v+t • f)).continuous.aestronglyMeasurable)
    (by simpa only [zero_smul,add_zero] using (boundedCTransform v).integrable mu)
    hmeas hlip (integrable_const _) hdiff
  have hlin : HasDerivAt (fun t : ℝ => ∫ y, (v+t • f) y ∂nu) (∫ y,f y ∂nu) 0 := by
    have H := (hasDerivAt_const (0:ℝ) (∫ y,v y ∂nu)).add
      ((hasDerivAt_id (0:ℝ)).mul_const (∫ y,f y ∂nu))
    simpa only [Pi.add_def,Pi.add_apply,id_eq,zero_add,one_mul,BoundedContinuousFunction.add_apply,
      BoundedContinuousFunction.smul_apply,smul_eq_mul,integral_add (v.integrable nu)
      ((f.integrable nu).const_mul _),integral_const_mul] using H
  have hsum := hder.add hlin
  have hlocal : IsLocalMin (fun t : ℝ => (∫ x,boundedCTransform (v+t • f) x ∂mu)+
      ∫ y,(v+t • f) y ∂nu) 0 := by
    filter_upwards [] with t
    simpa only [zero_smul,add_zero,dualObjective] using
      hmin (boundedCTransform (v+t • f)) (v+t • f)
        (cTransform_gap_nonneg (v+t • f).continuous)
  have H := hlocal.hasDerivAt_eq_zero hsum
  rw [integral_neg] at H
  linarith

lemma dual_minimum_pushforward_ae (mu nu : Measure M) [IsProbabilityMeasure mu]
    [IsProbabilityMeasure nu] (v : M →ᵇ ℝ) (T : M → M)
    (hT : AEMeasurable T mu)
    (hfib : ∀ᵐ x ∂mu, contactGap (boundedCTransform v) v x (T x)=0 ∧
      ∀ y, contactGap (boundedCTransform v) v x y=0 → y=T x)
    (hmin : ∀ a b : M →ᵇ ℝ, (∀ x y, 0 ≤ contactGap a b x y) →
      dualObjective mu nu (boundedCTransform v,v)≤dualObjective mu nu (a,b)) :
    Measure.map T mu=nu := by
  apply ext_of_forall_integral_eq_of_IsFiniteMeasure
  intro f
  rw [integral_map hT f.continuous.aestronglyMeasurable]
  exact dual_minimum_integral_eq_ae mu nu v T hT hfib hmin f

end AEDual
end WeakMTWTransport

end

end

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Contact_ContactSelection
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set Filter Manifold MeasureTheory Bundle Metric
open scoped Topology ContDiff ENNReal NNReal

namespace WeakMTWTransport
section ContactSelection
variable {M : Type*} [MetricSpace M] [CompactSpace M]

lemma contact_selection_continuousAt {u v : M → ℝ} (hu : Continuous u) (hv : Continuous v)
    {T : M → M} (hT : ∀ z, contactGap u v z (T z)=0) {x : M}
    (hx : ∀ y, contactGap u v x y=0 → y=T x) : ContinuousAt T x := by
  rw [Metric.continuousAt_iff]
  intro ε hε
  let A := {z : M×M | contactGap u v z.1 z.2=0 ∧ z.2∉ball (T x) ε}
  have hg : Continuous (fun z : M×M => contactGap u v z.1 z.2) :=
    ((hu.comp continuous_fst).add
      (((continuous_fst.dist continuous_snd).pow 2).div_const 2)).add
      (hv.comp continuous_snd)
  have hA : IsClosed A := (isClosed_eq hg continuous_const).inter
    (isOpen_ball.preimage continuous_snd).isClosed_compl
  have hB : IsClosed (Prod.fst '' A) := isClosedMap_fst_of_compactSpace A hA
  have hxB : x∉Prod.fst '' A := by
    rintro ⟨⟨z,y⟩,⟨hzy,hy⟩,rfl⟩
    exact hy ((hx y hzy) ▸ mem_ball_self hε)
  obtain ⟨δ,hδ,hball⟩ := Metric.mem_nhds_iff.mp (hB.isOpen_compl.mem_nhds hxB)
  refine ⟨δ,hδ,fun {z} hz => ?_⟩
  by_contra hbad
  exact hball hz ⟨(z,T z),⟨hT z,hbad⟩,rfl⟩

variable [Nonempty M]

lemma contactSelection_mem {v : M → ℝ} (hv : Continuous v) (x : M) :
    contactGap (cTransform v) v x (contactSelection hv x)=0 :=
  (cTransform_gap_zero hv x).choose_spec

end ContactSelection

end WeakMTWTransport
end
end
end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Volume_AemeasurableAeContinuous
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set Filter Manifold MeasureTheory Bundle Metric
open scoped Topology ContDiff ENNReal NNReal

namespace WeakMTWTransport

lemma aemeasurable_of_ae_continuousAt {X Y : Type*} [TopologicalSpace X]
    [MeasurableSpace X] [OpensMeasurableSpace X] [TopologicalSpace Y]
    [MeasurableSpace Y] [BorelSpace Y] {μ : Measure X} {f : X → Y}
    (h : ∀ᵐ x ∂μ, ContinuousAt f x) : AEMeasurable f μ := by
  let s := {x | ContinuousAt f x}
  have hs : NullMeasurableSet s μ := .of_compl (.of_null (ae_iff.mp h))
  have hc : ContinuousOn f s := fun x hx => hx.continuousWithinAt
  have H := hc.aemeasurable₀ hs
  rw [Measure.restrict_eq_self_of_ae_mem (s := s) h] at H
  exact H

end WeakMTWTransport
end
end
end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Volume_AESelection
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set Filter Manifold MeasureTheory Bundle Metric
open scoped Topology ContDiff ENNReal NNReal

namespace WeakMTWTransport
section AESelection
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma contactSelection_aemeasurable {v : M → ℝ} (hv : Continuous v) :
    AEMeasurable (contactSelection hv) (metricVolume (M := M) n) := by
  apply aemeasurable_of_ae_continuousAt
  filter_upwards [cTransform_ae_unique_contact (n := n) hv] with x hx
  apply contact_selection_continuousAt (continuous_cTransform hv) hv (contactSelection_mem hv)
  intro y hy
  exact hx.unique hy (contactSelection_mem hv x)

end AESelection
end WeakMTWTransport

end

end

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Volume_DensityBounds
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set MeasureTheory Manifold Bundle
open scoped ContDiff Manifold ENNReal NNReal Topology

namespace WeakMTWTransport
open Matrix
open scoped MatrixOrder
open scoped BoundedContinuousFunction

section DensityBounds
variable {M : Type*} [MetricSpace M] [MeasurableSpace M] [BorelSpace M] [CompactSpace M]
omit [MetricSpace M] [BorelSpace M] [CompactSpace M] in

lemma densityMeasure_bounds {vol : Measure M} {lam cap : ℝ} {rho : M → ℝ}
    (hrho : AdmissibleDensity vol lam cap rho) :
    ENNReal.ofReal lam • vol ≤ densityMeasure vol rho ∧
      densityMeasure vol rho ≤ ENNReal.ofReal cap • vol := by
  constructor
  · rw [← withDensity_const]
    apply withDensity_mono
    filter_upwards [hrho.2.2.2] with x hx
    exact ENNReal.ofReal_le_ofReal hx.1
  · rw [← withDensity_const]
    apply withDensity_mono
    filter_upwards [hrho.2.2.2] with x hx
    exact ENNReal.ofReal_le_ofReal hx.2

omit [MetricSpace M] [BorelSpace M] [CompactSpace M] in
lemma volume_absolutelyContinuous_densityMeasure {vol : Measure M} {lam cap : ℝ}
    {rho : M → ℝ} (hlam : 0 < lam) (hrho : AdmissibleDensity vol lam cap rho) :
    vol ≪ densityMeasure vol rho := by
  apply withDensity_absolutelyContinuous' hrho.1.ennreal_ofReal
  filter_upwards [hrho.2.2.2] with x hx
  exact (ENNReal.ofReal_pos.mpr (hlam.trans_le hx.1)).ne'
end DensityBounds

end WeakMTWTransport
end
end
end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Volume_MeasureContacts
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set Filter MeasureTheory Manifold Bundle
open scoped ENNReal NNReal ContDiff Topology BoundedContinuousFunction

namespace WeakMTWTransport

section MeasureContacts
variable {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [MeasurableSpace M] [BorelSpace M]

omit [CompactSpace M] [Nonempty M] [BorelSpace M] in

lemma dual_minimum_swap {μ ν : Measure M} {u v : M →ᵇ ℝ}
    (hmin : ∀ a b : M →ᵇ ℝ, (∀ x y, 0 ≤ contactGap a b x y) →
      dualObjective μ ν (u,v) ≤ dualObjective μ ν (a,b)) :
    ∀ a b : M →ᵇ ℝ, (∀ x y, 0 ≤ contactGap a b x y) →
      dualObjective ν μ (v,u) ≤ dualObjective ν μ (a,b) := by
  intro a b hab
  have hh := hmin b a (fun x y => by rw [contactGap_symm]; exact hab y x)
  simpa only [dualObjective,add_comm] using hh

omit [CompactSpace M] [Nonempty M] [BorelSpace M] in

lemma contactImage_ae_eq_preimage {μ : Measure M} {u v : M → ℝ} {S : M → M}
    (hcontact : ∀ y, contactGap u v (S y) y = 0)
    (hsingle : ∀ᵐ y ∂μ, ∀ x, contactGap u v x y = 0 → x = S y)
    (A : Set M) : contactImage u v A =ᵐ[μ] S ⁻¹' A := by
  filter_upwards [hsingle] with y hy
  apply propext
  change (∃ x ∈ A, contactGap u v x y = 0) ↔ S y ∈ A
  constructor
  · rintro ⟨x,hx,hxy⟩
    simpa only [hy x hxy] using hx
  · intro hx
    exact ⟨S y,hx,hcontact y⟩

omit [CompactSpace M] [Nonempty M] [BorelSpace M] in

lemma contactImage_measure {μ ν : Measure M} {u v : M → ℝ} {S : M → M}
    (hcontact : ∀ y, contactGap u v (S y) y = 0)
    (hsingle : ∀ᵐ y ∂ν, ∀ x, contactGap u v x y = 0 → x = S y)
    (hS : AEMeasurable S ν) (hpush : Measure.map S ν = μ)
    {A : Set M} (hA : MeasurableSet A) :
    NullMeasurableSet (contactImage u v A) ν ∧ ν (contactImage u v A) = μ A := by
  have he := contactImage_ae_eq_preimage hcontact hsingle A
  refine ⟨?_,?_⟩
  · exact (hS.nullMeasurableSet_preimage hA).congr he.symm
  · rw [measure_congr he,← Measure.map_apply_of_aemeasurable hS hA,hpush]

end MeasureContacts

end WeakMTWTransport
end
end
end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Volume_RadialNull
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory Manifold Bundle
open scoped ContDiff Manifold ENNReal NNReal Topology

namespace WeakMTWTransport
open Matrix
open scoped MatrixOrder

section TransportCertificates
variable {M : Type*} [MetricSpace M] [MeasurableSpace M] [BorelSpace M]

omit [MetricSpace M] [BorelSpace M] in
lemma density_nonnegative {vol : Measure M} {lam cap : ℝ} {rho : M → ℝ}
    (hlam : 0 < lam) (hrho : AdmissibleDensity vol lam cap rho) :
    ∀ᵐ x ∂vol, 0 ≤ rho x := by
  filter_upwards [hrho.2.2.2] with x hx
  exact hlam.le.trans hx.1

omit [MetricSpace M] [BorelSpace M] in
lemma densityMeasure_probability {vol : Measure M} {lam cap : ℝ} {rho : M → ℝ}
    (hlam : 0 < lam) (hrho : AdmissibleDensity vol lam cap rho) :
    IsProbabilityMeasure (densityMeasure vol rho) := by
  constructor
  rw [densityMeasure, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal hrho.2.1 (density_nonnegative hlam hrho),
    hrho.2.2.1, ENNReal.ofReal_one]

end TransportCertificates

open scoped BoundedContinuousFunction

end WeakMTWTransport
end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Geodesics_OriginalMass
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set Filter MeasureTheory Metric Manifold Bundle
open scoped Topology ContDiff ENNReal NNReal BoundedContinuousFunction

namespace WeakMTWTransport
section OriginalMass
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma minimizing_dualPair_selection_pushforward {lam cap : ℝ} (hlam : 0<lam)
    {rho0 rho1 : M → ℝ}
    (h0 : AdmissibleDensity (metricVolume n) lam cap rho0)
    (h1 : AdmissibleDensity (metricVolume n) lam cap rho1)
    {u v : M →ᵇ ℝ} (huv : IsCostDualPair u v)
    (hmin : ∀ a b : M →ᵇ ℝ, (∀ x y,0 ≤ contactGap a b x y) →
      dualObjective (densityMeasure (metricVolume n) rho0)
        (densityMeasure (metricVolume n) rho1) (u,v) ≤
      dualObjective (densityMeasure (metricVolume n) rho0)
        (densityMeasure (metricVolume n) rho1) (a,b)) :
    Measure.map (contactSelection v.continuous) (densityMeasure (metricVolume n) rho0)=
      densityMeasure (metricVolume n) rho1 := by
  let : IsProbabilityMeasure (densityMeasure (metricVolume n) rho0) := densityMeasure_probability hlam h0
  let : IsProbabilityMeasure (densityMeasure (metricVolume n) rho1) := densityMeasure_probability hlam h1
  have heq : u=boundedCTransform v := by
    ext x
    exact congrFun huv.1 x
  have habs : densityMeasure (metricVolume n) rho0 ≪ metricVolume n :=
    withDensity_absolutelyContinuous (metricVolume (M := M) n) _
  apply dual_minimum_pushforward_ae _ _ v (contactSelection v.continuous)
    ((contactSelection_aemeasurable (n := n) v.continuous).mono_ac habs)
  · filter_upwards [habs.ae_le (cTransform_ae_unique_contact (n := n) v.continuous)] with x hx
    exact ⟨contactSelection_mem v.continuous x,
      fun y hy => hx.unique hy (contactSelection_mem v.continuous x)⟩
  · simpa only [heq] using hmin

lemma minimizing_dualPair_contact_mass {lam cap : ℝ} (hlam : 0<lam)
    {rho0 rho1 : M → ℝ}
    (h0 : AdmissibleDensity (metricVolume n) lam cap rho0)
    (h1 : AdmissibleDensity (metricVolume n) lam cap rho1)
    {u v : M →ᵇ ℝ} (huv : IsCostDualPair u v)
    (hmin : ∀ a b : M →ᵇ ℝ, (∀ x y,0 ≤ contactGap a b x y) →
      dualObjective (densityMeasure (metricVolume n) rho0)
        (densityMeasure (metricVolume n) rho1) (u,v) ≤
      dualObjective (densityMeasure (metricVolume n) rho0)
        (densityMeasure (metricVolume n) rho1) (a,b))
    {A : Set M} (hA : MeasurableSet A) :
    densityMeasure (metricVolume n) rho1 (contactImage u v A)=
      densityMeasure (metricVolume n) rho0 A := by
  have hrev : ∀ a b : M →ᵇ ℝ, (∀ x y,0 ≤ contactGap a b x y) →
      dualObjective (densityMeasure (metricVolume n) rho1)
        (densityMeasure (metricVolume n) rho0) (v,u) ≤
      dualObjective (densityMeasure (metricVolume n) rho1)
        (densityMeasure (metricVolume n) rho0) (a,b) := by
    intro a b hab
    have H := hmin b a (fun x y => by rw [contactGap_swap]; exact hab y x)
    simpa only [dualObjective,add_comm] using H
  have hp := minimizing_dualPair_selection_pushforward hlam h1 h0
    ⟨huv.2,huv.1⟩ hrev
  have habs : densityMeasure (metricVolume n) rho1 ≪ metricVolume n :=
    withDensity_absolutelyContinuous (metricVolume (M := M) n) _
  have hc : ∀ y,contactGap u v (contactSelection u.continuous y) y=0 := by
    intro y
    rw [contactGap_swap,huv.2]
    exact contactSelection_mem u.continuous y
  have hs : ∀ᵐ y ∂densityMeasure (metricVolume n) rho1,
      ∀ x,contactGap u v x y=0 → x=contactSelection u.continuous y := by
    filter_upwards [habs.ae_le (cTransform_ae_unique_contact (n := n) u.continuous)] with y hy
    intro x hx
    rw [contactGap_swap,huv.2] at hx
    exact hy.unique hx (contactSelection_mem u.continuous y)
  exact (contactImage_measure hc hs
    ((contactSelection_aemeasurable (n := n) u.continuous).mono_ac habs) hp hA).2

lemma minimizing_dualPair_contact_volume {lam cap : ℝ} (hlam : 0<lam) (hcap : lam ≤ cap)
    {rho0 rho1 : M → ℝ}
    (h0 : AdmissibleDensity (metricVolume n) lam cap rho0)
    (h1 : AdmissibleDensity (metricVolume n) lam cap rho1)
    {u v : M →ᵇ ℝ} (huv : IsCostDualPair u v)
    (hmin : ∀ a b : M →ᵇ ℝ, (∀ x y,0 ≤ contactGap a b x y) →
      dualObjective (densityMeasure (metricVolume n) rho0)
        (densityMeasure (metricVolume n) rho1) (u,v) ≤
      dualObjective (densityMeasure (metricVolume n) rho0)
        (densityMeasure (metricVolume n) rho1) (a,b))
    {A : Set M} (hA : MeasurableSet A) :
    ENNReal.ofReal (lam/cap)*metricVolume n A ≤ metricVolume n (contactImage u v A) ∧
      metricVolume n (contactImage u v A) ≤ ENNReal.ofReal (cap/lam)*metricVolume n A := by
  have hm := minimizing_dualPair_contact_mass hlam h0 h1 huv hmin hA
  have ha := (densityMeasure_bounds h0).1 A
  have hb := (densityMeasure_bounds h0).2 A
  have hc := (densityMeasure_bounds h1).1 (contactImage u v A)
  have hd := (densityMeasure_bounds h1).2 (contactImage u v A)
  simp only [Measure.smul_apply,smul_eq_mul] at ha hb hc hd
  rw [hm] at hc hd
  have hcap' := hlam.trans_le hcap
  have hdiv (a b c : ℝ≥0∞) : a/b*c=a*c/b := by
    simp only [div_eq_mul_inv,mul_right_comm]
  constructor
  · rw [ENNReal.ofReal_div_of_pos hcap',hdiv,
      ENNReal.div_le_iff' (ENNReal.ofReal_pos.mpr hcap').ne' ENNReal.ofReal_ne_top]
    exact ha.trans hd
  · rw [ENNReal.ofReal_div_of_pos hlam,hdiv,
      ENNReal.le_div_iff_mul_le (Or.inl (ENNReal.ofReal_pos.mpr hlam).ne')
        (Or.inl ENNReal.ofReal_ne_top),mul_comm]
    exact hc.trans hb

end OriginalMass
end WeakMTWTransport

end

end

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Volume_MeasurableFullSubset
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set Filter MeasureTheory Metric Manifold Bundle
open scoped Topology ContDiff ENNReal NNReal BoundedContinuousFunction

namespace WeakMTWTransport

lemma exists_measurable_full_subset {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {P : X → Prop} (h : ∀ᵐ x ∂μ, P x) :
    ∃ G : Set X, MeasurableSet G ∧ (∀ᵐ x ∂μ, x∈G) ∧ ∀ x∈G, P x := by
  have hn : μ {x | ¬P x}=0 := ae_iff.mp h
  obtain ⟨G,hG,hGm,hGe⟩ := (NullMeasurableSet.of_null hn).compl.exists_measurable_subset_ae_eq
  refine ⟨G,hGm,?_,?_⟩
  · filter_upwards [hGe,h] with x hx hp
    exact hx.mpr (fun hn => hn hp)
  · intro x hx
    exact not_not.mp (hG hx)

end WeakMTWTransport
end
end
end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Geodesics_GoodContact
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set Filter MeasureTheory Metric Manifold Bundle
open scoped Topology ContDiff ENNReal NNReal BoundedContinuousFunction

namespace WeakMTWTransport
section GoodContact
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma minimizing_dualPair_good_contact_set {lam cap : ℝ} (hlam : 0<lam) (hcap : lam ≤ cap)
    {rho0 rho1 : M → ℝ}
    (h0 : AdmissibleDensity (metricVolume n) lam cap rho0)
    (h1 : AdmissibleDensity (metricVolume n) lam cap rho1)
    {u v : M →ᵇ ℝ} (huv : IsCostDualPair u v)
    (hmin : ∀ a b : M →ᵇ ℝ, (∀ x y,0 ≤ contactGap a b x y) →
      dualObjective (densityMeasure (metricVolume n) rho0)
        (densityMeasure (metricVolume n) rho1) (u,v) ≤
      dualObjective (densityMeasure (metricVolume n) rho0)
        (densityMeasure (metricVolume n) rho1) (a,b)) :
    ∃ G : Set M, MeasurableSet G ∧ (∀ᵐ x ∂metricVolume n, x∈G) ∧
      InjOn (contactSelection v.continuous) G ∧
      (∀ x∈G, MDifferentiableAt 𝓘(ℝ,Model n) 𝓘(ℝ,ℝ) (cTransform v) x) ∧
      (∀ A : Set M, MeasurableSet A → A⊆G →
        ENNReal.ofReal (lam/cap)*metricVolume n A ≤
          metricVolume n (contactSelection v.continuous '' A) ∧
        metricVolume n (contactSelection v.continuous '' A) ≤
          ENNReal.ofReal (cap/lam)*metricVolume n A) := by
  let μ := densityMeasure (metricVolume n) rho0
  let ν := densityMeasure (metricVolume n) rho1
  let T := contactSelection v.continuous
  have hT (x : M) : contactGap u v x (T x)=0 := by
    rw [huv.1]
    exact contactSelection_mem v.continuous x
  have hμ : μ ≪ metricVolume n := withDensity_absolutelyContinuous _ _
  have hν : ν ≪ metricVolume n := withDensity_absolutelyContinuous _ _
  have hTm : AEMeasurable T μ := (contactSelection_aemeasurable (n := n) v.continuous).mono_ac hμ
  have hpush : Measure.map T μ=ν := minimizing_dualPair_selection_pushforward hlam h0 h1 huv hmin
  have hrev : ∀ᵐ x ∂metricVolume n, ∀ a, contactGap u v a (T x)=0 → a=x := by
    have H := hν.ae_le (cTransform_ae_unique_contact (n := n) u.continuous)
    rw [←hpush] at H
    have H' := ae_of_ae_map hTm H
    apply (volume_absolutelyContinuous_densityMeasure hlam h0).ae_le
    filter_upwards [H'] with x hx
    intro a ha
    have hax : contactGap (cTransform u) u (T x) a=0 := by
      simpa only [←huv.2,contactGap_swap _ _ (T x) a] using ha
    have hxx : contactGap (cTransform u) u (T x) x=0 := by
      simpa only [←huv.2,contactGap_swap _ _ (T x) x] using hT x
    exact hx.unique hax hxx
  obtain ⟨G,hGm,hGae,hG⟩ := exists_measurable_full_subset
    ((cTransform_ae_mdifferentiableAt (n := n) v.continuous).and hrev)
  refine ⟨G,hGm,hGae,?_,fun x hx => (hG x hx).1,?_⟩
  · intro x hx z hz he
    apply (hG z hz).2 x
    change T x=T z at he
    rw [←he]
    exact hT x
  · intro A hA hAG
    have he : contactImage u v A=T '' A := by
      ext y
      constructor
      · rintro ⟨x,hx,hxy⟩
        refine ⟨x,hx,?_⟩
        apply contact_unique_of_mdifferentiable v.continuous (hG x (hAG hx)).1
        · exact contactSelection_mem v.continuous x
        · rwa [←huv.1]
      · rintro ⟨x,hx,rfl⟩
        exact ⟨x,hx,hT x⟩
    simpa only [he] using minimizing_dualPair_contact_volume hlam hcap h0 h1 huv hmin hA

end GoodContact
end WeakMTWTransport

end

end

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Contact_ContactCharts
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.WeakMTWTransport.fixedJoinMiddle_apply _root_.OAI.WeakMTWTransport.normalEndpointMixedOperator_inner
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
open Set Filter MeasureTheory Manifold Bundle Metric
open scoped Topology ContDiff ENNReal NNReal BoundedContinuousFunction

namespace WeakMTWTransport
section RegularContact
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

local instance tangentFiniteRegularContact_r076506_1 (x : M) :
    FiniteDimensional ℝ (TangentSpace 𝓘(ℝ,Model n) x) :=
  inferInstanceAs (FiniteDimensional ℝ (Model n))
omit [MeasurableSpace M] [BorelSpace M] in
lemma cTransform_normal_expansion_active {v : M → ℝ} (hv : Continuous v) {x : M}
    (hD : MDifferentiableAt 𝓘(ℝ,Model n) 𝓘(ℝ,ℝ) (cTransform v) x)
    {p : TangentSpace 𝓘(ℝ,Model n) x}
    {A : TangentSpace 𝓘(ℝ,Model n) x →L[ℝ] TangentSpace 𝓘(ℝ,Model n) x}
    (hexp : HasQuadraticExpansion (fun h => cTransform v (riemannianExp x h)) p A) :
    p∈activeLogs (n := n) v x := by
  obtain ⟨y,hy⟩ := cTransform_gap_zero hv x
  obtain ⟨q,hq,heq⟩ := exists_minimizing_vector (n := n) x y
  have hqa : q∈activeLogs (n := n) v x := ⟨hq,by simpa only [heq] using hy⟩
  have hDerivative : HasFDerivAt (fun offset => cTransform v (riemannianExp x offset))
      ((innerSL ℝ) p) 0 := by
    obtain ⟨radius,hradius,hbound⟩ := hexp 1 zero_lt_one
    let bound : ℝ := 1+‖A‖/2
    have hpositive : 0<bound := by dsimp [bound] <;> positivity
    rw [hasFDerivAt_iff_isLittleO_nhds_zero,Asymptotics.isLittleO_iff]
    intro epsilon hepsilon
    have hsmall : 0 < min radius (epsilon/bound) := by positivity
    filter_upwards [Metric.ball_mem_nhds (0:TangentSpace 𝓘(ℝ,Model n) x) hsmall]
      with offset hoffset
    have hnorm : ‖offset‖ < min radius (epsilon/bound) := by
      simpa only [Metric.mem_ball,dist_zero_right] using hoffset
    have hremainder := hbound offset (lt_of_lt_of_le hnorm (min_le_left _ _))
    have hquadratic : |inner ℝ (A offset) offset|≤‖A‖*‖offset‖^2 := by
      calc
        _ ≤ ‖A offset‖*‖offset‖ := abs_real_inner_le_norm _ _
        _ ≤ (‖A‖*‖offset‖)*‖offset‖ :=
          mul_le_mul_of_nonneg_right (A.le_opNorm offset) (norm_nonneg _)
        _ = _ := by ring
    have hlinear : |cTransform v (riemannianExp x offset)-
        cTransform v (riemannianExp (n := n) x 0)-inner ℝ p offset|≤bound*‖offset‖^2 := by
      have htriangle := abs_add_le
        (cTransform v (riemannianExp x offset)-
          quadraticTaylor (cTransform v (riemannianExp (n := n) x 0)) p A offset)
        (inner ℝ (A offset) offset/2)
      rw [abs_div,abs_of_pos (by norm_num : (0:ℝ)<2)] at htriangle
      simp only [quadraticTaylor] at hremainder htriangle
      dsimp [bound]
      have hcancel : cTransform v (riemannianExp x offset)-
          (cTransform v (riemannianExp (n := n) x 0)+inner ℝ p offset+
            inner ℝ (A offset) offset/2)+inner ℝ (A offset) offset/2 =
          cTransform v (riemannianExp x offset)-
            cTransform v (riemannianExp (n := n) x 0)-inner ℝ p offset := by ring
      rw [hcancel] at htriangle
      nlinarith
    have hscale : ‖offset‖*bound≤epsilon := (le_div_iff₀ hpositive).mp
      (le_of_lt (lt_of_lt_of_le hnorm (min_le_right _ _)))
    have hfinal : bound*‖offset‖^2≤epsilon*‖offset‖ := by
      nlinarith [mul_le_mul_of_nonneg_right hscale (norm_nonneg offset)]
    simpa only [zero_add,innerSL_apply_apply,Real.norm_eq_abs] using hlinear.trans hfinal
  have H := hDerivative.unique (active_log_derivative hv hD hqa)
  have hpq : p=q := by
    apply ext_inner_right ℝ
    intro h
    exact congrArg (fun D : TangentSpace 𝓘(ℝ,Model n) x →L[ℝ] ℝ => D h) H
  rwa [hpq]

omit [MeasurableSpace M] [BorelSpace M] in
lemma contactSelection_continuousAt_of_mdifferentiable {v : M → ℝ} (hv : Continuous v)
    {x : M} (hD : MDifferentiableAt 𝓘(ℝ,Model n) 𝓘(ℝ,ℝ) (cTransform v) x) :
    ContinuousAt (contactSelection hv) x := by
  apply contact_selection_continuousAt (continuous_cTransform hv) hv (contactSelection_mem hv)
  exact fun y hy => contact_unique_of_mdifferentiable hv hD hy (contactSelection_mem hv x)

lemma minimizing_dualPair_regular_contact_set {lam cap : ℝ} (hlam : 0<lam) (hcap : lam ≤ cap)
    {rho0 rho1 : M → ℝ}
    (h0 : AdmissibleDensity (metricVolume n) lam cap rho0)
    (h1 : AdmissibleDensity (metricVolume n) lam cap rho1)
    {u v : M →ᵇ ℝ} (huv : IsCostDualPair u v)
    (hmin : ∀ a b : M →ᵇ ℝ, (∀ x y,0 ≤ contactGap a b x y) →
      dualObjective (densityMeasure (metricVolume n) rho0)
        (densityMeasure (metricVolume n) rho1) (u,v) ≤
      dualObjective (densityMeasure (metricVolume n) rho0)
        (densityMeasure (metricVolume n) rho1) (a,b)) :
    ∃ G : Set M, MeasurableSet G ∧ (∀ᵐ x ∂metricVolume n, x∈G) ∧
      InjOn (contactSelection v.continuous) G ∧
      (∀ x∈G, MDifferentiableAt 𝓘(ℝ,Model n) 𝓘(ℝ,ℝ) (cTransform v) x) ∧
      (∀ x∈G, ContinuousAt (contactSelection v.continuous) x) ∧
      (∀ x∈G, ∃ p : TangentSpace 𝓘(ℝ,Model n) x,
        ∃ A : TangentSpace 𝓘(ℝ,Model n) x →L[ℝ] TangentSpace 𝓘(ℝ,Model n) x,
        p∈activeLogs (n := n) v x ∧ p∈injectivityDomain x ∧
        (∀ h k, inner ℝ (A h) k=inner ℝ h (A k)) ∧
        HasQuadraticExpansion (fun h => cTransform v (riemannianExp x h)) p A) ∧
      (∀ B : Set M, MeasurableSet B → B⊆G →
        ENNReal.ofReal (lam/cap)*metricVolume n B ≤
          metricVolume n (contactSelection v.continuous '' B) ∧
        metricVolume n (contactSelection v.continuous '' B) ≤
          ENNReal.ofReal (cap/lam)*metricVolume n B) := by
  obtain ⟨G,hGm,hGae,hGi,hGD,hGmass⟩ :=
    minimizing_dualPair_good_contact_set hlam hcap h0 h1 huv hmin
  obtain ⟨H,hHm,hHae,hH⟩ := exists_measurable_full_subset
    ((cTransform_ae_normal_quadraticExpansion (n := n) v.continuous).and
      (cTransform_ae_active_before_cut (n := n) v.continuous))
  refine ⟨G∩H,hGm.inter hHm,hGae.and hHae,hGi.mono inter_subset_left,
    fun x hx => hGD x hx.1,fun x hx =>
      contactSelection_continuousAt_of_mdifferentiable v.continuous (hGD x hx.1),?_,?_⟩
  · intro x hx
    obtain ⟨p,A,hAs,hA⟩ := (hH x hx.2).1
    have hp := cTransform_normal_expansion_active v.continuous (hGD x hx.1) hA
    exact ⟨p,A,hp,(hH x hx.2).2 p hp,hAs,hA⟩
  · intro B hBm hBG
    exact hGmass B hBm (hBG.trans inter_subset_left)

end RegularContact
end WeakMTWTransport

end

end

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_LinearAlgebra_ContactDifferential
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set Filter Manifold Bundle
open scoped Topology ContDiff

namespace WeakMTWTransport
section ContactDifferential
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

attribute [local instance] OAI.WeakMTWTransport.instFiniteDimensionalRealTangentSpaceModelModelWithCornersSelf
omit [CompactSpace M] [Nonempty M] [MeasurableSpace M] [BorelSpace M]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M] in
lemma inner_normalHessianOperator (x : M) (p u v : TangentSpace 𝓘(ℝ,Model n) x) :
    inner ℝ (normalHessianOperator x p u) v=normalHessian x p u v := by
  exact InnerProductSpace.toDual_symm_apply

end ContactDifferential
end WeakMTWTransport

end

end

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Contact_IntrinsicCEMS
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set Filter MeasureTheory Manifold Bundle Metric
open scoped Topology ContDiff ENNReal NNReal BoundedContinuousFunction

namespace WeakMTWTransport
section IntrinsicCEMS
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

attribute [local instance] OAI.WeakMTWTransport.instFiniteDimensionalRealTangentSpaceModelModelWithCornersSelf_3
lemma minimizing_dualPair_uniform_intrinsic_cems {lam cap : ℝ} (hlam : 0<lam)
    (hcap : lam ≤ cap) :
    ∃ chi eta : ℝ, 0 < chi ∧ 0<eta ∧ ∀ (rho0 rho1 : M → ℝ),
      AdmissibleDensity (metricVolume n) lam cap rho0 →
      AdmissibleDensity (metricVolume n) lam cap rho1 →
      ∀ (u v : M →ᵇ ℝ), IsCostDualPair u v →
      (∀ a b : M →ᵇ ℝ, (∀ x y,0 ≤ contactGap a b x y) →
        dualObjective (densityMeasure (metricVolume n) rho0)
          (densityMeasure (metricVolume n) rho1) (u,v) ≤
        dualObjective (densityMeasure (metricVolume n) rho0)
          (densityMeasure (metricVolume n) rho1) (a,b)) →
      ∀ᵐ x ∂metricVolume n, ∃ p A,
        NormalAlexandrovContact (n := n) v x p A ∧
        (∀ w, w≠0 → 0 < inner ℝ ((normalHessianOperator x p+A) w) w) ∧
        chi≤expJacobian (n := n) x p*|(normalHessianOperator x p+A).det| ∧
        expJacobian (n := n) x p*|(normalHessianOperator x p+A).det|≤eta := by
  obtain ⟨chi,eta,hchi,heta,H⟩ := exists_uniform_intrinsic_contact_bounds
    (n := n) (M := M) (div_pos hlam (hlam.trans_le hcap))
      (div_pos (hlam.trans_le hcap) hlam)
  refine ⟨chi,eta,hchi,heta,?_⟩
  intro rho0 rho1 h0 h1 u v huv hmin
  obtain ⟨G,hGm,hGae,hGi,hGD,_hGc,hReg,hmass⟩ :=
    minimizing_dualPair_regular_contact_set hlam hcap h0 h1 huv hmin
  exact H v v.continuous G hGm hGae hGD hGi hReg hmass

end IntrinsicCEMS
end WeakMTWTransport

end

end

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_LinearAlgebra_InverseProfile
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Module
open scoped Topology

namespace WeakMTWTransport
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] {n : ℕ}

lemma symmetric_eigenvalue_pos {A : E →ₗ[ℝ] E} (hA : A.IsSymmetric)
    (hn : finrank ℝ E=n) (hpos : ∀ x:E, x≠0 → 0 < inner ℝ (A x) x) (i:Fin n) :
    0 < hA.eigenvalues hn i := by
  have H := hpos (hA.eigenvectorBasis hn i) ((hA.eigenvectorBasis hn).toBasis.ne_zero i)
  rw [hA.apply_eigenvectorBasis,real_inner_smul_left,real_inner_self_eq_norm_sq,
    (hA.eigenvectorBasis hn).norm_eq_one] at H
  simpa using H
end WeakMTWTransport

end



end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Regularity_PullbackDet
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open Set
open scoped Topology

namespace WeakMTWTransport
section PullbackDet
variable {E F:Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F] [CompleteSpace E] [CompleteSpace F]

omit [CompleteSpace E] in
lemma symmetric_det_pos {A:E →L[ℝ] E}
    (hA:∀x y,inner ℝ (A x) y=inner ℝ x (A y))
    (hp:∀x,x≠0 → 0 < inner ℝ (A x) x) : 0<A.det := by
  have hs:A.toLinearMap.IsSymmetric:=hA
  change 0<A.toLinearMap.det
  rw [hs.det_eq_prod_eigenvalues rfl]
  exact Finset.prod_pos (fun i _=>symmetric_eigenvalue_pos hs rfl hp i)

end PullbackDet
end WeakMTWTransport

end
end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_LinearAlgebra_TrueCenterMatrix
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open Set Filter Manifold Bundle
open scoped Topology ContDiff

namespace WeakMTWTransport
section TrueCenterMatrix
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

attribute [local instance] OAI.WeakMTWTransport.tangentFiniteTrue
attribute [local instance] OAI.WeakMTWTransport.tangentCompleteTrue
omit [Nonempty M] [MeasurableSpace M] [BorelSpace M] in
lemma normal_contact_matrix_symmetric {u:M → ℝ} {y:M}
    {p:TangentSpace 𝓘(ℝ,Model n) y}
    {A:TangentSpace 𝓘(ℝ,Model n) y →L[ℝ] TangentSpace 𝓘(ℝ,Model n) y}
    (hA:NormalAlexandrovContact (n:=n) u y p A) :
    ∀d e,inner ℝ ((normalHessianOperator y p+A) d) e=
      inner ℝ d ((normalHessianOperator y p+A) e) := by
  intro d e
  simp only [add_apply,inner_add_left,inner_add_right,
    inner_normalHessianOperator,hA.2.2.1]
  rw [←real_inner_comm d (normalHessianOperator y p e),inner_normalHessianOperator,
    normalHessian_symm hA.2.1 d e]

end TrueCenterMatrix
end WeakMTWTransport

end
end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Oscillation_SectionOscillation
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set MeasureTheory Manifold Bundle
open scoped ContDiff Manifold ENNReal NNReal Topology

namespace WeakMTWTransport
open Matrix
open scoped MatrixOrder
open scoped BoundedContinuousFunction

section SectionOscillation
variable {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]

variable [MeasurableSpace M] [BorelSpace M]

omit [BorelSpace M] in
lemma densityDualClass_isDual {vol : Measure M} {lam cap : ℝ} {x0 : M}
    {uv : (M →ᵇ ℝ) × (M →ᵇ ℝ)} (h : uv ∈ densityDualClass vol lam cap x0) :
    IsCostDualPair uv.1 uv.2 := by
  constructor
  · exact congrArg (fun f : M →ᵇ ℝ => (f : M → ℝ)) h.1.2.1.symm
  · exact congrArg (fun f : M →ᵇ ℝ => (f : M → ℝ)) h.1.2.2.symm

end SectionOscillation

open Filter

end WeakMTWTransport
end
end
end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Volume_DensityOriginalJets
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff BoundedContinuousFunction

namespace WeakMTWTransport
section DensityOriginalJets
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]
local instance densityOriginalFinite (x:M) : FiniteDimensional ℝ (TangentSpace 𝓘(ℝ,Model n) x) :=
  inferInstanceAs (FiniteDimensional ℝ (Model n))

local instance densityOriginalComplete_r076506_1 (x:M) : CompleteSpace (TangentSpace 𝓘(ℝ,Model n) x) :=
  FiniteDimensional.complete ℝ _
omit [Nonempty M] [MeasurableSpace M] [BorelSpace M] in
lemma OriginalCenterGood.of_contact {u:M → ℝ} {χ:ℝ} {y:M}
    {p:TangentSpace 𝓘(ℝ,Model n) y}
    {A:TangentSpace 𝓘(ℝ,Model n) y →L[ℝ] TangentSpace 𝓘(ℝ,Model n) y}
    (hA:NormalAlexandrovContact (n:=n) u y p A)
    (hp:∀d,d≠0 → 0 < inner ℝ ((normalHessianOperator y p+A) d) d)
    (hlo:χ≤expJacobian y p*|(normalHessianOperator y p+A).det|) :
    OriginalCenterGood (n:=n) u χ y := by
  have hs : ∀d e,inner ℝ ((normalHessianOperator y p+A) d) e=
      inner ℝ d ((normalHessianOperator y p+A) e) := normal_contact_matrix_symmetric hA
  have hdet : 0 < (normalHessianOperator y p+A).det :=
    symmetric_det_pos (A:=normalHessianOperator y p+A) hs hp
  exact ⟨p,A,hA,hp,by simpa only [abs_of_pos hdet] using hlo⟩

lemma exists_density_original_center_good_oai {lam cap:ℝ} (hlam:0<lam) (hcap:lam ≤ cap) :
    ∃χ>0,∀(x0:M) (uv:(M →ᵇ ℝ)×(M →ᵇ ℝ)),
      uv∈densityDualClass (metricVolume n) lam cap x0 →
      ∀ᵐ y ∂metricVolume n,OriginalCenterGood (n:=n) uv.1 χ y := by
  obtain ⟨χ,_,hχ,_,H⟩:=minimizing_dualPair_uniform_intrinsic_cems (n:=n) (M:=M) hlam hcap
  refine ⟨χ,hχ,?_⟩
  intro x0 uv huv
  have hd:=densityDualClass_isDual huv
  obtain ⟨_,ρ0,ρ1,h0,h1,hmin⟩:=huv
  have Ha:=H ρ1 ρ0 h1 h0 uv.2 uv.1 ⟨hd.2,hd.1⟩ (dual_minimum_swap hmin)
  filter_upwards [Ha] with y hy
  obtain ⟨p,A,hA,hp,hlo,_⟩:=hy
  exact OriginalCenterGood.of_contact hA hp hlo
end DensityOriginalJets
end WeakMTWTransport

end
end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.WeakMTWTransport.exists_density_original_center_good_oai.{u_1} := @OAI.WeakMTWTransport.exists_density_original_center_good_oai.{u_1}
