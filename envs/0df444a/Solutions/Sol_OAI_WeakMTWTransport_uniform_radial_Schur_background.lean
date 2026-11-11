-- Prove2me | solution 1 for OAI.WeakMTWTransport.uniform_radial_Schur_background
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T19:32:07.266278+00:00
-- url     : https://prove2.me/submissions/01305c27-8a84-44d2-a19d-66b636656886

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
import Definitions.Def_OAIQ232A029

section
-- module Solutions.OAIQ232_BH.BiholderTransport_LinearAlgebra_HessianCoordinates
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set Filter Manifold Bundle ContinuousLinearMap
open scoped Topology ContDiff

namespace WeakMTWTransport
section HessianCoordinates
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma coordinateNormalCost_contDiffAt (c z : TangentBundle 𝓘(ℝ,Model n) M)
    (hz : z∈(extChartAt (𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n)) c).source)
    (hp : z.2∈injectivityDomain z.1) :
    ContDiffAt ℝ ∞ (coordinateNormalCost c)
      (extChartAt (𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n)) c z,0) := by
  let χ := extChartAt (𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n)) c
  let Q := (χ z,(0:Model n))
  let τ := trivializationAt (Model n) (fun x : M => TangentSpace 𝓘(ℝ,Model n) x) c.1
  let L := τ.continuousLinearEquivAt ℝ z.1 (by simpa only [τ,TangentBundle.trivializationAt_baseSet,extChartAt_source] using (tangent_chart_source_iff c z).mp hz)
  have hzero : χ.symm ((χ z).1,0)=(⟨z.1,0⟩ : TangentBundle 𝓘(ℝ,Model n) M) := by
    simpa only [map_zero] using tangent_chart_fiber_inverse c z hz (0:Model n)
  have hs0 : ((χ z).1,(0:Model n))∈χ.target := by
    have hf : χ (⟨z.1,0⟩ : TangentBundle 𝓘(ℝ,Model n) M)=((χ z).1,0) := by
      apply Prod.ext
      · rfl
      · change L 0=0
        exact map_zero _
    rw [←hf]
    exact χ.map_source ((tangent_chart_source_iff c _).mpr ((tangent_chart_source_iff c z).mp hz))
  have hχ0 : ContMDiffAt 𝓘(ℝ,Model n×Model n) (𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n)) ∞
      χ.symm ((χ z).1,0) :=
    (contMDiffOn_extChartAt_symm c).contMDiffAt ((isOpen_extChartAt_target c).mem_nhds hs0)
  have hχp : ContMDiffAt 𝓘(ℝ,Model n×Model n) (𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n)) ∞
      χ.symm (χ z) :=
    (contMDiffOn_extChartAt_symm c).contMDiffAt ((isOpen_extChartAt_target c).mem_nhds (χ.map_source hz))
  have hA := (contMDiff_riemannianExp.contMDiffAt.comp ((χ z).1,0) hχ0).comp Q
    ((contDiffAt_fst.fst.prodMk contDiffAt_snd).contMDiffAt)
  have hB := (contMDiff_riemannianExp.contMDiffAt.comp (χ z) hχp).comp Q
    contDiffAt_fst.contMDiffAt
  have hC := cost_contMDiffAt_of_injectivityDomain z hp
  have hC' : ContMDiffAt (𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n)) 𝓘(ℝ,ℝ) ∞
      (fun q : M×M => cost q.1 q.2)
      (riemannianExp (χ.symm ((χ z).1,0)).1 (χ.symm ((χ z).1,0)).2,
       riemannianExp (χ.symm (χ z)).1 (χ.symm (χ z)).2) := by
    rw [hzero,χ.left_inv hz,riemannianExp_zero]
    exact hC
  exact (hC'.comp Q (hA.prodMk hB)).contDiffAt

omit [CompactSpace M]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M] in
lemma coordinateNormalCost_slice (c z : TangentBundle 𝓘(ℝ,Model n) M)
    (hz : z∈(extChartAt (𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n)) c).source) :
    let χ := extChartAt (𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n)) c
    let τ := trivializationAt (Model n) (fun x : M => TangentSpace 𝓘(ℝ,Model n) x) c.1
    let L := τ.continuousLinearEquivAt ℝ z.1 (by simpa only [τ,TangentBundle.trivializationAt_baseSet,extChartAt_source] using (tangent_chart_source_iff c z).mp hz)
    (fun a => coordinateNormalCost c (χ z,a))=normalCost z.1 z.2 ∘ L.symm := by
  intro χ τ L
  funext a
  dsimp only [coordinateNormalCost]
  rw [tangent_chart_fiber_inverse c z hz a,χ.left_inv hz]
  rfl

lemma normalHessian_coordinate_form (c z : TangentBundle 𝓘(ℝ,Model n) M)
    (hz : z∈(extChartAt (𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n)) c).source)
    (hp : z.2∈injectivityDomain z.1) (v w : TangentSpace 𝓘(ℝ,Model n) z.1) :
    let χ := extChartAt (𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n)) c
    let τ := trivializationAt (Model n) (fun x : M => TangentSpace 𝓘(ℝ,Model n) x) c.1
    normalHessian z.1 z.2 v w=
      fderiv ℝ (fderiv ℝ (coordinateNormalCost c)) (χ z,0)
        (0,τ.continuousLinearMapAt ℝ z.1 v) (0,τ.continuousLinearMapAt ℝ z.1 w) := by
  intro χ τ
  let L := τ.continuousLinearEquivAt ℝ z.1 (by simpa only [τ,TangentBundle.trivializationAt_baseSet,extChartAt_source] using (tangent_chart_source_iff c z).mp hz)
  have hB := (coordinateNormalCost_contDiffAt c z hz hp).of_le
    (m := 2) (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  have H := second_derivative_target_slice hB (L v) (L w)
  rw [coordinateNormalCost_slice c z hz] at H
  have hs := (normalCost_contDiffAt hp).of_le
    (m := 2) (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  have hs' : ContDiffAt ℝ 2 (normalCost z.1 z.2) (L.symm (0:Model n)) := by
    simpa only [map_zero] using hs
  have HH := second_derivative_linear_sandwich (L.symm : Model n →L[ℝ] TangentSpace 𝓘(ℝ,Model n) z.1)
    (ContinuousLinearMap.id ℝ ℝ) hs' (L v) (L w)
  simp only [id_apply,map_zero] at HH
  change fderiv ℝ (fderiv ℝ (normalCost z.1 z.2 ∘ L.symm)) 0 (L v) (L w)=
    normalHessian z.1 z.2 (L.symm (L v)) (L.symm (L w)) at HH
  rw [L.symm_apply_apply,L.symm_apply_apply] at HH
  have Hfinal := HH.symm.trans H
  simpa only [L,Trivialization.coe_continuousLinearEquivAt_eq] using Hfinal

end HessianCoordinates
end WeakMTWTransport

end

end

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_LinearAlgebra_HessianBounds
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
open Set Filter Manifold Bundle ContinuousLinearMap
open scoped Topology ContDiff

namespace WeakMTWTransport
section HessianBounds
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma eventually_normalHessian_bounds {c : TangentBundle 𝓘(ℝ,Model n) M}
    (hc : c.2∈injectivityDomain c.1) :
    ∃ C : ℝ, 0<C ∧ ∀ᶠ z : TangentBundle 𝓘(ℝ,Model n) M in 𝓝 c,
      ∀ v w : TangentSpace 𝓘(ℝ,Model n) z.1,
      |normalHessian z.1 z.2 v w|≤C*‖v‖*‖w‖ := by
  have : IsContinuousRiemannianBundle (Model n) (fun x : M => TangentSpace 𝓘(ℝ,Model n) x) :=
    continuousRiemannianBundle_of_smooth (IB := 𝓘(ℝ,Model n))
  let χ := extChartAt (𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n)) c
  let U := trivializationAt (Model n) (fun x : M => TangentSpace 𝓘(ℝ,Model n) x) c.1
  let V := (Model n×Model n)×Model n
  let : NormedAddCommGroup V := inferInstanceAs (NormedAddCommGroup ((Model n×Model n)×Model n))
  let : NormedSpace ℝ V := inferInstanceAs (NormedSpace ℝ ((Model n×Model n)×Model n))
  let : NormedAddCommGroup (V →L[ℝ] ℝ) := inferInstance
  let : NormedSpace ℝ (V →L[ℝ] ℝ) := inferInstance
  let : NormedAddCommGroup (V →L[ℝ] V →L[ℝ] ℝ) := inferInstance
  let : SeminormedAddGroup (V →L[ℝ] V →L[ℝ] ℝ) := inferInstance
  let B : TangentBundle 𝓘(ℝ,Model n) M → (V →L[ℝ] V →L[ℝ] ℝ) := fun z =>
    fderiv ℝ (fderiv ℝ (coordinateNormalCost c)) (χ z,0)
  have hG := (coordinateNormalCost_contDiffAt c c (mem_extChartAt_source c) hc).of_le
    (m := 3) (ENat.natCast_le_of_coe_top_le_withTop le_rfl 3)
  have hD : ContinuousAt (fderiv ℝ (fderiv ℝ (coordinateNormalCost c))) (χ c,(0:Model n)) :=
    ((hG.fderiv_right (m := 2) (by norm_num)).fderiv_right
      (m := 1) (by norm_num)).continuousAt
  have hχ := (contMDiffAt_extChartAt (I := 𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n))
    (n := ∞) (x := c)).continuousAt
  have hmap : ContinuousAt (fun z : TangentBundle 𝓘(ℝ,Model n) M => (χ z,(0:Model n))) c :=
    hχ.prodMk continuousAt_const
  have hBc : ContinuousAt B c := ContinuousAt.comp
    (f := fun z : TangentBundle 𝓘(ℝ,Model n) M => (χ z,(0:Model n)))
    (g := fderiv ℝ (fderiv ℝ (coordinateNormalCost c))) hD hmap
  have hBb : ∀ᶠ z in 𝓝 c, ‖B z‖<‖B c‖+1 := hBc.norm.eventually
    (gt_mem_nhds (by linarith : ‖B c‖<‖B c‖+1))
  obtain ⟨CU,hCU,hUb⟩ := eventually_norm_trivializationAt_lt (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x) c.1
  have hproj : Continuous (fun z : TangentBundle 𝓘(ℝ,Model n) M => z.1) :=
    (Bundle.contMDiff_proj (n := ∞) (IB := 𝓘(ℝ,Model n)) (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)).continuous
  refine ⟨(‖B c‖+1)*CU*CU,by positivity,?_⟩
  filter_upwards [hBb,hproj.continuousAt.eventually hUb,
    extChartAt_source_mem_nhds (I := 𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n)) c,
    isOpen_total_injectivityDomain.mem_nhds hc] with z hz hU hzχ hzI
  intro v w
  rw [normalHessian_coordinate_form c z hzχ hzI v w]
  change ‖B z (0,U.continuousLinearMapAt ℝ z.1 v) (0,U.continuousLinearMapAt ℝ z.1 w)‖≤_
  have hv : ‖(U.continuousLinearMapAt ℝ z.1) v‖≤CU*‖v‖ :=
    ((U.continuousLinearMapAt ℝ z.1).le_opNorm v).trans
      (mul_le_mul_of_nonneg_right hU.le (norm_nonneg v))
  have hw : ‖(U.continuousLinearMapAt ℝ z.1) w‖≤CU*‖w‖ :=
    ((U.continuousLinearMapAt ℝ z.1).le_opNorm w).trans
      (mul_le_mul_of_nonneg_right hU.le (norm_nonneg w))
  have hv' : ‖((0:Model n×Model n),U.continuousLinearMapAt ℝ z.1 v)‖≤CU*‖v‖ := by simpa using hv
  have hw' : ‖((0:Model n×Model n),U.continuousLinearMapAt ℝ z.1 w)‖≤CU*‖w‖ := by simpa using hw
  calc
    _ ≤ ‖B z‖*‖(0,U.continuousLinearMapAt ℝ z.1 v)‖*‖(0,U.continuousLinearMapAt ℝ z.1 w)‖ :=
      ((B z _).le_opNorm _).trans (mul_le_mul_of_nonneg_right
        ((B z).le_opNorm _) (norm_nonneg _))
    _ ≤ (‖B c‖+1)*(CU*‖v‖)*(CU*‖w‖) :=
      mul_le_mul (mul_le_mul hz.le hv' (norm_nonneg _) (by positivity)) hw'
        (norm_nonneg _) (by positivity)
    _ = _ := by ring

lemma compact_normalHessian_bounds {K : Set (TangentBundle 𝓘(ℝ,Model n) M)}
    (hK : IsCompact K) (hI : ∀ z∈K, z.2∈injectivityDomain z.1) :
    ∃ C : ℝ, 0<C ∧ ∀ z∈K, ∀ v w : TangentSpace 𝓘(ℝ,Model n) z.1,
      |normalHessian z.1 z.2 v w|≤C*‖v‖*‖w‖ := by
  obtain ⟨r,C,hr,hC,H⟩ := compact_local_positive_bounds
    (P := fun (_ : ℝ) C z => ∀ v w : TangentSpace 𝓘(ℝ,Model n) z.1,
      |normalHessian z.1 z.2 v w|≤C*‖v‖*‖w‖) hK (by
        intro r R b B hr hrR hbB z hz v w
        exact (hz v w).trans (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hbB (norm_nonneg v)) (norm_nonneg w))) (by
        intro z hz
        obtain ⟨C,hC,H⟩ := eventually_normalHessian_bounds (hI z hz)
        exact ⟨1,C,by norm_num,hC,H⟩)
  exact ⟨C,hC,H⟩

lemma uniform_prefixHessian_bounds :
    ∃ C : ℝ, 0<C ∧ ∀ x : M, ∀ p : TangentSpace 𝓘(ℝ,Model n) x,
      p∈minimizingVectors x → ∀ t∈Icc (1/4:ℝ) (3/4),
      ∀ v w : TangentSpace 𝓘(ℝ,Model n) x,
      |normalHessian x (t • p) v w|≤C*‖v‖*‖w‖ := by
  let G := {z : TangentBundle 𝓘(ℝ,Model n) M | z.2∈minimizingVectors z.1}
  let S := Icc (1/4:ℝ) (3/4) ×ˢ G
  let P : ℝ × TangentBundle 𝓘(ℝ,Model n) M → TangentBundle 𝓘(ℝ,Model n) M :=
    fun q => tangentScale q.1 q.2
  have hP : Continuous P := contMDiff_tangentScale.continuous
  have hS : IsCompact S := isCompact_Icc.prod (isCompact_total_minimizingVectors (n := n) (M := M))
  obtain ⟨C,hC,H⟩ := compact_normalHessian_bounds (hS.image hP) (by
    intro w hw
    rcases hw with ⟨⟨t,z⟩,htz,rfl⟩
    exact contracted_minimizer_mem_injectivityDomain htz.2 (by linarith [htz.1.1])
      (by linarith [htz.1.2]))
  refine ⟨C,hC,?_⟩
  intro x p hp t ht
  exact H (P (t,⟨x,p⟩)) (mem_image_of_mem _ ⟨ht,hp⟩)

end HessianBounds
end WeakMTWTransport

end

end

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Regularity_SplitSelection
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set Filter Manifold Bundle ContinuousLinearMap
open scoped Topology ContDiff

namespace WeakMTWTransport
section SplitSelection
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma reverseRay_fraction_endpoint (z : TangentBundle 𝓘(ℝ,Model n) M) (t : ℝ) :
    riemannianExp (reverseRay z).1 ((1-t) • (reverseRay z).2)=
      riemannianExp z.1 (t • z.2) := by
  rw [riemannianExp_smul,riemannianExp_smul]
  change (sprayFlow (1-t) (tangentScale (-1) (sprayFlow 1 z))).1=(sprayFlow t z).1
  rw [sprayFlow_scale,←sprayFlow_add]
  change (sprayFlow ((-1:ℝ)*(1-t)+1) z).1=(sprayFlow t z).1
  rw [show (-1:ℝ)*(1-t)+1=t by ring]

lemma minimizing_reversed_split_action {y : M} {r : TangentSpace 𝓘(ℝ,Model n) y}
    (hr : r∈minimizingVectors y) {t : ℝ} (ht : 0<t) (ht1 : t<1) :
    cost (riemannianExp y r) (riemannianExp y ((1-t) • r))/t+
      cost (riemannianExp y ((1-t) • r)) y/(1-t)=cost (riemannianExp y r) y := by
  have H := splitNormalAction_contact hr (show 0<1-t by linarith) (show 1-t<1 by linarith)
  dsimp only [splitNormalAction,normalCost] at H
  rw [riemannianExp_zero,sub_sub_cancel] at H
  unfold cost at H ⊢
  rw [dist_comm (riemannianExp y r),dist_comm _ y,dist_comm (riemannianExp y r) y]
  linarith

lemma exists_split_minimizing_selection {x : M} {p : TangentSpace 𝓘(ℝ,Model n) x}
    (hp : p∈injectivityDomain x) {t : ℝ} (ht : 0<t) (ht1 : t<1) :
    ∃ a : TangentSpace 𝓘(ℝ,Model n) x → TangentSpace 𝓘(ℝ,Model n) x,
      a 0=p ∧ ContDiffAt ℝ ∞ a 0 ∧
      ∀ᶠ u in 𝓝 0, splitNormalAction x t p (u,a u)=normalCost x p u := by
  let : Nonempty M := ⟨x⟩
  let : MeasurableSpace M := borel M
  let : BorelSpace M := ⟨rfl⟩
  let X := TangentSpace 𝓘(ℝ,Model n) x
  let z : TangentBundle 𝓘(ℝ,Model n) M := ⟨x,p⟩
  let R := reverseRay z
  have hR : R.2∈injectivityDomain R.1 := reverseRay_injectivityDomain hp
  obtain ⟨q,hq0,hq,hqr,_⟩ := exists_normal_eikonal_log hR (reverseRay_endpoint z)
  have hprefix := contracted_minimizer_mem_injectivityDomain
    (injectivityDomain_subset_minimizingVectors x hp) ht ht1
  obtain ⟨κ,hκ0,hκ,hκright⟩ := exists_normal_local_inverse_at hprefix
  let J : X → M := fun u => riemannianExp R.1 ((1-t) • q u)
  have hJ0 : J 0=riemannianExp x (t • p) := by
    dsimp only [J]
    rw [hq0]
    exact reverseRay_fraction_endpoint z t
  have hJ : ContMDiffAt 𝓘(ℝ,X) 𝓘(ℝ,Model n) ∞ J 0 :=
    (contMDiff_riemannianExp_fiber R.1 _).comp 0 (hq.const_smul (1-t)).contMDiffAt
  let a : X → X := fun u => t⁻¹ • κ (J u)
  have ha : ContDiffAt ℝ ∞ a 0 := by
    apply ContDiffAt.const_smul
    apply ContMDiffAt.contDiffAt
    apply ContMDiffAt.comp 0 _ hJ
    rwa [hJ0]
  have ha0 : a 0=p := by
    dsimp only [a]
    rw [hJ0,hκ0,←mul_smul,inv_mul_cancel₀ ht.ne',one_smul]
  have hright : ∀ᶠ u in 𝓝 0, riemannianExp x (t • a u)=J u := by
    have H := hJ.continuousAt.eventually (by simpa only [hJ0] using hκright)
    filter_upwards [H] with u hu
    simpa only [a,←mul_smul,mul_inv_cancel₀ ht.ne',one_smul] using hu
  have hqI : ∀ᶠ u in 𝓝 0, q u∈injectivityDomain R.1 :=
    hq.continuousAt.preimage_mem_nhds ((isOpen_injectivityDomain R.1).mem_nhds (hq0.symm ▸ hR))
  refine ⟨a,ha0,ha,?_⟩
  filter_upwards [hright,hqr,hqI] with u hu hv hw
  have HE : R.1=riemannianExp x p := by
    change (sprayFlow 1 z).1=riemannianExp x p
    exact (riemannianExp_eq_sprayFlow x p).symm
  dsimp only [splitNormalAction,normalCost]
  rw [hu,←hv,←HE]
  exact minimizing_reversed_split_action (injectivityDomain_subset_minimizingVectors R.1 hw) ht ht1

end SplitSelection
end WeakMTWTransport

end

end

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_LinearAlgebra_SchurCalculus
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
open Set Filter ContinuousLinearMap
open scoped Topology ContDiff

namespace WeakMTWTransport
section SchurCalculus
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

lemma stationary_graph_hessian_identity {B : E×F → ℝ} {q : E → F} {p : E}
    (hB : ContDiffAt ℝ 2 B (p,q p)) (hq : DifferentiableAt ℝ q p)
    (hstat : ∀ᶠ a in 𝓝 p, ∀ k, fderiv ℝ B (a,q a) (0,k)=0)
    (v : E) (k : F) :
    fderiv ℝ (fderiv ℝ B) (p,q p) (0,fderiv ℝ q p v) (0,k)=
      -fderiv ℝ (fderiv ℝ B) (p,q p) (v,0) (0,k) := by
  have hdf := (hB.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hG := (hasFDerivAt_id (𝕜 := ℝ) p).prodMk hq.hasFDerivAt
  have hD := ((hdf.hasFDerivAt.comp (f := fun a => (a,q a)) p hG).clm_apply
    (hasFDerivAt_const ((0:E),k) p)).fderiv
  have heq : (fun a => fderiv ℝ B (a,q a) (0,k)) =ᶠ[𝓝 p] (fun _ => (0:ℝ)) :=
    hstat.mono (fun _ h => h k)
  have hz : fderiv ℝ (fun a => fderiv ℝ B (a,q a) (0,k)) p=0 := by
    rw [heq.fderiv_eq]
    exact (hasFDerivAt_const (0:ℝ) p).fderiv
  have H := congrArg (fun A : E →L[ℝ] ℝ => A v) (hD.symm.trans hz)
  simp only [add_apply,comp_apply,zero_apply,map_zero,zero_add,
    flip_apply,prod_apply,id_apply] at H
  rw [show (v,fderiv ℝ q p v)=(v,0)+((0:E),fderiv ℝ q p v) by ext <;> simp,
    map_add,add_apply] at H
  linarith

lemma stationary_graph_envelope_fderiv {B : E×F → ℝ} {q : E → F} {p : E}
    (hB : DifferentiableAt ℝ B (p,q p)) (hq : DifferentiableAt ℝ q p)
    (hstat : ∀ k, fderiv ℝ B (p,q p) (0,k)=0) :
    HasFDerivAt (fun a => B (a,q a)) ((fderiv ℝ B (p,q p)).comp (inl ℝ E F)) p := by
  apply (hB.hasFDerivAt.comp (f := fun a => (a,q a)) p
    ((hasFDerivAt_id (𝕜 := ℝ) p).prodMk hq.hasFDerivAt)).congr_fderiv
  ext v
  simp only [comp_apply,prod_apply,id_apply,inl_apply]
  rw [show (v,fderiv ℝ q p v)=(v,0)+((0:E),fderiv ℝ q p v) by ext <;> simp,
    map_add,hstat,add_zero]

lemma stationary_graph_schur_hessian {B : E×F → ℝ} {q : E → F} {p : E}
    (hB : ContDiffAt ℝ 2 B (p,q p)) (hq : ContDiffAt ℝ 1 q p)
    (hstat : ∀ᶠ a in 𝓝 p, ∀ k, fderiv ℝ B (a,q a) (0,k)=0)
    (v w : E) :
    fderiv ℝ (fderiv ℝ (fun a => B (a,q a))) p v w=
      fderiv ℝ (fderiv ℝ B) (p,q p) (v,0) (w,0)-
      fderiv ℝ (fderiv ℝ B) (p,q p) (0,fderiv ℝ q p v) (0,fderiv ℝ q p w) := by
  have hdq := hq.differentiableAt (by norm_num)
  have hdf := (hB.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hG := (hasFDerivAt_id (𝕜 := ℝ) p).prodMk hdq.hasFDerivAt
  have hBn := hG.continuousAt.eventually ((hB.of_le (m := 1) (by norm_num)).eventually (by norm_num))
  have hqn := hq.eventually (by norm_num)
  have heq : fderiv ℝ (fun a => B (a,q a)) =ᶠ[𝓝 p]
      (fun a => (fderiv ℝ B (a,q a)).comp (inl ℝ E F)) := by
    filter_upwards [hBn,hqn,hstat] with a ha hb hc
    exact (stationary_graph_envelope_fderiv (ha.differentiableAt (by norm_num))
      (hb.differentiableAt (by norm_num)) hc).fderiv
  have hD := (hdf.hasFDerivAt.comp (f := fun a => (a,q a)) p hG).clm_comp
    (hasFDerivAt_const (inl ℝ E F) p)
  have H := congrArg (fun A : E →L[ℝ] E →L[ℝ] ℝ => A v w)
    (heq.fderiv_eq.trans hD.fderiv)
  simp only [add_apply,comp_apply,zero_apply,map_zero,zero_add,
    flip_apply,prod_apply,id_apply,inl_apply,compL_apply] at H
  rw [show (v,fderiv ℝ q p v)=(v,0)+((0:E),fderiv ℝ q p v) by ext <;> simp,
    map_add,add_apply] at H
  have HS := stationary_graph_hessian_identity hB hdq hstat w (fderiv ℝ q p v)
  have hsym := (hB.isSymmSndFDerivAt (by norm_num)).eq
  rw [hsym (w,0) (0,fderiv ℝ q p v),
    hsym (0,fderiv ℝ q p w) (0,fderiv ℝ q p v)] at HS
  linarith

end SchurCalculus
end WeakMTWTransport

end

end

section

noncomputable section
open Set Filter Manifold Bundle ContinuousLinearMap
open scoped Topology ContDiff

namespace WeakMTWTransport
section SchurAction
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma fixedSplitAction_contDiffAt {x : M} {p : TangentSpace 𝓘(ℝ,Model n) x}
    (hp : p∈minimizingVectors x) {t : ℝ} (ht : 0<t) (ht1 : t<1) :
    ContDiffAt ℝ ∞ (splitNormalAction x t p) (0,p) := by
  have hleft := contracted_minimizer_mem_injectivityDomain hp ht ht1
  have hright := proper_suffix_in_injectivityDomain
    (z := (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M)) hp ht ht1 le_rfl
  exact (splitNormalAction_contDiffAt hleft hright).comp
    (f := fun q : TangentSpace 𝓘(ℝ,Model n) x × TangentSpace 𝓘(ℝ,Model n) x => (p,q)) (0,p)
    (contDiffAt_const.prodMk contDiffAt_id)

lemma fixedSplitAction_source_hessian {x : M} {p : TangentSpace 𝓘(ℝ,Model n) x}
    (hp : p∈minimizingVectors x) {t : ℝ} (ht : 0<t) (ht1 : t<1)
    (v : TangentSpace 𝓘(ℝ,Model n) x) :
    fderiv ℝ (fderiv ℝ (splitNormalAction x t p)) (0,p) (v,0) (v,0)=
      normalHessian x (t • p) v v/t := by
  have hB := fixedSplitAction_contDiffAt hp ht ht1
  have H := iteratedDeriv_two_affine_line
    (hB.of_le (m := 2) (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)) (v,0)
  simp only [splitNormalAction,Prod.fst_add,Prod.smul_fst,Prod.snd_add,Prod.smul_snd,
    zero_add,smul_zero,add_zero] at H
  conv_lhs at H => arg 2; ext r; rw [add_comm]
  rw [iteratedDeriv_const_add (by norm_num : 0<(2:ℕ)),iteratedDeriv_div_const] at H
  rw [←H,←hessianValue_eq_normalHessian (contracted_minimizer_mem_injectivityDomain hp ht ht1)]
  rfl

lemma exists_splitAction_schur_operator {x : M} {p : TangentSpace 𝓘(ℝ,Model n) x}
    (hp : p∈injectivityDomain x) {t : ℝ} (ht : 0<t) (ht1 : t<1) :
    ∃ K : TangentSpace 𝓘(ℝ,Model n) x →L[ℝ] TangentSpace 𝓘(ℝ,Model n) x,
      Function.Bijective K ∧ (∀ v w, inner ℝ (K v) w=inner ℝ v (K w)) ∧
      (∀ v, 0≤ inner ℝ (K v) v) ∧
      (∀ v k, fderiv ℝ (fderiv ℝ (splitNormalAction x t p)) (0,p) (0,K v) (0,k)=inner ℝ k v) ∧
      ∀ v, normalHessian x p v v=normalHessian x (t • p) v v/t-inner ℝ (K v) v := by
  let X := TangentSpace 𝓘(ℝ,Model n) x
  let : FiniteDimensional ℝ X := inferInstanceAs (FiniteDimensional ℝ (Model n))
  let B := splitNormalAction x t p
  have hpG := injectivityDomain_subset_minimizingVectors x hp
  have hSmooth := fixedSplitAction_contDiffAt hpG ht ht1
  have hB : ContDiffAt ℝ 2 B (0,p) :=
    hSmooth.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  have hleft := contracted_minimizer_mem_injectivityDomain hpG ht ht1
  have hright := proper_suffix_in_injectivityDomain
    (z := (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M)) hpG ht ht1 le_rfl
  obtain ⟨a,ha0,ha,he⟩ := exists_split_minimizing_selection hp ht ht1
  have hG : ContinuousAt (fun u => (u,a u)) (0:X) := continuousAt_id.prodMk ha.continuousAt
  have hBn : ∀ᶠ u in 𝓝 (0:X), DifferentiableAt ℝ B (u,a u) := by
    apply (hG.eventually (show ∀ᶠ z in 𝓝 ((0:X),a 0), ContDiffAt ℝ 2 B z from by
      rw [ha0]; exact hB.eventually (by norm_num))).mono
    exact fun u hu => hu.differentiableAt (by norm_num)
  have hstat : ∀ᶠ u in 𝓝 (0:X), ∀ k, fderiv ℝ B (u,a u) (0,k)=0 := by
    filter_upwards [he,hBn] with u hu hbu
    have hmin : IsLocalMin (fun v => B (u,v)) (a u) := by
      filter_upwards [] with v
      change splitNormalAction x t p (u,a u)≤ splitNormalAction x t p (u,v)
      rw [hu]
      exact normalCost_le_splitNormalAction x p u v ht ht1
    have hD := hbu.hasFDerivAt.comp (f := fun v => (u,v)) (a u)
      ((hasFDerivAt_const u (a u)).prodMk (hasFDerivAt_id (𝕜 := ℝ) (a u)))
    have hz := hmin.hasFDerivAt_eq_zero hD
    intro k
    exact congrArg (fun L : X →L[ℝ] ℝ => L k) hz
  let K := fderiv ℝ a 0
  have hBa : ContDiffAt ℝ 2 B (0,a 0) := by rwa [ha0]
  have hInv (v k : X) : fderiv ℝ (fderiv ℝ B) (0,p) (0,K v) (0,k)=inner ℝ k v := by
    have H := stationary_graph_hessian_identity hBa (ha.differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)) hstat v k
    rw [ha0,splitNormalAction_mixed_pairing ht.ne' hleft hright] at H
    simpa only [neg_neg] using H
  have hKinj : Function.Injective K := by
    apply (injective_iff_map_eq_zero K).mpr
    intro v hv
    have H := hInv v v
    rw [hv,show ((0:X),(0:X))=0 from rfl,map_zero,zero_apply] at H
    exact inner_self_eq_zero.mp H.symm
  have hKsurj : Function.Surjective K :=
    (LinearMap.injective_iff_surjective (f := K.toLinearMap)).mp hKinj
  have hsym := (hB.isSymmSndFDerivAt (by norm_num)).eq
  have hKs (v w : X) : inner ℝ (K v) w=inner ℝ v (K w) := by
    have H := hsym (0,K v) (0,K w)
    rw [hInv,hInv] at H
    exact H.symm.trans (real_inner_comm _ _)
  have hKn (v : X) : 0≤ inner ℝ (K v) v := by
    have hmin : IsLocalMin (fun k : X => B (0,k)) p := by
      filter_upwards [] with k
      change splitNormalAction x t p (0,p)≤ splitNormalAction x t p (0,k)
      rw [splitNormalAction_contact hpG ht ht1]
      exact normalCost_le_splitNormalAction x p 0 k ht ht1
    have HC := hB.comp p (contDiffAt_const.prodMk contDiffAt_id)
    have H := localMin_hessian_nonneg HC hmin (K v)
    change 0 ≤ fderiv ℝ (fderiv ℝ (fun k : X => B (0,k))) p (K v) (K v) at H
    rw [second_derivative_target_slice hB,hInv] at H
    exact H
  refine ⟨K,⟨hKinj,hKsurj⟩,hKs,hKn,hInv,?_⟩
  intro v
  have H := stationary_graph_schur_hessian hBa
    (ha.of_le (m := 1) (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)) hstat v v
  rw [ha0,fixedSplitAction_source_hessian hpG ht ht1,hInv] at H
  have heq : (fun u => B (u,a u)) =ᶠ[𝓝 (0:X)] normalCost x p := he
  have heDD := (heq.fderiv (𝕜 := ℝ)).fderiv_eq (𝕜 := ℝ)
  rw [heDD] at H
  exact H

end SchurAction
end WeakMTWTransport

end

end

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_LinearAlgebra_ShearConvexity
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
section ShearConvexity
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

omit [CompactSpace M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)] [IsRiemannianManifold 𝓘(ℝ,Model n) M] in
lemma radialHessianDefect_apply (x : M) (p : TangentSpace 𝓘(ℝ,Model n) x)
    (δ : ℝ) (u v : TangentSpace 𝓘(ℝ,Model n) x) :
    radialHessianDefectBilinear x p δ u v =
      -δ*(normalHessian x ((1-δ) • p) u v-inner ℝ u v) := rfl

end ShearConvexity
end WeakMTWTransport

end

end

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_LinearAlgebra_SchurBackground
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
open Set Filter Manifold Bundle ContinuousLinearMap
open scoped Topology ContDiff

namespace WeakMTWTransport
section SchurBackground
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma splitJoinHessianOperator_pairing_fixed {x : M}
    {p : TangentSpace 𝓘(ℝ,Model n) x} (hp : p∈minimizingVectors x)
    {t : ℝ} (ht : 0<t) (ht1 : t<1) (a k : TangentSpace 𝓘(ℝ,Model n) x) :
    inner ℝ (splitJoinHessianOperator x t p a) k=
      fderiv ℝ (fderiv ℝ (splitNormalAction x t p)) (0,p) (0,a) (0,k) := by
  rw [inner_splitJoinHessianOperator]
  have hleft := contracted_minimizer_mem_injectivityDomain hp ht ht1
  have hright := proper_suffix_in_injectivityDomain
    (z := (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M)) hp ht ht1 le_rfl
  have hD := (diagonalSplitAction_contDiffAt hleft hright).of_le
    (m := 2) (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  have hB := (fixedSplitAction_contDiffAt hp ht ht1).of_le
    (m := 2) (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  rw [←second_derivative_target_slice hD,←second_derivative_target_slice hB]
  rfl

lemma schur_operator_inverse {x : M} {p : TangentSpace 𝓘(ℝ,Model n) x}
    (hp : p∈minimizingVectors x) {t : ℝ} (ht : 0<t) (ht1 : t<1)
    (K : TangentSpace 𝓘(ℝ,Model n) x →L[ℝ] TangentSpace 𝓘(ℝ,Model n) x)
    (hK : ∀ v k, fderiv ℝ (fderiv ℝ (splitNormalAction x t p)) (0,p) (0,K v) (0,k)=inner ℝ k v) :
    ∀ v, splitJoinHessianOperator x t p (K v)=v := by
  intro v
  apply ext_inner_right ℝ
  intro k
  rw [splitJoinHessianOperator_pairing_fixed hp ht ht1,hK,real_inner_comm]

lemma uniform_radial_Schur_background_oai :
    ∃ C : ℝ, 0<C ∧ ∀ x : M, ∀ p : TangentSpace 𝓘(ℝ,Model n) x,
      p∈minimizingVectors x → ∀ δ∈Ioc (0:ℝ) (1/2),
      ∃ K : TangentSpace 𝓘(ℝ,Model n) x →L[ℝ] TangentSpace 𝓘(ℝ,Model n) x,
        Function.Bijective K ∧ K.toLinearMap.IsPositive ∧
        (∀ v, splitJoinHessianOperator x (1/2) ((1-δ) • p) (K v)=v) ∧
        (∀ v, radialHessianDefectBilinear x p δ v v=δ*inner ℝ (K v) v+
          δ*(‖v‖^2-2*normalHessian x (((1-δ)/2) • p) v v)) ∧
        ∀ v, |radialHessianDefectBilinear x p δ v v-δ*inner ℝ (K v) v|≤C*δ*‖v‖^2 := by
  obtain ⟨C,hC,H⟩ := uniform_prefixHessian_bounds (n := n) (M := M)
  refine ⟨1+2*C,by positivity,?_⟩
  intro x p hp δ hd
  have hI := contracted_minimizer_mem_injectivityDomain hp
    (show 0<1-δ by linarith [hd.2]) (show 1-δ<1 by linarith [hd.1])
  obtain ⟨K,hK,hKs,hKn,hInv,hS⟩ := exists_splitAction_schur_operator hI
    (show (0:ℝ)<1/2 by norm_num) (show (1/2:ℝ)<1 by norm_num)
  have hKpos : K.toLinearMap.IsPositive := ⟨hKs,hKn⟩
  have hEq (v : TangentSpace 𝓘(ℝ,Model n) x) :
      radialHessianDefectBilinear x p δ v v=δ*inner ℝ (K v) v+
        δ*(‖v‖^2-2*normalHessian x (((1-δ)/2) • p) v v) := by
    rw [radialHessianDefect_apply,hS,smul_smul,real_inner_self_eq_norm_sq]
    have he : (1/2:ℝ)*(1-δ)=(1-δ)/2 := by ring
    rw [he]
    ring
  refine ⟨K,hK,hKpos,schur_operator_inverse
    (injectivityDomain_subset_minimizingVectors x hI) (by norm_num) (by norm_num) K hInv,hEq,?_⟩
  intro v
  rw [hEq,add_sub_cancel_left,abs_mul,abs_of_pos hd.1]
  have hB := H x p hp ((1-δ)/2) (by constructor <;> linarith [hd.1,hd.2]) v v
  have htri := abs_sub (‖v‖^2) (2*normalHessian x (((1-δ)/2) • p) v v)
  rw [abs_of_nonneg (sq_nonneg ‖v‖),abs_mul,abs_of_pos (by norm_num : (0:ℝ)<2)] at htri
  have hB' : |‖v‖^2-2*normalHessian x (((1-δ)/2) • p) v v|≤(1+2*C)*‖v‖^2 := by
    nlinarith
  have HH := mul_le_mul_of_nonneg_left hB' hd.1.le
  nlinarith only [HH]

end SchurBackground
end WeakMTWTransport

end

end

end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.WeakMTWTransport.uniform_radial_Schur_background_oai.{u_1} := @OAI.WeakMTWTransport.uniform_radial_Schur_background_oai.{u_1}
