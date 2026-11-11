-- Prove2me | solution 1 for OAI.WeakMTWTransport.cTransform_ae_normal_quadraticExpansion
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T19:26:42.515915+00:00
-- url     : https://prove2.me/submissions/769bb106-37b7-464d-8d06-588b10a5a664

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
import Definitions.Def_OAIQ232A025
import Definitions.Def_OAIQ232A026

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Contact_CompactMinty
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
open Set Filter
open scoped Topology

namespace WeakMTWTransport
section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma convexOn_of_linear_lower_support {u : E → ℝ} {S : Set E}
    (hS : Convex ℝ S)
    (h : ∀ x∈S, ∃ l : E →L[ℝ] ℝ, ∀ y∈S, u x+l (y-x) ≤ u y) :
    ConvexOn ℝ S u := by
  refine ⟨hS,?_⟩
  intro x hx y hy a b ha hb hab
  obtain ⟨l,hl⟩ := h (a • x+b • y) (hS hx hy ha hb hab)
  have H₁ := mul_le_mul_of_nonneg_left (hl x hx) ha
  have H₂ := mul_le_mul_of_nonneg_left (hl y hy) hb
  have he : a*l (x-(a • x+b • y))+b*l (y-(a • x+b • y)) = 0 := by
    change a • l (x-(a • x+b • y))+b • l (y-(a • x+b • y)) = 0
    rw [← map_smul,← map_smul,← map_add]
    have hz : a • (x-(a • x+b • y))+b • (y-(a • x+b • y)) = 0 := by
      rw [smul_sub,smul_sub]
      calc
        _ = (a • x+b • y)-(a • (a • x+b • y)+b • (a • x+b • y)) := by abel
        _ = 0 := by rw [← add_smul,hab,one_smul,sub_self]
    rw [hz,map_zero]
  simp only [smul_eq_mul]
  have habu := congrArg (fun t : ℝ => t * u (a • x+b • y)) hab
  nlinarith only [H₁,H₂,he,habu]

lemma convexOn_of_quadratic_lower_support {u : E → ℝ} {S : Set E} {K : ℝ}
    (hS : Convex ℝ S)
    (h : ∀ x∈S, ∃ l : E →L[ℝ] ℝ, ∀ y∈S, u x+l (y-x)-K*‖y-x‖^2 ≤ u y) :
    ConvexOn ℝ S (fun z => u z+K*‖z‖^2) := by
  apply convexOn_of_linear_lower_support hS
  intro x hx
  obtain ⟨l,hl⟩ := h x hx
  refine ⟨l+(2*K) • innerSL ℝ x,?_⟩
  intro y hy
  have H := hl y hy
  have hn : ‖y‖^2-‖x‖^2-2*inner ℝ x (y-x)=‖y-x‖^2 := by
    simp only [← real_inner_self_eq_norm_sq,inner_sub_left,inner_sub_right,real_inner_comm y x]
    ring
  simp only [add_apply,smul_apply,innerSL_apply_apply,smul_eq_mul]
  have hnK := congrArg (fun t : ℝ => K*t) hn
  nlinarith only [H,hnK]

end
section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma c2_quadratic_remainder_on_convex {f : E → ℝ} {S : Set E} {K : ℝ}
    (hK : 0≤K) (hS : Convex ℝ S) (hf : ∀ z∈S, ContDiffAt ℝ 2 f z)
    (hbound : ∀ z∈S, ‖fderiv ℝ (fderiv ℝ f) z‖≤K) {x y : E} (hx : x∈S) (hy : y∈S) :
    ‖f y-f x-fderiv ℝ f x (y-x)‖ ≤ K*‖y-x‖^2 := by
  have hd (z) (hz : z∈S) : DifferentiableAt ℝ (fderiv ℝ f) z :=
    ((hf z hz).fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hseg : segment ℝ x y ⊆ S := hS.segment_subset hx hy
  have hball : segment ℝ x y ⊆ Metric.closedBall x ‖y-x‖ :=
    (convex_closedBall x ‖y-x‖).segment_subset (by simp only [Metric.mem_closedBall,dist_self] <;> positivity)
      (by simp only [Metric.mem_closedBall,dist_eq_norm,le_refl])
  have hdif (z) (hz : z∈segment ℝ x y) : ‖fderiv ℝ f z-fderiv ℝ f x‖≤K*‖y-x‖ := by
    calc
      _ ≤ K*‖z-x‖ := hS.norm_image_sub_le_of_norm_fderiv_le hd hbound hx (hseg hz)
      _ ≤ K*‖y-x‖ := mul_le_mul_of_nonneg_left (by
        simpa only [Metric.mem_closedBall,dist_eq_norm] using hball hz) hK
  have H := (convex_segment x y).norm_image_sub_le_of_norm_fderiv_le'
    (fun z hz => (hf z (hseg hz)).differentiableAt (by norm_num)) hdif
    (left_mem_segment ℝ x y) (right_mem_segment ℝ x y)
  simpa only [mul_assoc,← sq] using H

end
end WeakMTWTransport

end

end

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Regularity_ContDiffParametricQuadratic
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
open Set Filter
open scoped Topology ContDiff

namespace WeakMTWTransport
section
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

lemma contDiffAt_parametric_quadratic_upper {f : E×F → ℝ} {x : E} {a : F}
    (hf : ContDiffAt ℝ ∞ f (x,a)) :
    ∃ δ>0, ∃ K>0, ∀ z∈Metric.ball x δ, ∀ w∈Metric.ball x δ,
      ∀ b∈Metric.ball a δ,
        f (w,b)-f (z,b)-fderiv ℝ f (z,b) (w-z,0) ≤ K*‖w-z‖^2 := by
  let K := ‖fderiv ℝ (fderiv ℝ f) (x,a)‖+1
  have hK : 0<K := by dsimp [K] <;> positivity
  have hc : ContinuousAt (fun q => ‖fderiv ℝ (fderiv ℝ f) q‖) (x,a) :=
    ((hf.fderiv_right (m := 2) (ENat.natCast_le_of_coe_top_le_withTop le_rfl 3)).continuousAt_fderiv (by norm_num)).norm
  have hf2 : ContDiffAt ℝ 2 f (x,a) := hf.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  have hk : ‖fderiv ℝ (fderiv ℝ f) (x,a)‖<K := by dsimp [K] <;> linarith
  have he : ∀ᶠ q in 𝓝 (x,a), ContDiffAt ℝ 2 f q ∧
      ‖fderiv ℝ (fderiv ℝ f) q‖<K :=
    (hf2.eventually (by norm_num)).and (hc.preimage_mem_nhds (Iio_mem_nhds hk))
  obtain ⟨δ,hδ,hbound⟩ := Metric.mem_nhds_iff.mp he
  refine ⟨δ,hδ,K,hK,?_⟩
  intro z hz w hw b hb
  have hzb : (z,b)∈Metric.ball (x,a) δ := by
    simpa only [Metric.mem_ball,Prod.dist_eq,max_lt_iff] using And.intro hz hb
  have hwb : (w,b)∈Metric.ball (x,a) δ := by
    simpa only [Metric.mem_ball,Prod.dist_eq,max_lt_iff] using And.intro hw hb
  have H := c2_quadratic_remainder_on_convex hK.le (convex_ball (x,a) δ)
    (fun q hq => (hbound hq).1) (fun q hq => (hbound hq).2.le) hzb hwb
  have H' := (abs_le.mp (show |f (w,b)-f (z,b)-fderiv ℝ f (z,b) ((w,b)-(z,b))|
      ≤ K*‖(w,b)-(z,b)‖^2 from H)).2
  simpa only [Prod.mk_sub_mk,sub_self,Prod.norm_def,norm_zero,max_eq_left (norm_nonneg _)] using H'

end
end WeakMTWTransport

end

end

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Contact_CoordinateSupport
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
open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

namespace WeakMTWTransport
section CoordinateSupport
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma smooth_coordinate_half_cost_quadratic {A : Type*} [TopologicalSpace A]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {ψ : E → M} (hψ : ContMDiffAt 𝓘(ℝ,E) 𝓘(ℝ,Model n) ∞ ψ 0)
    {Y : A → M} {a : A} (hY : ContinuousAt Y a) {x : M} (hx : ψ 0=x)
    {p : TangentSpace 𝓘(ℝ,Model n) x} (hp : p∈minimizingVectors x)
    (hya : Y a=riemannianExp x ((1/2:ℝ) • p)) :
    ∃ δ>0, ∃ K>0, ∀ᶠ b in 𝓝 a,
      ∀ z∈Metric.ball (0:E) δ,
        ∃ l : E →L[ℝ] ℝ,
          ∀ w∈Metric.ball (0:E) δ,
            2*(cost (ψ w) (Y b)-cost (ψ z) (Y b))-
              l (w-z) ≤ K*‖w-z‖^2 := by
  let y := riemannianExp x ((1/2:ℝ) • p)
  let d := extChartAt 𝓘(ℝ,Model n) y
  have hyS : y∈d.source := mem_extChartAt_source y
  have hyT : d y∈d.target := d.map_source hyS
  have hdy : d.symm (d y)=y := d.left_inv hyS
  have hID := contracted_minimizer_mem_injectivityDomain hp
    (show (0:ℝ)<1/2 by norm_num) (show (1/2:ℝ)<1 by norm_num)
  let F := fun q : E×Model n => (2:ℝ)*cost (ψ q.1) (d.symm q.2)
  have hA : ContMDiffAt 𝓘(ℝ,E×Model n) 𝓘(ℝ,Model n) ∞
      (fun q : E×Model n => ψ q.1) (0,d y) :=
    hψ.comp (0,d y) contDiffAt_fst.contMDiffAt
  have hB : ContMDiffAt 𝓘(ℝ,E×Model n) 𝓘(ℝ,Model n) ∞
      (fun q : E×Model n => d.symm q.2) (0,d y) :=
    ((contMDiffWithinAt_extChartAt_symm_target y hyT).contMDiffAt
      ((isOpen_extChartAt_target y).mem_nhds hyT)).comp (0,d y) contDiffAt_snd.contMDiffAt
  have hC := cost_contMDiffAt_of_injectivityDomain
    (⟨x,(1/2:ℝ) • p⟩ : TangentBundle 𝓘(ℝ,Model n) M) hID
  have hC' : ContMDiffAt (𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n)) 𝓘(ℝ,ℝ) ∞
      (fun q : M×M => cost q.1 q.2) (ψ (0:E),d.symm (d y)) := by
    simpa only [hx,hdy] using hC
  have hF0 := hC'.comp (0,d y) (hA.prodMk hB)
  have hF : ContDiffAt ℝ ∞ F (0,d y) := by
    simpa only [Function.comp_def] using contDiffAt_const.mul hF0.contDiffAt
  obtain ⟨δ,hδ,K,hK,H⟩ := contDiffAt_parametric_quadratic_upper hF
  have hc : ContinuousAt (fun b => d (Y b)) a :=
    (show ContinuousAt d (Y a) by rw [hya]; exact continuousAt_extChartAt y).comp hY
  have hdY : ∀ᶠ b in 𝓝 a, d (Y b)∈Metric.ball (d y) δ := by
    apply hc.preimage_mem_nhds
    apply Metric.isOpen_ball.mem_nhds
    simpa only [hya,Metric.mem_ball,y,dist_self] using hδ
  have hsrc : ∀ᶠ b in 𝓝 a, Y b∈d.source :=
    hY.preimage_mem_nhds ((isOpen_extChartAt_source y).mem_nhds (hya.symm ▸ hyS))
  refine ⟨δ,hδ,K,hK,?_⟩
  filter_upwards [hdY,hsrc] with b hb hbs
  intro z hz
  refine ⟨(fderiv ℝ F (z,d (Y b))).comp (ContinuousLinearMap.inl ℝ E (Model n)),?_⟩
  intro w hw
  have HH := H z hz w hw (d (Y b)) hb
  dsimp only [F] at HH
  rw [d.left_inv hbs] at HH
  change 2*(cost (ψ w) (Y b)-cost (ψ z) (Y b))-
    (fderiv ℝ F (z,d (Y b))) (w-z,0) ≤ K*‖w-z‖^2
  change 2*cost (ψ w) (Y b)-2*cost (ψ z) (Y b)-
    (fderiv ℝ F (z,d (Y b))) (w-z,0) ≤ K*‖w-z‖^2 at HH
  simpa only [mul_sub] using HH

end CoordinateSupport
end WeakMTWTransport

end

end

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Contact_Subgradient
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

open Set Filter
open scoped Topology NNReal

namespace WeakMTWTransport
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma convex_lipschitz_extension {f : E → ℝ} {s : Set E} {L : ℝ≥0}
    (hc : ConvexOn ℝ s f) (hlip : LipschitzOnWith L f s) (hs : s.Nonempty) :
    ∃ g : E → ℝ, LipschitzWith L g ∧ ConvexOn ℝ univ g ∧ EqOn f g s := by
  have : Nonempty s := hs.to_subtype
  let g := fun y : E => ⨅ x : s, f x + L * dist y x
  have hB : ∀ y : E, BddBelow (range fun x : s => f x + L * dist y x) := by
    intro y
    obtain ⟨z,hz⟩ := hs
    refine ⟨f z - L*dist y z, ?_⟩
    rintro w ⟨t,rfl⟩
    dsimp
    rw [sub_le_iff_le_add,add_assoc,← mul_add,add_comm (dist y t)]
    calc
      f z ≤ f t + L * dist z t := hlip.le_add_mul hz t.2
      _ ≤ f t + L*(dist y z + dist y t) := by
        gcongr
        exact dist_triangle_left _ _ _
  have hEq : EqOn f g s := by
    intro x hx
    refine le_antisymm (le_ciInf fun y => hlip.le_add_mul hx y.2) ?_
    simpa only [add_zero,Subtype.coe_mk,mul_zero,dist_self] using ciInf_le (hB x) ⟨x,hx⟩
  have hgL : LipschitzWith L g := by
    apply LipschitzWith.of_le_add_mul L
    intro x y
    rw [← sub_le_iff_le_add]
    refine le_ciInf fun z => ?_
    rw [sub_le_iff_le_add]
    calc
      g x ≤ f z + L*dist x z := ciInf_le (hB x) _
      _ ≤ f z + L*dist y z + L*dist x y := by
        rw [add_assoc,← mul_add,add_comm (dist y z)]
        gcongr
        exact dist_triangle _ _ _
  refine ⟨g,hgL,⟨convex_univ,?_⟩,hEq⟩
  intro x _ y _ a b ha hb hab
  simp only [smul_eq_mul]
  apply le_of_forall_pos_le_add
  intro eps heps
  obtain ⟨u,hu⟩ : ∃ u : s, f u + L*dist x u < g x + eps :=
    exists_lt_of_ciInf_lt (by dsimp [g]; linarith : g x < g x + eps)
  obtain ⟨v,hv⟩ : ∃ v : s, f v + L*dist y v < g y + eps :=
    exists_lt_of_ciInf_lt (by dsimp [g]; linarith : g y < g y + eps)
  have huv : a • (u:E) + b • (v:E) ∈ s := hc.1 u.2 v.2 ha hb hab
  have hcf := hc.2 u.2 v.2 ha hb hab
  have hdist : dist (a • x+b • y) (a • (u:E)+b • (v:E)) ≤
      a*dist x u + b*dist y v := by
    rw [dist_eq_norm,dist_eq_norm,dist_eq_norm]
    have heq : a • x+b • y-(a • (u:E)+b • (v:E)) =
      a • (x-u) + b • (y-v) := by simp only [smul_sub]; abel
    rw [heq]
    calc
      ‖a • (x-u)+b • (y-v)‖ ≤ ‖a • (x-u)‖+‖b • (y-v)‖ := norm_add_le _ _
      _ = a*‖x-u‖+b*‖y-v‖ := by rw [norm_smul_of_nonneg ha,norm_smul_of_nonneg hb]
  calc
    g (a • x+b • y) ≤ f (a • (u:E)+b • (v:E)) +
        L*dist (a • x+b • y) (a • (u:E)+b • (v:E)) :=
      ciInf_le (hB _) ⟨_,huv⟩
    _ ≤ a*f u+b*f v + L*(a*dist x u+b*dist y v) := by
      exact add_le_add hcf (mul_le_mul_of_nonneg_left hdist L.coe_nonneg)
    _ = a*(f u+L*dist x u)+b*(f v+L*dist y v) := by ring
    _ ≤ a*(g x+eps)+b*(g y+eps) := add_le_add
      (mul_le_mul_of_nonneg_left hu.le ha) (mul_le_mul_of_nonneg_left hv.le hb)
    _ = a*g x+b*g y+eps := by nlinarith [hab]

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

namespace ConvexProximal

lemma norm_sq_add_real (a b : E) :
    ‖a+b‖^2 = ‖a‖^2 + 2 * inner ℝ a b + ‖b‖^2 := by
  simp only [← real_inner_self_eq_norm_sq, inner_add_left, inner_add_right]
  rw [real_inner_comm b a]
  ring

lemma energy_increment (f : E → ℝ) (y x v : E) (t : ℝ) :
    energy f y (x + t • (v-x)) - energy f y x =
      f (x + t • (v-x)) - f x +
        t * inner ℝ (x-y) (v-x) + t^2/2*‖v-x‖^2 := by
  have heq : x + t • (v-x) - y = (x-y) + t • (v-x) := by abel
  simp only [energy, heq, norm_sq_add_real, real_inner_smul_right, norm_smul,
    mul_pow, Real.norm_eq_abs, sq_abs]
  ring

lemma subgradient_iff_minimizer {f : E → ℝ} (hf : ConvexOn ℝ univ f) (y x : E) :
    IsSubgradientOn f univ x (y-x) ↔ ∀ v, energy f y x ≤ energy f y v := by
  constructor
  · intro hs v
    have hh := hs v (mem_univ _)
    have hi := energy_increment f y x v 1
    have heq : x + (1:ℝ) • (v-x) = v := by simp
    rw [heq] at hi
    have hí : inner ℝ (y-x) (v-x) = -inner ℝ (x-y) (v-x) := by
      rw [← neg_sub x y, inner_neg_left]
    rw [hí] at hh
    nlinarith [sq_nonneg ‖v-x‖]
  · intro hm v _
    have hb (t : ℝ) (ht : t ∈ Ioo 0 1) :
        f x + inner ℝ (y-x) (v-x) ≤ f v + t/2*‖v-x‖^2 := by
      have hc := hf.2 (mem_univ x) (mem_univ v) (by linarith [ht.2] : 0 ≤ 1-t)
        ht.1.le (by ring : 1-t+t=1)
      have heq : (1-t) • x + t • v = x + t • (v-x) := by
        simp only [sub_smul, one_smul, smul_sub]
        abel
      rw [heq] at hc
      have hi := energy_increment f y x v t
      have hlo := hm (x + t • (v-x))
      have hinner : inner ℝ (y-x) (v-x) = -inner ℝ (x-y) (v-x) := by
        rw [← neg_sub x y, inner_neg_left]
      rw [hinner]
      have hc' : f (x + t • (v-x)) ≤ (1-t)*f x + t*f v := by
        simpa only [smul_eq_mul] using hc
      apply (mul_le_mul_iff_left₀ ht.1).mp
      nlinarith
    have hcl : (0 : ℝ) ∈ closure (Ioo 0 1) := by
      rw [closure_Ioo (by norm_num : (0:ℝ) ≠ 1)]
      simp
    have hc : Continuous (fun t : ℝ => f v + t/2*‖v-x‖^2) := by fun_prop
    have hh := ContinuousWithinAt.closure_le hcl
      (continuousWithinAt_const (b := f x + inner ℝ (y-x) (v-x))) hc.continuousWithinAt hb
    simpa using hh

lemma subgradient_strong_min {f : E → ℝ} {y x : E}
    (hs : IsSubgradientOn f univ x (y-x)) (v : E) :
    energy f y x + ‖v-x‖^2/2 ≤ energy f y v := by
  have hh := hs v (mem_univ _)
  have hi := energy_increment f y x v 1
  have heq : x + (1:ℝ) • (v-x) = v := by simp
  rw [heq] at hi
  have hí : inner ℝ (y-x) (v-x) = -inner ℝ (x-y) (v-x) := by
    rw [← neg_sub x y, inner_neg_left]
  rw [hí] at hh
  nlinarith

lemma subgradient_monotone {f : E → ℝ} {x z p q : E}
    (hp : IsSubgradientOn f univ x p) (hq : IsSubgradientOn f univ z q) :
    0 ≤ inner ℝ (p-q) (x-z) := by
  have h1 := hp z (mem_univ _)
  have h2 := hq x (mem_univ _)
  rw [← neg_sub x z, inner_neg_right] at h1
  simp only [inner_sub_left]
  linarith

lemma minimizer_unique {f : E → ℝ} (hf : ConvexOn ℝ univ f) {y x z : E}
    (hx : ∀ v, energy f y x ≤ energy f y v)
    (hz : ∀ v, energy f y z ≤ energy f y v) : x = z := by
  have hs := (subgradient_iff_minimizer hf y x).mpr hx
  have hb := subgradient_strong_min hs z
  have hh := hz x
  have hzero : ‖z-x‖ = 0 := by nlinarith [norm_nonneg (z-x)]
  exact (sub_eq_zero.mp (norm_eq_zero.mp hzero)).symm

variable [FiniteDimensional ℝ E]

lemma prox_minimizes (f : E → ℝ) (L : ℝ≥0) (hf : LipschitzWith L f) (y v : E) :
    energy f y (prox f L hf y) ≤ energy f y v :=
  Classical.choose_spec (exists_minimizer hf y) v

lemma prox_subgradient {f : E → ℝ} {L : ℝ≥0} (hlip : LipschitzWith L f)
    (hconv : ConvexOn ℝ univ f) (y : E) :
    IsSubgradientOn f univ (prox f L hlip y) (y - prox f L hlip y) :=
  (subgradient_iff_minimizer hconv y _).mpr (prox_minimizes f L hlip y)

lemma prox_of_subgradient {f : E → ℝ} {L : ℝ≥0} (hlip : LipschitzWith L f)
    (hconv : ConvexOn ℝ univ f) {x p : E} (hp : IsSubgradientOn f univ x p) :
    prox f L hlip (x+p) = x := by
  apply minimizer_unique hconv (prox_minimizes f L hlip (x+p))
  apply (subgradient_iff_minimizer hconv (x+p) x).mp
  simpa using hp

lemma prox_firm {f : E → ℝ} {L : ℝ≥0} (hlip : LipschitzWith L f)
    (hconv : ConvexOn ℝ univ f) (y z : E) :
    ‖prox f L hlip y - prox f L hlip z‖^2 ≤
      inner ℝ (prox f L hlip y - prox f L hlip z) (y-z) := by
  have hm := subgradient_monotone (prox_subgradient hlip hconv y)
    (prox_subgradient hlip hconv z)
  have heq : (y-prox f L hlip y) - (z-prox f L hlip z) =
      (y-z) - (prox f L hlip y - prox f L hlip z) := by abel
  rw [heq, inner_sub_left, real_inner_self_eq_norm_sq, real_inner_comm] at hm
  linarith

lemma prox_lipschitz {f : E → ℝ} {L : ℝ≥0} (hlip : LipschitzWith L f)
    (hconv : ConvexOn ℝ univ f) : LipschitzWith 1 (prox f L hlip) := by
  apply LipschitzWith.of_dist_le_mul
  intro y z
  have hf := prox_firm hlip hconv y z
  have hi := real_inner_le_norm (prox f L hlip y - prox f L hlip z) (y-z)
  have hnorm : ‖prox f L hlip y - prox f L hlip z‖ ≤ ‖y-z‖ := by
    nlinarith [norm_nonneg (prox f L hlip y - prox f L hlip z), norm_nonneg (y-z)]
  simpa only [NNReal.coe_one, one_mul, dist_eq_norm] using hnorm

omit [FiniteDimensional ℝ E] in
lemma subgradient_norm_le {f : E → ℝ} {L : ℝ≥0} (hlip : LipschitzWith L f)
    {x p : E} (hp : IsSubgradientOn f univ x p) : ‖p‖ ≤ L := by
  have hs := hp (x+p) (mem_univ _)
  have hl := hlip.dist_le_mul (x+p) x
  simp only [add_sub_cancel_left, real_inner_self_eq_norm_sq] at hs
  simp only [dist_eq_norm, add_sub_cancel_left] at hl
  have hh := (abs_le.mp hl).2
  nlinarith [norm_nonneg p]

lemma gradient_subgradient {f : E → ℝ} (hc : ConvexOn ℝ univ f) {x : E}
    {f' : E →L[ℝ] ℝ} (hder : HasFDerivAt f f' x) :
    IsSubgradientOn f univ x ((InnerProductSpace.toDual ℝ E).symm f') := by
  intro v _
  rw [InnerProductSpace.toDual_symm_apply]
  have hd : HasDerivAt (fun t : ℝ => f (x + t • (v-x))) (f' (v-x)) 0 := by
    have hp : HasDerivAt (fun t : ℝ => x + t • (v-x)) (v-x) 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (v-x)).const_add x
    have hdf : HasFDerivAt f f' (x + (0:ℝ) • (v-x)) := by simpa using hder
    exact hdf.comp_hasDerivAt 0 hp
  have hb : ∀ᶠ t : ℝ in 𝓝[>] 0,
      t⁻¹ * (f (x+t • (v-x)) - f x) ≤ f v - f x := by
    filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0:ℝ)<1)] with t ht
    have hcv := hc.2 (mem_univ x) (mem_univ v) (by linarith [ht.2] : 0 ≤ 1-t)
      ht.1.le (by ring : 1-t+t=1)
    have heq : (1-t) • x + t • v = x + t • (v-x) := by
      simp only [sub_smul, one_smul, smul_sub]
      abel
    rw [heq] at hcv
    simp only [smul_eq_mul] at hcv
    rw [inv_mul_eq_div, div_le_iff₀ ht.1]
    nlinarith
  have ht : Tendsto (fun t : ℝ => t⁻¹ * (f (x+t • (v-x)) - f x))
      (𝓝[>] 0) (𝓝 (f' (v-x))) := by
    simpa only [zero_add, zero_smul, add_zero, smul_eq_mul] using hd.tendsto_slope_zero_right
  have hh := le_of_tendsto ht hb
  linarith

lemma subgradient_eq_gradient {f : E → ℝ} {x p : E} {f' : E →L[ℝ] ℝ}
    (hder : HasFDerivAt f f' x) (hp : IsSubgradientOn f univ x p) :
    p = (InnerProductSpace.toDual ℝ E).symm f' := by
  let g : E → ℝ := fun z => f z - inner ℝ p z
  have hmin : IsLocalMin g x := by
    apply Filter.Eventually.of_forall
    intro z
    have hh := hp z (mem_univ _)
    dsimp [g]
    simp only [inner_sub_right] at hh
    linarith
  have hdg : HasFDerivAt g (f' - innerSL ℝ p) x :=
    hder.sub (innerSL ℝ p).hasFDerivAt
  have hz := hmin.hasFDerivAt_eq_zero hdg
  have heq : f' = innerSL ℝ p := sub_eq_zero.mp hz
  apply (InnerProductSpace.toDual ℝ E).injective
  simp only [LinearIsometryEquiv.apply_symm_apply]
  exact heq.symm

omit [FiniteDimensional ℝ E] in
lemma isClosed_subgradient_projection {f : E → ℝ} (hf : Continuous f)
    {K : Set E} (hK : IsCompact K) :
    IsClosed {x | ∃ p ∈ K, IsSubgradientOn f univ x p} := by
  have : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let C : Set (E × K) := {z | IsSubgradientOn f univ z.1 z.2.1}
  have hC : IsClosed C := by
    simp only [C, IsSubgradientOn, ofPred_forall]
    exact isClosed_iInter fun _ => isClosed_iInter fun _ =>
      isClosed_le (by fun_prop) (by fun_prop)
  have heq : {x | ∃ p ∈ K, IsSubgradientOn f univ x p} = Prod.fst '' C := by
    ext x
    constructor
    · rintro ⟨p,hp,hpx⟩
      exact ⟨(x,⟨p,hp⟩),hpx,rfl⟩
    · rintro ⟨⟨z,p⟩,hz,rfl⟩
      exact ⟨p.1,p.2,hz⟩
  rw [heq]
  exact isClosedMap_fst_of_compactSpace C hC

lemma subgradient_continuity_at_singleton {f : E → ℝ} {L : ℝ≥0}
    (hlip : LipschitzWith L f) {x p0 : E}
    (huniq : ∀ p, IsSubgradientOn f univ x p → p = p0) :
    ∀ eps : ℝ, 0 < eps → ∃ delta : ℝ, 0 < delta ∧
      ∀ z p : E, ‖z-x‖ < delta → IsSubgradientOn f univ z p → ‖p-p0‖ < eps := by
  intro eps heps
  let K := Metric.closedBall (0:E) (L:ℝ) \ Metric.ball p0 eps
  have hK : IsCompact K := (isCompact_closedBall _ _).diff Metric.isOpen_ball
  have hclosed := isClosed_subgradient_projection hlip.continuous hK
  have hx : x ∉ {z | ∃ p ∈ K, IsSubgradientOn f univ z p} := by
    rintro ⟨p,hp,hpx⟩
    have heq := huniq p hpx
    exact hp.2 (heq ▸ Metric.mem_ball_self heps)
  obtain ⟨delta,hd,hball⟩ := Metric.mem_nhds_iff.mp (hclosed.isOpen_compl.mem_nhds hx)
  refine ⟨delta,hd,?_⟩
  intro z p hz hp
  by_contra hbad
  have hpK : p ∈ K := by
    constructor
    · simpa only [Metric.mem_closedBall,dist_zero_right] using subgradient_norm_le hlip hp
    · simpa only [Metric.mem_ball,dist_eq_norm] using hbad
  exact (hball (by simpa only [Metric.mem_ball,dist_eq_norm] using hz)) ⟨p,hpK,hp⟩

lemma subgradient_continuity_of_differentiable {f : E → ℝ} {L : ℝ≥0}
    (hlip : LipschitzWith L f) {x : E} {f' : E →L[ℝ] ℝ} (hder : HasFDerivAt f f' x) :
    ∀ eps : ℝ, 0 < eps → ∃ delta : ℝ, 0 < delta ∧
      ∀ z p : E, ‖z-x‖ < delta → IsSubgradientOn f univ z p →
        ‖p-(InnerProductSpace.toDual ℝ E).symm f'‖ < eps :=
  subgradient_continuity_at_singleton hlip (fun _ hp => subgradient_eq_gradient hder hp)

lemma uniform_subgradient_differential_of_regular_prox {f : E → ℝ} {L : ℝ≥0}
    (hlip : LipschitzWith L f) (hc : ConvexOn ℝ univ f)
    {x y : E} {f' : E →L[ℝ] ℝ} (hdf : HasFDerivAt f f' x)
    (hy : prox f L hlip y = x) (B : E ≃L[ℝ] E)
    (hdP : HasFDerivAt (prox f L hlip) (B : E →L[ℝ] E) y) :
    ∀ eps : ℝ, 0 < eps → ∃ delta : ℝ, 0 < delta ∧
      ∀ z p : E, ‖z-x‖ < delta → IsSubgradientOn f univ z p →
        ‖p - (InnerProductSpace.toDual ℝ E).symm f' -
          ((B.symm : E →L[ℝ] E) - ContinuousLinearMap.id ℝ E) (z-x)‖ ≤
          eps * ‖z-x‖ := by
  let p0 := (InnerProductSpace.toDual ℝ E).symm f'
  have hyp : y = x + p0 := by
    have hs := prox_subgradient hlip hc y
    rw [hy] at hs
    have heq := subgradient_eq_gradient hdf hs
    dsimp [p0]
    rw [← heq]
    abel
  intro eps heps
  let K : ℝ := ‖(B.symm : E →L[ℝ] E)‖ + 1
  have hK : 0 < K := by dsimp [K] <;> positivity
  have hKbound : ‖(B.symm : E →L[ℝ] E)‖ ≤ K := by dsimp [K] <;> linarith
  let eta : ℝ := min (1/(2*K)) (eps/(2*K^2))
  have heta : 0 < eta := by dsimp [eta] <;> positivity
  have heta1 : K*eta ≤ 1/2 := by
    have hh := min_le_left (1/(2*K)) (eps/(2*K^2))
    have hh' := (le_div_iff₀ (by positivity : 0 < 2*K)).mp hh
    dsimp [eta]
    nlinarith
  have heta2 : 2*K^2*eta ≤ eps := by
    have hh := min_le_right (1/(2*K)) (eps/(2*K^2))
    have hh' := (le_div_iff₀ (by positivity : 0 < 2*K^2)).mp hh
    dsimp [eta]
    nlinarith
  obtain ⟨r,hr,hrem⟩ := Metric.mem_nhds_iff.mp (hdP.isLittleO.bound heta)
  obtain ⟨d,hd,hcont⟩ := subgradient_continuity_of_differentiable hlip hdf (r/2)
    (by positivity)
  refine ⟨min d (r/2), by positivity, ?_⟩
  intro z p hz hp
  have hpn : ‖p-p0‖ < r/2 := hcont z p (lt_of_lt_of_le hz (min_le_left _ _)) hp
  let k : E := z+p-y
  have hk : k = (z-x) + (p-p0) := by dsimp [k]; rw [hyp]; abel
  have hkr : ‖z+p-y‖ < r := by
    calc
      ‖z+p-y‖ = ‖(z-x)+(p-p0)‖ := congrArg norm hk
      _ ≤ ‖z-x‖ + ‖p-p0‖ := norm_add_le _ _
      _ < r := by have hz' := lt_of_lt_of_le hz (min_le_right _ _); linarith
  have hPz : prox f L hlip (z+p) = z := prox_of_subgradient hlip hc hp
  have hres : ‖(z-x) - B k‖ ≤ eta*‖k‖ := by
    have hh := hrem (by simpa only [Metric.mem_ball,dist_eq_norm] using hkr)
    simpa only [Set.mem_ofPred_eq, hy,hPz,k,ContinuousLinearEquiv.coe_coe] using hh
  have hinv : k = B.symm (z-x) - B.symm ((z-x)-B k) := by
    simp only [map_sub, B.symm_apply_apply]
    abel
  have hknorm : ‖k‖ ≤ 2*K*‖z-x‖ := by
    have htri : ‖k‖ ≤ ‖B.symm (z-x)‖ + ‖B.symm ((z-x)-B k)‖ := by
      conv_lhs => rw [hinv]
      exact norm_sub_le _ _
    have h1 := (B.symm : E →L[ℝ] E).le_opNorm (z-x)
    have h2 := (B.symm : E →L[ℝ] E).le_opNorm ((z-x)-B k)
    have h1' : ‖B.symm (z-x)‖ ≤ K*‖z-x‖ := h1.trans
      (mul_le_mul_of_nonneg_right hKbound (norm_nonneg _))
    have h2' : ‖B.symm ((z-x)-B k)‖ ≤ K*eta*‖k‖ := by
      calc
        ‖B.symm ((z-x)-B k)‖ ≤ K*‖(z-x)-B k‖ := h2.trans
          (mul_le_mul_of_nonneg_right hKbound (norm_nonneg _))
        _ ≤ K*(eta*‖k‖) := mul_le_mul_of_nonneg_left hres hK.le
        _ = K*eta*‖k‖ := by ring
    have h3 := mul_le_mul_of_nonneg_right heta1 (norm_nonneg k)
    nlinarith
  have heq : p-p0-((B.symm : E →L[ℝ] E) - ContinuousLinearMap.id ℝ E) (z-x) =
      - B.symm ((z-x)-B k) := by
    simp only [sub_apply, ContinuousLinearMap.id_apply,
      ContinuousLinearEquiv.coe_coe, map_sub, B.symm_apply_apply]
    rw [hk]
    abel
  change ‖p-p0-((B.symm : E →L[ℝ] E) - ContinuousLinearMap.id ℝ E) (z-x)‖ ≤ _
  rw [heq,norm_neg]
  calc
    ‖B.symm ((z-x)-B k)‖ ≤ K*‖(z-x)-B k‖ :=
      ((B.symm : E →L[ℝ] E).le_opNorm _).trans
        (mul_le_mul_of_nonneg_right hKbound (norm_nonneg _))
    _ ≤ K*(eta*‖k‖) := mul_le_mul_of_nonneg_left hres hK.le
    _ ≤ K*(eta*(2*K*‖z-x‖)) := mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left hknorm heta.le) hK.le
    _ = (2*K^2*eta)*‖z-x‖ := by ring
    _ ≤ eps*‖z-x‖ := mul_le_mul_of_nonneg_right heta2 (norm_nonneg _)

end ConvexProximal
end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Convexity_CoordinateSemiconvex
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
open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

namespace WeakMTWTransport
section CoordinateSemiconvex
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma cTransform_uniform_smooth_coordinate_semiconvex
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {ψ : E → M} (hψ : ContMDiffAt 𝓘(ℝ,E) 𝓘(ℝ,Model n) ∞ ψ 0) :
    ∃ r>0, ∃ K>0, ∀ v : M → ℝ, Continuous v →
      ConvexOn ℝ (Metric.ball (0:E) r)
        (fun h => cTransform v (ψ h)+K*‖h‖^2) := by
  let x := ψ 0
  let Y := fun z : TangentBundle 𝓘(ℝ,Model n) M => riemannianExp z.1 ((1/2:ℝ) • z.2)
  have hY : Continuous Y := (contMDiff_riemannianExp (n := n) (M := M)).continuous.comp
    ((contMDiff_tangentScale (E := Model n) (M := M)).continuous.comp
      (continuous_const.prodMk continuous_id))
  let P := fun r K : ℝ => fun h : E => fun Z : TangentBundle 𝓘(ℝ,Model n) M =>
    Z.1=ψ h → ∀ z∈Metric.ball (0:E) r, ∃ l : E →L[ℝ] ℝ,
      ∀ w∈Metric.ball (0:E) r,
        2*(cost (ψ w) (Y Z)-cost (ψ z) (Y Z))-
          l (w-z) ≤ K*‖w-z‖^2
  have hmono : ∀ {r R b B : ℝ}, 0 < r → r≤R → b≤B → ∀ h Z, P R b h Z → P r B h Z := by
    intro r R b B hr hrR hbB h Z HP he z hz
    obtain ⟨l,hl⟩ := HP he z (Metric.ball_subset_ball hrR hz)
    exact ⟨l,fun w hw => (hl w (Metric.ball_subset_ball hrR hw)).trans
      (mul_le_mul_of_nonneg_right hbB (sq_nonneg _))⟩
  have hlocal : ∀ Z : TangentBundle 𝓘(ℝ,Model n) M,
      Z.2∈minimizingVectors Z.1 →
      ∃ r>0, ∃ b>0, ∀ᶠ q : E×TangentBundle 𝓘(ℝ,Model n) M in 𝓝 (0,Z),
        P r b q.1 q.2 := by
    rintro ⟨a,p⟩ hp
    by_cases ha : a=x
    · subst a
      obtain ⟨r,hr,b,hb,H⟩ := smooth_coordinate_half_cost_quadratic hψ (hY.continuousAt (x := (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M))) rfl hp rfl
      refine ⟨r,hr,b,hb,?_⟩
      filter_upwards [continuousAt_snd.tendsto.eventually H] with q hq
      exact fun _ => hq
    · have hbase : Continuous (fun q : E×TangentBundle 𝓘(ℝ,Model n) M => q.2.1) :=
        (FiberBundle.continuous_proj _ _).comp continuous_snd
      have hexp : ContinuousAt (fun q : E×TangentBundle 𝓘(ℝ,Model n) M => ψ q.1) (0,⟨a,p⟩) :=
        ContinuousAt.comp (x := ((0:E),(⟨a,p⟩ : TangentBundle 𝓘(ℝ,Model n) M))) (f := Prod.fst) hψ.continuousAt continuousAt_fst
      have H : ∀ᶠ q : E×TangentBundle 𝓘(ℝ,Model n) M in 𝓝 (0,⟨a,p⟩),
          q.2.1≠ψ q.1 :=
        (hbase.continuousAt.prodMk hexp).preimage_mem_nhds
          (isClosed_diagonal.isOpen_compl.mem_nhds (by simpa only [mem_compl_iff,mem_diagonal_iff] using ha))
      exact ⟨1,by norm_num,1,by norm_num,H.mono (fun _ h he => (h he).elim)⟩
  obtain ⟨r,hr,K,hK,H⟩ := compact_eventually_uniform_radius_bound
    (isCompact_total_minimizingVectors (n := n) (M := M)) hmono hlocal
  obtain ⟨δ,hδ,Hδ⟩ := Metric.mem_nhds_iff.mp H
  refine ⟨min r δ,lt_min hr hδ,K,hK,?_⟩
  intro v hv
  apply convexOn_of_quadratic_lower_support (convex_ball _ _)
  intro z hz
  obtain ⟨p,hp⟩ := nonempty_activeLogs (n := n) hv (ψ z)
  have HZ := Hδ (Metric.ball_subset_ball (min_le_right r δ) hz)
    ⟨ψ z,p⟩ hp.1 rfl
  obtain ⟨l,hl⟩ := HZ z (Metric.ball_subset_ball (min_le_left r δ) hz)
  refine ⟨-l,?_⟩
  intro w hw
  have HH := hl w (Metric.ball_subset_ball (min_le_left r δ) hw)
  have hs := active_split_lower_support hv hp.1 hp.2
    (show (0:ℝ)<1/2 by norm_num) (show (1/2:ℝ)<1 by norm_num) (ψ w)
  simp only [neg_apply]
  dsimp only [Y] at HH
  linarith

end CoordinateSemiconvex
end WeakMTWTransport

end

end

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
local instance instNormedSpaceRealContinuousLinearMapIdTangentSpaceModelModelWithCornersSelf_r1900ce_1 (y : Model n) (x : M) : NormedSpace ℝ
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
-- module Solutions.OAIQ232_BH.BiholderTransport_Coordinates_Inner
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set Filter
open scoped Topology

namespace WeakMTWTransport
section Inner
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma hasQuadraticExpansion_iff_isLittleO {f : E → ℝ} {p : E} {A : E →L[ℝ] E} :
    HasQuadraticExpansion f p A ↔
      (fun h => f h - quadraticTaylor (f 0) p A h) =o[𝓝 0] (fun h : E => ‖h‖^2) := by
  rw [Asymptotics.isLittleO_iff]
  constructor
  · intro H c hc
    obtain ⟨d,hd,hbound⟩ := H c hc
    filter_upwards [Metric.ball_mem_nhds (0:E) hd] with h hh
    simpa only [Set.mem_ofPred_eq,Real.norm_eq_abs,abs_of_nonneg (sq_nonneg ‖h‖)] using
      hbound h (by simpa only [Metric.mem_ball,dist_zero_right] using hh)
  · intro H c hc
    obtain ⟨d,hd,hbound⟩ := Metric.mem_nhds_iff.mp (H hc)
    refine ⟨d,hd,?_⟩
    intro h hh
    simpa only [Set.mem_ofPred_eq,Real.norm_eq_abs,abs_of_nonneg (sq_nonneg ‖h‖)] using
      hbound (show h ∈ Metric.ball (0:E) d by simpa only [Metric.mem_ball,dist_zero_right] using hh)
end Inner
end WeakMTWTransport

end

end

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Volume_Measurable
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
open Set MeasureTheory Manifold Bundle
open scoped ContDiff Manifold ENNReal NNReal Topology

noncomputable section
open Set Filter
open scoped Topology NNReal

namespace WeakMTWTransport
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
open MeasureTheory

namespace ConvexProximal
variable [FiniteDimensional ℝ E]
section Measurable
open MeasureTheory

variable [MeasurableSpace E] [BorelSpace E]

lemma exists_subgradient {f : E → ℝ} {L : ℝ≥0} (hlip : LipschitzWith L f)
    (hc : ConvexOn ℝ univ f) (x : E) :
    ∃ p, IsSubgradientOn f univ x p := by
  let μ : Measure E := Measure.hausdorffMeasure (Module.finrank ℝ E)
  have hdense : Dense {z | DifferentiableAt ℝ f z} :=
    μ.dense_of_ae (hlip.ae_differentiableAt (μ := μ))
  let P := Metric.closedBall (0:E) (L:ℝ)
  have hP : IsCompact P := isCompact_closedBall _ _
  have : CompactSpace P := isCompact_iff_compactSpace.mp hP
  let C : Set (E × P) := {z | IsSubgradientOn f univ z.1 z.2.1}
  have hfc := hlip.continuous
  have hC : IsClosed C := by
    simp only [C, IsSubgradientOn, ofPred_forall]
    apply isClosed_iInter
    intro y
    apply isClosed_iInter
    intro _hy
    exact isClosed_le (by fun_prop) (by fun_prop)
  have hproj : IsClosed (Prod.fst '' C) := isClosedMap_fst_of_compactSpace C hC
  have hsub : {z | DifferentiableAt ℝ f z} ⊆ Prod.fst '' C := by
    intro z hz
    let p := (InnerProductSpace.toDual ℝ E).symm (fderiv ℝ f z)
    have hp : IsSubgradientOn f univ z p := gradient_subgradient hc hz.hasFDerivAt
    have hpn : p ∈ P := by
      simpa only [P, Metric.mem_closedBall, dist_zero_right] using subgradient_norm_le hlip hp
    exact ⟨(z, ⟨p, hpn⟩), hp, rfl⟩
  have hx : x ∈ Prod.fst '' C := by
    rw [← hproj.closure_eq]
    exact (Dense.mono hsub hdense) x
  obtain ⟨⟨z,p⟩, hz, rfl⟩ := hx
  exact ⟨p.1, hz⟩

lemma prox_surjective {f : E → ℝ} {L : ℝ≥0} (hlip : LipschitzWith L f)
    (hc : ConvexOn ℝ univ f) : Function.Surjective (prox f L hlip) := by
  intro x
  obtain ⟨p,hp⟩ := exists_subgradient hlip hc x
  exact ⟨x+p, prox_of_subgradient hlip hc hp⟩

lemma ae_exists_regular_proximal_inverse {f : E → ℝ} {L : ℝ≥0}
    (hlip : LipschitzWith L f) (hc : ConvexOn ℝ univ f)
    (μ : Measure E) [μ.IsAddHaarMeasure] :
    ∀ᵐ x ∂μ, ∃ y : E, prox f L hlip y = x ∧
      DifferentiableAt ℝ (prox f L hlip) y ∧
      (fderiv ℝ (prox f L hlip) y).det ≠ 0 := by
  let P := prox f L hlip
  let ν : Measure E := Measure.hausdorffMeasure (Module.finrank ℝ E)
  have hP : LipschitzWith 1 P := prox_lipschitz hlip hc
  let N : Set E := {y | ¬DifferentiableAt ℝ P y}
  let Z : Set E := {y | DifferentiableAt ℝ P y ∧ (fderiv ℝ P y).det = 0}
  have hN : ν N = 0 := (ae_iff).mp (hP.ae_differentiableAt (μ := ν))
  have hPN : ν (P '' N) = 0 := by
    have hh := hP.hausdorffMeasure_image_le
      (by positivity : (0:ℝ) ≤ Module.finrank ℝ E) N
    simpa only [ν, hN, mul_zero, nonpos_iff_eq_zero] using hh
  have hNμ : μ (P '' N) = 0 :=
    (Measure.absolutelyContinuous_isAddHaarMeasure μ ν) hPN
  have hZμ : μ (P '' Z) = 0 :=
    addHaar_image_eq_zero_of_det_fderivWithin_eq_zero μ
      (fun y hy => hy.1.hasFDerivAt.hasFDerivWithinAt) (fun y hy => hy.2)
  have hgood : ∀ᵐ x ∂μ, x ∉ P '' N ∧ x ∉ P '' Z := by
    exact (ae_iff.mpr (by simpa only [not_not, Set.ofPred_mem_eq] using hNμ)).and (ae_iff.mpr (by simpa only [not_not, Set.ofPred_mem_eq] using hZμ))
  filter_upwards [hgood] with x hx
  obtain ⟨y,hy⟩ := prox_surjective hlip hc x
  have hd : DifferentiableAt ℝ P y := by
    by_contra hn
    exact hx.1 ⟨y,hn,hy⟩
  refine ⟨y,hy,hd,?_⟩
  intro hz
  exact hx.2 ⟨y,⟨hd,hz⟩,hy⟩

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in

lemma subgradient_line_deriv {f : E → ℝ} {x h : E} {t a : ℝ} {p : E}
    (hp : IsSubgradientOn f univ (x+t • h) p)
    (hd : HasDerivAt (fun s : ℝ => f (x+s • h)) a t) :
    a = inner ℝ p h := by
  have hm : IsLocalMin (fun s : ℝ => f (x+s • h) - s*inner ℝ p h) t := by
    apply Filter.Eventually.of_forall
    intro s
    have hh := hp (x+s • h) (mem_univ _)
    have heq : (x+s • h)-(x+t • h) = (s-t) • h := by
      simp only [sub_smul]; abel
    rw [heq,real_inner_smul_right] at hh
    dsimp
    nlinarith
  have hh := hm.hasDerivAt_eq_zero (hd.sub ((hasDerivAt_id t).mul_const (inner ℝ p h)))
  simpa only [one_mul, sub_eq_zero] using hh

lemma quadraticExpansion_of_subgradient_differential {f : E → ℝ} {L : ℝ≥0}
    (hlip : LipschitzWith L f) (hc : ConvexOn ℝ univ f)
    {x p : E} {A : E →L[ℝ] E}
    (hdiff : ∀ eps : ℝ, 0 < eps → ∃ delta : ℝ, 0 < delta ∧
      ∀ z q : E, ‖z-x‖ < delta → IsSubgradientOn f univ z q →
        ‖q-p-A (z-x)‖ ≤ eps*‖z-x‖) :
    HasQuadraticExpansion (fun h => f (x+h)) p A := by
  intro eps heps
  obtain ⟨d,hd,hbound⟩ := hdiff eps heps
  refine ⟨d,hd,?_⟩
  intro h hh
  let g : ℝ → ℝ := fun t => f (x+t • h)
  have hline : LipschitzWith ‖h‖₊ (fun t : ℝ => x+t • h) := by
    apply LipschitzWith.of_dist_le_mul
    intro s t
    have heq : (x+s • h)-(x+t • h) = (s-t) • h := by
      simp only [sub_smul]; abel
    simp only [dist_eq_norm,heq,norm_smul,Real.norm_eq_abs,coe_nnnorm]
    exact le_of_eq (mul_comm _ _)
  have hgAC : AbsolutelyContinuousOnInterval g 0 1 :=
    (hlip.comp hline).lipschitzOnWith.absolutelyContinuousOnInterval
  let a : ℝ := inner ℝ p h
  let b : ℝ := inner ℝ (A h) h
  have hlin : IntervalIntegrable (fun t : ℝ => a+t*b) volume 0 1 :=
    (by fun_prop : Continuous (fun t : ℝ => a+t*b)).intervalIntegrable _ _
  have haebound : ∀ᵐ t : ℝ, t ∈ uIoc (0:ℝ) 1 →
      ‖deriv g t - (a+t*b)‖ ≤ eps*‖h‖^2 := by
    filter_upwards [hgAC.ae_differentiableAt] with t ht htc
    have ht01 : 0 ≤ t ∧ t ≤ 1 := by
      rw [uIoc_of_le (by norm_num : (0:ℝ) ≤ 1)] at htc
      exact ⟨htc.1.le,htc.2⟩
    have htu : t ∈ uIcc (0:ℝ) 1 := by
      rw [uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)]
      exact ht01
    obtain ⟨q,hq⟩ := exists_subgradient hlip hc (x+t • h)
    have hder : deriv g t = inner ℝ q h := subgradient_line_deriv hq (ht htu).hasDerivAt
    have hth : ‖(x+t • h)-x‖ ≤ ‖h‖ := by
      simp only [add_sub_cancel_left,norm_smul_of_nonneg ht01.1]
      exact mul_le_of_le_one_left (norm_nonneg _) ht01.2
    have hnorm := hbound (x+t • h) q (hth.trans_lt hh) hq
    have heq : deriv g t - (a+t*b) = inner ℝ (q-p-A ((x+t • h)-x)) h := by
      simp only [hder,a,b,inner_sub_left,add_sub_cancel_left,map_smul,
        real_inner_smul_left]
      ring
    calc
      ‖deriv g t - (a+t*b)‖ = ‖inner ℝ (q-p-A ((x+t • h)-x)) h‖ := congrArg norm heq
      _ ≤ ‖q-p-A ((x+t • h)-x)‖*‖h‖ := norm_inner_le_norm _ _
      _ ≤ (eps*‖(x+t • h)-x‖)*‖h‖ := mul_le_mul_of_nonneg_right hnorm (norm_nonneg _)
      _ ≤ (eps*‖h‖)*‖h‖ := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hth heps.le) (norm_nonneg _)
      _ = eps*‖h‖^2 := by ring
  have hi := intervalIntegral.norm_integral_le_of_norm_le_const_ae haebound
  rw [intervalIntegral.integral_sub hgAC.intervalIntegrable_deriv hlin,
    hgAC.integral_deriv_eq_sub] at hi
  have hilin : (∫ t : ℝ in (0:ℝ)..1, a+t*b) = a+b/2 := by
    rw [intervalIntegral.integral_add (f := fun _ : ℝ => a) (g := fun t : ℝ => t*b)
      (continuous_const.intervalIntegrable _ _)
      ((by fun_prop : Continuous (fun t : ℝ => t*b)).intervalIntegrable _ _),
      intervalIntegral.integral_const, intervalIntegral.integral_mul_const,integral_id]
    norm_num
    ring
  rw [hilin] at hi
  simpa only [HasQuadraticExpansion,quadraticTaylor,g,a,b,one_smul,zero_smul,add_zero,
    Real.norm_eq_abs,sub_zero,abs_one,mul_one,sub_sub,add_assoc] using hi

omit [MeasurableSpace E] [BorelSpace E] in

lemma symmetrized_quadratic (A : E →L[ℝ] E) :
    let S := (1/2 : ℝ) • (A + A.adjoint)
    (∀ h k, inner ℝ (S h) k = inner ℝ h (S k)) ∧
      (∀ h, inner ℝ (S h) h = inner ℝ (A h) h) := by
  dsimp
  constructor
  · intro h k
    simp only [smul_apply,add_apply,real_inner_smul_left,real_inner_smul_right,
      inner_add_left,inner_add_right,A.adjoint_inner_left,A.adjoint_inner_right]
    ring
  · intro h
    simp only [smul_apply,add_apply,real_inner_smul_left,inner_add_left,
      A.adjoint_inner_left,real_inner_comm h (A h)]
    ring

lemma ae_quadraticExpansion_lipschitz_convex {f : E → ℝ} {L : ℝ≥0}
    (hlip : LipschitzWith L f) (hc : ConvexOn ℝ univ f)
    (μ : Measure E) [μ.IsAddHaarMeasure] :
    ∀ᵐ x ∂μ, ∃ p : E, ∃ A : E →L[ℝ] E,
      (∀ h k, inner ℝ (A h) k = inner ℝ h (A k)) ∧
      HasQuadraticExpansion (fun h => f (x+h)) p A := by
  filter_upwards [hlip.ae_differentiableAt (μ := μ),
    ae_exists_regular_proximal_inverse hlip hc μ] with x hdf hx
  obtain ⟨y,hy,hdP,hdet⟩ := hx
  let B := (fderiv ℝ (prox f L hlip) y).toContinuousLinearEquivOfDetNeZero hdet
  have hB : HasFDerivAt (prox f L hlip) (B : E →L[ℝ] E) y := by
    simpa only [B,ContinuousLinearMap.coe_toContinuousLinearEquivOfDetNeZero] using hdP.hasFDerivAt
  let p := (InnerProductSpace.toDual ℝ E).symm (fderiv ℝ f x)
  let A := (B.symm : E →L[ℝ] E) - ContinuousLinearMap.id ℝ E
  have hdiff := uniform_subgradient_differential_of_regular_prox hlip hc
    hdf.hasFDerivAt hy B hB
  have hquad : HasQuadraticExpansion (fun h => f (x+h)) p A :=
    quadraticExpansion_of_subgradient_differential hlip hc hdiff
  let S := (1/2 : ℝ) • (A + A.adjoint)
  obtain ⟨hsym,hdiag⟩ := symmetrized_quadratic A
  change ∀ h, inner ℝ (S h) h = inner ℝ (A h) h at hdiag
  refine ⟨p,S,hsym,?_⟩
  intro eps heps
  obtain ⟨d,hd,hbound⟩ := hquad eps heps
  refine ⟨d,hd,?_⟩
  intro h hh
  have hi := hbound h hh
  simpa only [quadraticTaylor,hdiag h] using hi

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in

lemma quadraticExpansion_congr_nhds {f g : E → ℝ} {p : E} {A : E →L[ℝ] E}
    (hfg : f =ᶠ[𝓝 (0:E)] g) (hf : HasQuadraticExpansion f p A) :
    HasQuadraticExpansion g p A := by
  obtain ⟨r,hr,hball⟩ := Metric.mem_nhds_iff.mp hfg
  have hzero : f 0 = g 0 := hfg.self_of_nhds
  intro eps heps
  obtain ⟨d,hd,hbound⟩ := hf eps heps
  refine ⟨min d r,by positivity,?_⟩
  intro h hh
  have hhg : f h = g h := hball (by
    simpa only [Metric.mem_ball,dist_zero_right] using lt_of_lt_of_le hh (min_le_right _ _))
  have hb := hbound h (lt_of_lt_of_le hh (min_le_left _ _))
  simpa only [quadraticTaylor,hzero,hhg] using hb

lemma ae_quadraticExpansion_convex_open {f : E → ℝ} {s : Set E}
    (hs : IsOpen s) (hc : ConvexOn ℝ s f) (μ : Measure E) [μ.IsAddHaarMeasure] :
    ∀ᵐ x ∂μ, x ∈ s → ∃ p : E, ∃ A : E →L[ℝ] E,
      (∀ h k, inner ℝ (A h) k = inner ℝ h (A k)) ∧
      HasQuadraticExpansion (fun h => f (x+h)) p A := by
  apply ae_of_locally_ae μ
  intro x hx
  obtain ⟨L,t,ht,hlip⟩ := hc.locallyLipschitzOn hs hx
  rw [nhdsWithin_eq_nhds.mpr (hs.mem_nhds hx)] at ht
  obtain ⟨r,hr,hrt⟩ := Metric.mem_nhds_iff.mp (inter_mem ht (hs.mem_nhds hx))
  have hrt' : Metric.ball x r ⊆ t := fun _ hy => (hrt hy).1
  have hrs : Metric.ball x r ⊆ s := fun _ hy => (hrt hy).2
  obtain ⟨g,hgL,hgC,hfg⟩ := convex_lipschitz_extension
    (hc.subset hrs (convex_ball _ _)) (hlip.mono hrt')
    (Metric.nonempty_ball.mpr hr)
  refine ⟨Metric.ball x r,Metric.isOpen_ball,Metric.mem_ball_self hr,?_⟩
  filter_upwards [ae_quadraticExpansion_lipschitz_convex hgL hgC μ] with z hz hzb
  obtain ⟨p,A,hA,hquad⟩ := hz
  refine ⟨p,A,hA,quadraticExpansion_congr_nhds ?_ hquad⟩
  have hcont : Tendsto (fun h : E => z+h) (𝓝 0) (𝓝 z) := by
    have hc : Continuous (fun h : E => z+h) := continuous_const.add continuous_id
    simpa only [add_zero] using hc.tendsto (0:E)
  filter_upwards [hcont (Metric.isOpen_ball.mem_nhds hzb)] with h hh
  exact (hfg hh).symm

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in

lemma quadraticExpansion_sub_quadratic {f : E → ℝ} {x p : E} {A : E →L[ℝ] E}
    (K : ℝ)
    (hg : HasQuadraticExpansion (fun h => f (x+h)+K/2*‖x+h‖^2) p A) :
    HasQuadraticExpansion (fun h => f (x+h)) (p-K • x)
      (A-K • ContinuousLinearMap.id ℝ E) := by
  intro eps heps
  obtain ⟨d,hd,hbound⟩ := hg eps heps
  refine ⟨d,hd,?_⟩
  intro h hh
  have heq : (f (x+h)+K/2*‖x+h‖^2) -
      quadraticTaylor (f (x+0)+K/2*‖x+0‖^2) p A h =
        f (x+h)-quadraticTaylor (f (x+0)) (p-K • x)
          (A-K • ContinuousLinearMap.id ℝ E) h := by
    simp only [quadraticTaylor,add_zero,norm_sq_add_real,inner_sub_left,
      real_inner_smul_left,sub_apply,smul_apply,ContinuousLinearMap.id_apply,
      real_inner_self_eq_norm_sq]
    ring
  have hb := hbound h hh
  rwa [heq] at hb

lemma ae_quadraticExpansion_semiconvex_open {f : E → ℝ} {s : Set E} (K : ℝ)
    (hs : IsOpen s) (hc : ConvexOn ℝ s (fun z => f z+K/2*‖z‖^2))
    (μ : Measure E) [μ.IsAddHaarMeasure] :
    ∀ᵐ x ∂μ, x ∈ s → ∃ p : E, ∃ A : E →L[ℝ] E,
      (∀ h k, inner ℝ (A h) k = inner ℝ h (A k)) ∧
      HasQuadraticExpansion (fun h => f (x+h)) p A := by
  filter_upwards [ae_quadraticExpansion_convex_open hs hc μ] with x hx hxs
  obtain ⟨p,A,hA,hquad⟩ := hx hxs
  refine ⟨p-K • x,A-K • ContinuousLinearMap.id ℝ E,?_,
    quadraticExpansion_sub_quadratic K hquad⟩
  intro h k
  simp only [sub_apply,smul_apply,ContinuousLinearMap.id_apply,inner_sub_left,
    inner_sub_right,real_inner_smul_left,real_inner_smul_right,hA h k]
end Measurable

end ConvexProximal
end WeakMTWTransport

end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Coordinates_CoordinateExpansion
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
open Set Filter
open scoped Topology

namespace WeakMTWTransport
section CoordinateExpansion
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

lemma contDiffAt_exists_quadraticExpansion {f : E → ℝ} (hf : ContDiffAt ℝ 2 f 0) :
    ∃ p : E, ∃ A : E →L[ℝ] E,
      (∀ u v, inner ℝ (A u) v=inner ℝ u (A v)) ∧ HasQuadraticExpansion f p A := by
  let J := (InnerProductSpace.toDual ℝ E).symm
  let p : E := J (fderiv ℝ f 0)
  let A : E →L[ℝ] E := J.toContinuousLinearEquiv.toContinuousLinearMap.comp
    (fderiv ℝ (fderiv ℝ f) 0)
  have hA (u v : E) : inner ℝ (A u) v=fderiv ℝ (fderiv ℝ f) 0 u v :=
    InnerProductSpace.toDual_symm_apply
  have hp (u : E) : inner ℝ p u=fderiv ℝ f 0 u := InnerProductSpace.toDual_symm_apply
  refine ⟨p,A,?_,?_⟩
  · intro u v
    have hc : inner ℝ u (A v)=inner ℝ (A v) u := real_inner_comm _ _
    rw [hA,hc,hA]
    exact (hf.isSymmSndFDerivAt (by norm_num)).eq u v
  · rw [hasQuadraticExpansion_iff_isLittleO]
    convert contDiffAt_second_order_remainder hf using 1
    all_goals try with_reducible_and_instances rfl
    funext h
    simp only [quadraticTaylor,hp,hA]
    ring

omit [CompleteSpace E] in
lemma HasQuadraticExpansion.of_isLittleO_sub {f g : E → ℝ} {p : E} {A : E →L[ℝ] E}
    (hg : HasQuadraticExpansion g p A) (h0 : f 0=g 0)
    (hfg : (fun h => f h-g h) =o[𝓝 0] (fun h : E => ‖h‖^2)) :
    HasQuadraticExpansion f p A := by
  rw [hasQuadraticExpansion_iff_isLittleO] at hg ⊢
  convert! hfg.add hg using 1
  all_goals try with_reducible_and_instances rfl
  funext h
  rw [h0]
  ring

omit [CompleteSpace E] in
lemma HasQuadraticExpansion.congr_eventually {f g : E → ℝ} {p : E} {A : E →L[ℝ] E}
    (hf : HasQuadraticExpansion f p A) (hfg : f =ᶠ[𝓝 0] g) :
    HasQuadraticExpansion g p A := by
  rw [hasQuadraticExpansion_iff_isLittleO] at hf ⊢
  apply hf.congr' _ (Filter.EventuallyEq.refl _ _)
  filter_upwards [hfg] with h hh
  rw [hh,hfg.self_of_nhds]

omit [CompleteSpace F] in
lemma HasQuadraticExpansion.comp_contDiffAt {f : F → ℝ} {p : F} {A : F →L[ℝ] F}
    (hf : HasQuadraticExpansion f p A) {η : E → F} (hη0 : η 0=0)
    (hη : ContDiffAt ℝ 2 η 0) :
    ∃ q : E, ∃ B : E →L[ℝ] E,
      (∀ u v, inner ℝ (B u) v=inner ℝ u (B v)) ∧
        HasQuadraticExpansion (fun h => f (η h)) q B := by
  let P : F → ℝ := quadraticTaylor (f 0) p A
  have hP : ContDiff ℝ 2 P := by
    dsimp [P,quadraticTaylor]
    exact (contDiff_const.add (contDiff_const.inner ℝ contDiff_id)).add
      ((A.contDiff.inner ℝ contDiff_id).div_const 2)
  obtain ⟨q,B,hBs,hB⟩ := contDiffAt_exists_quadraticExpansion (hP.contDiffAt.comp 0 hη)
  refine ⟨q,B,hBs,hB.of_isLittleO_sub ?_ ?_⟩
  · simp only [Function.comp_apply,hη0,P,quadraticTaylor,map_zero,inner_zero_right,zero_div,add_zero]
  · have hD := (hη.differentiableAt (by norm_num)).hasFDerivAt
    have hO : η =O[𝓝 0] (fun h : E => h) := by
      simpa only [hη0,sub_zero] using hD.isBigO_sub
    have hO2 : (fun h : E => ‖η h‖^2) =O[𝓝 0] (fun h : E => ‖h‖^2) := by
      simpa only [←sq] using hO.norm_norm.mul hO.norm_norm
    have ht : Tendsto η (𝓝 0) (𝓝 0) := by
      simpa only [ContinuousAt,hη0] using hη.continuousAt
    exact ((hasQuadraticExpansion_iff_isLittleO.mp hf).comp_tendsto ht).trans_isBigO hO2

end CoordinateExpansion
end WeakMTWTransport

end

end

section

noncomputable section
open Set Filter Manifold MeasureTheory Bundle Metric
open scoped Topology ContDiff ENNReal NNReal

namespace WeakMTWTransport
section AENormalExpansion
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

local instance localInst_r1900ce_1 (x : M) : FiniteDimensional ℝ (TangentSpace 𝓘(ℝ,Model n) x) :=
  inferInstanceAs (FiniteDimensional ℝ (Model n))
omit [Nonempty M] in
lemma cTransform_ae_normal_quadraticExpansion_oai {v : M → ℝ} (hv : Continuous v) :
    ∀ᵐ w ∂metricVolume (M := M) n,
      ∃ p : TangentSpace 𝓘(ℝ,Model n) w, ∃ A : TangentSpace 𝓘(ℝ,Model n) w →L[ℝ] TangentSpace 𝓘(ℝ,Model n) w,
        (∀ h k, inner ℝ (A h) k=inner ℝ h (A k)) ∧
        HasQuadraticExpansion (fun h => cTransform v (riemannianExp w h)) p A := by
  suffices HH : ∀ x∈(univ : Set M), ∃ U : Set M, IsOpen U ∧ x∈U ∧
      (∀ᵐ w ∂metricVolume (M := M) n, w∈U →
        ∃ p : TangentSpace 𝓘(ℝ,Model n) w, ∃ A : TangentSpace 𝓘(ℝ,Model n) w →L[ℝ] TangentSpace 𝓘(ℝ,Model n) w,
          (∀ h k, inner ℝ (A h) k=inner ℝ h (A k)) ∧
          HasQuadraticExpansion (fun h => cTransform v (riemannianExp w h)) p A) by
    simpa only [mem_univ,true_implies] using ae_of_locally_ae (metricVolume (M := M) n) HH
  intro x _
  obtain ⟨C,r,hr,htarget,hLip⟩ := exists_lipschitz_inverse_chart (n := n) x
  let d := extChartAt 𝓘(ℝ,Model n) x
  let ψ := fun z : Model n => d.symm (d x+z)
  have hψ : ContMDiffAt 𝓘(ℝ,Model n) 𝓘(ℝ,Model n) ∞ ψ 0 := by
    apply (show ContMDiffAt 𝓘(ℝ,Model n) 𝓘(ℝ,Model n) ∞ d.symm (d x+0) from by
      simpa only [add_zero] using (contMDiffOn_extChartAt_symm x).contMDiffAt
        ((isOpen_extChartAt_target x).mem_nhds (mem_extChartAt_target x))).comp
    exact (contDiff_const.add contDiff_id).contDiffAt.contMDiffAt
  obtain ⟨R,hR,K,hK,hconv⟩ := cTransform_uniform_smooth_coordinate_semiconvex hψ
  let B := ball (0:Model n) (min R r)
  let U := d.source ∩ (fun w => d w-d x) ⁻¹' B
  have hU : IsOpen U := ((continuousOn_extChartAt x).sub continuousOn_const).isOpen_inter_preimage
    (isOpen_extChartAt_source x) isOpen_ball
  refine ⟨U,hU,⟨mem_extChartAt_source x,by simpa [B] using And.intro hR hr⟩,?_⟩
  have hBtarget : ∀ z∈B, d x+z∈d.target := by
    intro z hz
    apply htarget
    change d x+z∈ball (d x) r
    simpa only [mem_ball,dist_eq_norm,add_sub_cancel_left,sub_zero] using
      Metric.ball_subset_ball (min_le_right R r) hz
  have hB' : ∀ z∈B, d x+z∈ball (d x) r := by
    intro z hz
    simpa only [mem_ball,dist_eq_norm,add_sub_cancel_left,sub_zero] using
      Metric.ball_subset_ball (min_le_right R r) hz
  have hψLip : LipschitzOnWith C ψ B := by
    intro a ha b hb
    simpa only [ψ,edist_dist,dist_eq_norm,add_sub_add_left_eq_sub] using
      hLip (hB' a ha) (hB' b hb)
  let μ : Measure (Model n) := Measure.hausdorffMeasure (n:ℝ)
  have hdim : Module.finrank ℝ (Model n)=n := by simp [Model]
  have : μ.IsAddHaarMeasure := by
    dsimp only [μ]
    rw [←hdim]
    first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)
  have hc : ConvexOn ℝ B (fun z => cTransform v (ψ z)+(2*K)/2*‖z‖^2) := by
    simpa only [mul_div_cancel_left₀ K (show (2:ℝ)≠0 by norm_num)] using
      (hconv v hv).subset (Metric.ball_subset_ball (min_le_left R r)) (convex_ball _ _)
  have hAlex := ConvexProximal.ae_quadraticExpansion_semiconvex_open (2*K) isOpen_ball hc μ
  let N := {z : Model n | z∈B ∧ ¬∃ p : Model n, ∃ A : Model n →L[ℝ] Model n,
    (∀ h k, inner ℝ (A h) k=inner ℝ h (A k)) ∧
      HasQuadraticExpansion (fun h => cTransform v (ψ (z+h))) p A}
  have hN : μ N=0 := by
    apply measure_mono_null _ (ae_iff.mp hAlex)
    intro z hz
    exact fun hh => hz.2 (hh hz.1)
  have hImage : (Measure.hausdorffMeasure (n:ℝ) : Measure M) (ψ '' N)=0 := by
    apply le_antisymm _ (show (0:ℝ≥0∞)≤_ from zero_le)
    have hNsub : N⊆B := fun _ h => h.1
    have H := (hψLip.mono hNsub).hausdorffMeasure_image_le
      (d := (n:ℝ)) (by positivity)
    change _≤(C : ℝ≥0∞)^(n:ℝ)*μ N at H
    simpa only [hN,mul_zero] using H
  have hImageVol : metricVolume (M := M) n (ψ '' N)=0 := by
    simp only [metricVolume,Measure.smul_apply,smul_eq_mul,hImage,mul_zero]
  have hOutside : ∀ᵐ w ∂metricVolume (M := M) n, w∉ψ '' N := ae_iff.mpr (by simpa only [not_not,Set.ofPred_mem_eq] using hImageVol)
  filter_upwards [hOutside] with w hw hwU
  let z := d w-d x
  have hzB : z∈B := hwU.2
  have hψz : ψ z=w := by simp only [ψ,z,add_sub_cancel,d.left_inv hwU.1]
  have hzN : z∉N := fun h => hw ⟨z,h,hψz⟩
  have hzQ : ∃ p : Model n, ∃ A : Model n →L[ℝ] Model n,
      (∀ h k, inner ℝ (A h) k=inner ℝ h (A k)) ∧
        HasQuadraticExpansion (fun h => cTransform v (ψ (z+h))) p A := by
    by_contra hh
    exact hzN ⟨hzB,hh⟩
  obtain ⟨p,A,_,hQ⟩ := hzQ
  let η := fun h : TangentSpace 𝓘(ℝ,Model n) w => d (riemannianExp w h)-d w
  have hη0 : η 0=0 := by simp [η,riemannianExp_zero]
  have hη : ContDiffAt ℝ ∞ η 0 := by
    have hc : ContMDiffAt 𝓘(ℝ,Model n) 𝓘(ℝ,Model n) ∞ d w :=
      contMDiffAt_extChartAt' (by simpa only [d,extChartAt_source] using hwU.1)
    have hd := (show ContMDiffAt 𝓘(ℝ,Model n) 𝓘(ℝ,Model n) ∞ d (riemannianExp w 0) from by
      simpa only [riemannianExp_zero] using hc).comp 0 (contMDiff_riemannianExp_fiber w 0)
    exact hd.contDiffAt.sub contDiffAt_const
  obtain ⟨q,B,hBs,hB⟩ := hQ.comp_contDiffAt hη0
    (hη.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2))
  refine ⟨q,B,hBs,hB.congr_eventually ?_⟩
  have hsource : d.source∈𝓝 w := (isOpen_extChartAt_source x).mem_nhds hwU.1
  have hsource' : d.source∈𝓝 (riemannianExp (n := n) w 0) := by
    simpa only [riemannianExp_zero] using hsource
  have hnear := (contMDiff_riemannianExp_fiber (n := n) w).continuous.continuousAt.preimage_mem_nhds hsource'
  filter_upwards [hnear] with h hh
  have he : ψ (z+η h)=riemannianExp w h := by
    dsimp [ψ,z,η]
    rw [show d x+(d w-d x+(d (riemannianExp w h)-d w))=d (riemannianExp w h) by abel]
    exact d.left_inv hh
  exact congrArg (cTransform v) he

end AENormalExpansion
end WeakMTWTransport

end

end

end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.WeakMTWTransport.cTransform_ae_normal_quadraticExpansion_oai.{u_1} := @OAI.WeakMTWTransport.cTransform_ae_normal_quadraticExpansion_oai.{u_1}
