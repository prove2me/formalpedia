-- Prove2me | solution 1 for OAI.WeakMTWTransport.contact_selection_chart_differential_full
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T19:26:44.892812+00:00
-- url     : https://prove2.me/submissions/2ebdcdff-d59e-4ab9-8900-86bb8869b165

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
import Definitions.Def_OAIQ232A027

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Calculus_Gradient
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter
open scoped Topology ContDiff

namespace WeakMTWTransport
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

lemma twist_hasFDerivWithinAt
    {B : E×E → ℝ} {q g : E → E} {p : E} {S A : E →L[ℝ] E} {s : Set E}
    (hB : ContDiffAt ℝ 2 B (0,p))
    (hxx : ∀ u v : E, fderiv ℝ (fderiv ℝ B) (0,p) (u,0) (v,0)=inner ℝ (S u) v)
    (hqx : ∀ u v : E, fderiv ℝ (fderiv ℝ B) (0,p) (0,u) (v,0)= -inner ℝ u v)
    (hq0 : q 0=p) (hqc : ContinuousAt q 0) (hg : HasFDerivWithinAt g A s 0)
    (hcontact : ∀ᶠ x in 𝓝[s] 0, (fderiv ℝ B (x,q x)).comp
      (ContinuousLinearMap.inl ℝ E E)= -(innerSL ℝ (g x)))
    (hcontact0 : (fderiv ℝ B (0,p)).comp
      (ContinuousLinearMap.inl ℝ E E)= -(innerSL ℝ (g 0))) :
    HasFDerivWithinAt q (S+A) s 0 := by
  let J : (E →L[ℝ] ℝ) →L[ℝ] E :=
    (InnerProductSpace.toDual ℝ E).symm.toContinuousLinearEquiv.toContinuousLinearMap
  let D : E×E → (E →L[ℝ] ℝ) := fun z =>
    (fderiv ℝ B z).comp (ContinuousLinearMap.inl ℝ E E)
  let H : E×E → E×E := fun z => (z.1,-J (D z))
  let L : E×E →L[ℝ] E×E :=
    (ContinuousLinearMap.fst ℝ E E).prod
      (ContinuousLinearMap.snd ℝ E E-S.comp (ContinuousLinearMap.fst ℝ E E))
  let R : E×E →L[ℝ] E×E :=
    (ContinuousLinearMap.fst ℝ E E).prod
      (ContinuousLinearMap.snd ℝ E E+S.comp (ContinuousLinearMap.fst ℝ E E))
  have hRL : Function.LeftInverse R L := by
    intro z
    change (z.1,z.2-S z.1+S z.1)=z
    simp
  have hLR : Function.RightInverse R L := by
    intro z
    change (z.1,z.2+S z.1-S z.1)=z
    simp
  let e : (E×E) ≃L[ℝ] (E×E) := ContinuousLinearEquiv.equivOfInverse L R hRL hLR
  have hDc : ContDiffAt ℝ 1 D (0,p) :=
    (hB.fderiv_right (m := 1) (by norm_num)).clm_comp contDiffAt_const
  have hHc : ContDiffAt ℝ 1 H (0,p) := contDiffAt_fst.prodMk
    (J.contDiff.contDiffAt.comp (0,p) hDc).neg
  have hDd := ((hB.fderiv_right (m := 1) (by norm_num)).differentiableAt
    (by norm_num)).hasFDerivAt.clm_comp
      (hasFDerivAt_const (ContinuousLinearMap.inl ℝ E E) (0,p))
  have hHd := (hasFDerivAt_fst (p := (0,p))).prodMk
    (((J.hasFDerivAt).comp (0,p) hDd).neg)
  have hHD : HasFDerivAt H (e : (E×E) →L[ℝ] (E×E)) (0,p) := by
    apply hHd.congr_fderiv
    apply ContinuousLinearMap.ext
    intro z
    apply Prod.ext
    · rfl
    · apply (InnerProductSpace.toDual ℝ E).injective
      change (InnerProductSpace.toDual ℝ E) (-J _) = _
      rw [map_neg,show ∀ ξ : E →L[ℝ] ℝ, (InnerProductSpace.toDual ℝ E) (J ξ)=ξ from
        fun ξ => (InnerProductSpace.toDual ℝ E).apply_symm_apply ξ]
      ext v
      change -((fderiv ℝ B (0,p)) (0,0)+fderiv ℝ (fderiv ℝ B) (0,p) z (v,0)) =
        inner ℝ (z.2-S z.1) v
      rw [show ((0:E),(0:E))=(0:E×E) by rfl,map_zero,zero_add]
      rw [show z=(z.1,0)+(0,z.2) by ext <;> simp,map_add,add_apply,hxx,hqx]
      simp only [inner_sub_left,Prod.fst_add,Prod.snd_add,add_zero,zero_add]
      ring
  have hstrict := hHc.hasStrictFDerivAt' hHD (by norm_num)
  have J_inner (a : E) : J (innerSL ℝ a)=a := by
    apply (InnerProductSpace.toDual ℝ E).injective
    rw [show (InnerProductSpace.toDual ℝ E) (J (innerSL ℝ a))=innerSL ℝ a from
      (InnerProductSpace.toDual ℝ E).apply_symm_apply _]
    rfl
  have hH0 : H (0,p)=(0,g 0) := by
    change (0,-J ((fderiv ℝ B (0,p)).comp (ContinuousLinearMap.inl ℝ E E)))=(0,g 0)
    rw [hcontact0,map_neg,J_inner,neg_neg]
  let inv := hstrict.localInverse H e (0,p)
  have hi : HasFDerivAt inv (e.symm : (E×E) →L[ℝ] (E×E)) (0,g 0) := by
    rw [←hH0]
    exact hstrict.to_localInverse.hasFDerivAt
  have hcomp := hi.comp_hasFDerivWithinAt 0 ((hasFDerivAt_id (𝕜 := ℝ) (0:E)).hasFDerivWithinAt.prodMk hg)
  have hfinal := (hasFDerivAt_snd (p := inv (0,g 0))).comp_hasFDerivWithinAt 0 hcomp
  have heq : ∀ᶠ x in 𝓝[s] 0, q x=(inv (x,g x)).2 := by
    have hnear := (continuousAt_id.prodMk hqc).tendsto.eventually
      (by rw [hq0]; exact hstrict.eventually_left_inverse)
    filter_upwards [hcontact,mem_nhdsWithin_of_mem_nhds hnear] with x hx hxi
    have Hx : H (x,q x)=(x,g x) := by
      change (x,-J ((fderiv ℝ B (x,q x)).comp (ContinuousLinearMap.inl ℝ E E)))=(x,g x)
      rw [hx,map_neg,J_inner,neg_neg]
    change inv (H (x,q x))=(x,q x) at hxi
    rw [Hx] at hxi
    exact (congrArg Prod.snd hxi).symm
  have heq0 : q 0=(inv (0,g 0)).2 := by
    change q 0=(hstrict.localInverse H e (0,p) (0,g 0)).2
    rw [←hH0,hstrict.localInverse_apply_image,hq0]
  apply (hfinal.congr_of_eventuallyEq heq heq0).congr_fderiv
  ext h
  change A h+S h=S h+A h
  exact add_comm _ _

end WeakMTWTransport

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

end AEContacts
end WeakMTWTransport

end

end

end

end OAI
end

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

end ContactSelection

end WeakMTWTransport
end
end
end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Contact_SubgradientDifferential
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

open Set Filter
open scoped Topology

namespace WeakMTWTransport

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma quadraticTaylor_increment (f0 : ℝ) (p : E) (A : E →L[ℝ] E)
    (hA : ∀ x y, inner ℝ (A x) y = inner ℝ x (A y)) (h e : E) (t : ℝ) :
    quadraticTaylor f0 p A (h + t • e) - quadraticTaylor f0 p A h =
      t * inner ℝ (p + A h) e + t ^ 2 / 2 * inner ℝ (A e) e := by
  have hs : inner ℝ (A e) h = inner ℝ (A h) e := (hA e h).trans (real_inner_comm _ _)
  simp only [quadraticTaylor, map_add, map_smul, inner_add_left, inner_add_right,
    real_inner_smul_left, real_inner_smul_right, hs]
  ring

lemma subgradient_directional_bound {f : E → ℝ} {f0 : ℝ} {p h zeta e : E}
    {A : E →L[ℝ] E} (hA : ∀ x y, inner ℝ (A x) y = inner ℝ x (A y))
    {r alpha w : ℝ} (hr : 0 < r) (ha : 0 < alpha) (ha1 : alpha ≤ 1)
    (hw : 0 ≤ w) (hh : ‖h‖ ≤ r) (he : ‖e‖ = 1)
    (hrem : ∀ z : E, ‖z‖ ≤ 2*r →
      |f z - quadraticTaylor f0 p A z| ≤ w * ‖z‖ ^ 2)
    (hsub : IsSubgradientOn f (Metric.closedBall 0 (2*r)) h zeta) :
    inner ℝ (zeta - p - A h) e ≤ ‖A‖ * alpha * r / 2 + 5*w*r/alpha := by
  have hat : 0 < alpha*r := mul_pos ha hr
  have hz : ‖h + (alpha*r) • e‖ ≤ 2*r := by
    calc
      ‖h + (alpha*r) • e‖ ≤ ‖h‖ + ‖(alpha*r) • e‖ := norm_add_le _ _
      _ = ‖h‖ + alpha*r := by rw [norm_smul_of_nonneg hat.le, he, mul_one]
      _ ≤ 2*r := by nlinarith
  have hxbound := hrem h (by linarith)
  have hzbound := hrem (h + (alpha*r) • e) hz
  have hsg := hsub (h + (alpha*r) • e) (by
    simpa only [Metric.mem_closedBall, dist_zero_right] using hz)
  have hnormsq : ‖h + (alpha*r) • e‖ ^ 2 ≤ 4*r^2 := by
    nlinarith [norm_nonneg (h + (alpha*r) • e)]
  have hhsq : ‖h‖ ^ 2 ≤ r^2 := by nlinarith [norm_nonneg h]
  have hremdiff : (f (h + (alpha*r) • e) - quadraticTaylor f0 p A (h + (alpha*r) • e)) -
      (f h - quadraticTaylor f0 p A h) ≤ 5*w*r^2 := by
    have h1 := (abs_le.mp hzbound).2
    have h2 := (abs_le.mp hxbound).1
    have h3 := mul_le_mul_of_nonneg_left hnormsq hw
    have h4 := mul_le_mul_of_nonneg_left hhsq hw
    nlinarith
  have hquad := quadraticTaylor_increment f0 p A hA h e (alpha*r)
  have hAe : inner ℝ (A e) e ≤ ‖A‖ := by
    calc
      inner ℝ (A e) e ≤ ‖inner ℝ (A e) e‖ := le_abs_self _
      _ ≤ ‖A e‖ * ‖e‖ := norm_inner_le_norm _ _
      _ ≤ ‖A‖ := by simpa only [he, mul_one] using A.le_opNorm e
  simp only [add_sub_cancel_left, real_inner_smul_right] at hsg
  have hdir : alpha*r * inner ℝ (zeta - p - A h) e ≤
      (alpha*r)^2/2 * ‖A‖ + 5*w*r^2 := by
    simp only [inner_sub_left, inner_add_left] at hquad ⊢
    have hm := mul_le_mul_of_nonneg_left hAe (by positivity : 0 ≤ (alpha*r)^2/2)
    nlinarith
  apply (mul_le_mul_iff_right₀ hat).mp
  have hcancel : (5*w*r/alpha) * (alpha*r) = 5*w*r^2 := by field_simp
  nlinarith

lemma subgradient_norm_bound {f : E → ℝ} {f0 : ℝ} {p h zeta : E}
    {A : E →L[ℝ] E} (hA : ∀ x y, inner ℝ (A x) y = inner ℝ x (A y))
    {r alpha w : ℝ} (hr : 0 < r) (ha : 0 < alpha) (ha1 : alpha ≤ 1)
    (hw : 0 ≤ w) (hh : ‖h‖ ≤ r)
    (hrem : ∀ z : E, ‖z‖ ≤ 2*r →
      |f z - quadraticTaylor f0 p A z| ≤ w * ‖z‖ ^ 2)
    (hsub : IsSubgradientOn f (Metric.closedBall 0 (2*r)) h zeta) :
    ‖zeta - p - A h‖ ≤ ‖A‖ * alpha * r / 2 + 5*w*r/alpha := by
  by_cases hzero : zeta - p - A h = 0
  · rw [hzero, norm_zero]
    positivity
  let v := zeta - p - A h
  let e := ‖v‖⁻¹ • v
  have he : ‖e‖ = 1 := norm_smul_inv_norm (𝕜 := ℝ) hzero
  have hd := subgradient_directional_bound hA hr ha ha1 hw hh he hrem hsub
  have hv : 0 < ‖v‖ := norm_pos_iff.mpr hzero
  have hip : inner ℝ (zeta - p - A h) e = ‖zeta - p - A h‖ := by
    change inner ℝ v (‖v‖⁻¹ • v) = ‖v‖
    rw [real_inner_smul_right, real_inner_self_eq_norm_sq]
    field_simp
  exact hip ▸ hd

lemma subgradient_zero_of_quadraticExpansion {f : E → ℝ} {p zeta : E}
    {A : E →L[ℝ] E} (hA : ∀ x y, inner ℝ (A x) y = inner ℝ x (A y))
    (hexp : HasQuadraticExpansion f p A) {R : ℝ} (hR : 0 < R)
    (hsub : IsSubgradientOn f (Metric.ball 0 R) 0 zeta) : zeta = p := by
  obtain ⟨delta, hdelta, hrem⟩ := hexp 1 zero_lt_one
  let eps := min R delta / 4
  have heps : 0 < eps := by dsimp [eps] <;> positivity
  have hbound (r : ℝ) (hr : r ∈ Ioo 0 eps) :
      ‖zeta - p‖ ≤ ‖A‖ * 1 * r / 2 + 5*1*r/1 := by
    have hrR : 2*r < R := by
      have hh : 4*eps ≤ R := by dsimp [eps] <;> linarith [min_le_left R delta]
      linarith [hr.2]
    have hrdelta : 2*r < delta := by
      have hh : 4*eps ≤ delta := by dsimp [eps] <;> linarith [min_le_right R delta]
      linarith [hr.2]
    have hh := subgradient_norm_bound (p := p) (h := 0) hA hr.1 zero_lt_one
      le_rfl zero_le_one (by simpa using hr.1.le)
      (fun z hz => hrem z (hz.trans_lt hrdelta))
      (fun z hz => hsub z (by
        rw [Metric.mem_ball, dist_zero_right]
        exact (show ‖z‖ ≤ 2 * r from by simpa only [Metric.mem_closedBall, dist_zero_right] using hz).trans_lt hrR))
    simpa only [map_zero, sub_zero] using hh
  have hcl : (0 : ℝ) ∈ closure (Ioo 0 eps) := by
    rw [closure_Ioo heps.ne]
    exact ⟨le_rfl, heps.le⟩
  have hcont : Continuous (fun r : ℝ => ‖A‖ * 1 * r / 2 + 5*1*r/1) := by fun_prop
  have hlim := ContinuousWithinAt.closure_le hcl
    (continuousWithinAt_const (b := ‖zeta-p‖)) hcont.continuousWithinAt hbound
  have hz : ‖zeta-p‖ = 0 := le_antisymm (by simpa using hlim) (norm_nonneg _)
  exact sub_eq_zero.mp (norm_eq_zero.mp hz)

lemma subgradient_uniform_differential {f : E → ℝ} {p : E} {A : E →L[ℝ] E}
    (hA : ∀ x y, inner ℝ (A x) y = inner ℝ x (A y))
    (hexp : HasQuadraticExpansion f p A) {R : ℝ} (hR : 0 < R) :
    ∀ eps : ℝ, 0 < eps → ∃ delta : ℝ, 0 < delta ∧
      ∀ h zeta : E, ‖h‖ < delta → IsSubgradientOn f (Metric.ball 0 R) h zeta →
        ‖zeta - p - A h‖ ≤ eps * ‖h‖ := by
  intro eps heps
  let alpha : ℝ := min 1 (eps / (‖A‖ + 1))
  have ha : 0 < alpha := by dsimp [alpha] <;> positivity
  have ha1 : alpha ≤ 1 := min_le_left _ _
  have hAa : ‖A‖ * alpha ≤ eps := by
    have hh := (le_div_iff₀ (by positivity : 0 < ‖A‖ + 1)).mp (min_le_right 1 (eps/(‖A‖+1)))
    change alpha * (‖A‖+1) ≤ eps at hh
    nlinarith
  let w : ℝ := eps * alpha / 20
  have hw : 0 < w := by dsimp [w] <;> positivity
  obtain ⟨d, hd, hrem⟩ := hexp w hw
  let delta := min R d / 4
  have hdelta : 0 < delta := by dsimp [delta] <;> positivity
  refine ⟨delta, hdelta, ?_⟩
  intro h zeta hh hsub
  by_cases hz : h = 0
  · subst h
    have hzet := subgradient_zero_of_quadraticExpansion hA hexp hR hsub
    simp [hzet]
  have hnorm : 0 < ‖h‖ := norm_pos_iff.mpr hz
  have hhr : 2*‖h‖ < R := by
    have ht : 4*delta ≤ R := by dsimp [delta] <;> linarith [min_le_left R d]
    linarith
  have hhd : 2*‖h‖ < d := by
    have ht : 4*delta ≤ d := by dsimp [delta] <;> linarith [min_le_right R d]
    linarith
  have hb := subgradient_norm_bound hA hnorm ha ha1 hw.le le_rfl
    (fun z hz => hrem z (hz.trans_lt hhd))
    (fun z hz => hsub z (by
      rw [Metric.mem_ball, dist_zero_right]
      exact (show ‖z‖ ≤ 2 * ‖h‖ from by simpa only [Metric.mem_closedBall, dist_zero_right] using hz).trans_lt hhr))
  apply hb.trans
  have hwcalc : 5*w*‖h‖/alpha = eps*‖h‖/4 := by
    dsimp [w]
    field_simp
    ring
  rw [hwcalc]
  have hm := mul_le_mul_of_nonneg_right hAa hnorm.le
  nlinarith

lemma semiconvex_subgradient_iff {f : E → ℝ} {s : Set E} {K : ℝ} {h zeta : E} :
    IsSemiconvexSubgradientOn f s K h zeta ↔
      IsSubgradientOn (fun x => f x + K / 2 * ‖x‖ ^ 2) s h (zeta + K • h) := by
  have heq (y : E) :
      f h + K / 2 * ‖h‖ ^ 2 + inner ℝ (zeta + K • h) (y - h) -
          (f y + K / 2 * ‖y‖ ^ 2) =
      f h + inner ℝ zeta (y-h) - K/2*‖y-h‖^2 - f y := by
    simp only [← real_inner_self_eq_norm_sq, inner_add_left, inner_sub_left,
      inner_sub_right, real_inner_smul_left]
    rw [real_inner_comm y h]
    ring
  constructor <;> intro hs y hy
  · have hh := hs y hy
    linarith [heq y]
  · have hh := hs y hy
    linarith [heq y]

lemma quadraticExpansion_add_quadratic {f : E → ℝ} {p : E} {A : E →L[ℝ] E}
    (hexp : HasQuadraticExpansion f p A) (K : ℝ) :
    HasQuadraticExpansion (fun x => f x + K / 2 * ‖x‖ ^ 2) p
      (A + K • ContinuousLinearMap.id ℝ E) := by
  intro w hw
  obtain ⟨d, hd, hr⟩ := hexp w hw
  refine ⟨d, hd, fun z hz => ?_⟩
  have heq : (f z + K/2*‖z‖ ^ 2) -
      quadraticTaylor (f 0 + K/2*‖(0 : E)‖ ^ 2) p
        (A + K • ContinuousLinearMap.id ℝ E) z = f z - quadraticTaylor (f 0) p A z := by
    simp only [quadraticTaylor, norm_zero, zero_pow (by omega : 2 ≠ 0), mul_zero,
      add_zero, add_apply, smul_apply,
      ContinuousLinearMap.id_apply, inner_add_left, real_inner_smul_left,
      real_inner_self_eq_norm_sq]
    ring
  rw [heq]
  exact hr z hz

lemma semiconvex_subgradient_uniform_differential {f : E → ℝ} {p : E}
    {A : E →L[ℝ] E} (hA : ∀ x y, inner ℝ (A x) y = inner ℝ x (A y))
    (hexp : HasQuadraticExpansion f p A) {R : ℝ} (hR : 0 < R) (K : ℝ) :
    ∀ eps : ℝ, 0 < eps → ∃ delta : ℝ, 0 < delta ∧
      ∀ h zeta : E, ‖h‖ < delta →
        IsSemiconvexSubgradientOn f (Metric.ball 0 R) K h zeta →
        ‖zeta - p - A h‖ ≤ eps * ‖h‖ := by
  have hs : ∀ x y : E,
      inner ℝ ((A + K • ContinuousLinearMap.id ℝ E) x) y =
        inner ℝ x ((A + K • ContinuousLinearMap.id ℝ E) y) := by
    intro x y
    simp only [add_apply, smul_apply,
      ContinuousLinearMap.id_apply, inner_add_left, inner_add_right,
      real_inner_smul_left, real_inner_smul_right, hA]
  intro eps heps
  obtain ⟨delta, hdelta, hb⟩ := subgradient_uniform_differential hs
    (quadraticExpansion_add_quadratic hexp K) hR eps heps
  refine ⟨delta, hdelta, ?_⟩
  intro h zeta hh hsub
  have hhbound := hb h (zeta + K • h) hh (semiconvex_subgradient_iff.mp hsub)
  have heq : zeta + K • h - p - (A + K • ContinuousLinearMap.id ℝ E) h =
      zeta - p - A h := by
    simp only [add_apply, smul_apply, ContinuousLinearMap.id_apply]
    abel
  rwa [heq] at hhbound


end WeakMTWTransport
end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Coordinates_Taylor
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

open Set Filter
open scoped Topology

namespace WeakMTWTransport
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma HasQuadraticExpansion.hasFDerivAt {f : E → ℝ} {p : E} {A : E →L[ℝ] E}
    (hexp : HasQuadraticExpansion f p A) : HasFDerivAt f ((innerSL ℝ) p) 0 := by
  obtain ⟨d,hd,hbound⟩ := hexp 1 zero_lt_one
  let K : ℝ := 1+‖A‖/2
  have hK : 0 < K := by dsimp [K] <;> positivity
  rw [hasFDerivAt_iff_isLittleO_nhds_zero,Asymptotics.isLittleO_iff]
  intro c hc
  have hpos : 0 < min d (c/K) := by positivity
  filter_upwards [Metric.ball_mem_nhds (0:E) hpos] with h hh
  have hn : ‖h‖ < min d (c/K) := by simpa only [Metric.mem_ball,dist_zero_right] using hh
  have hb := hbound h (lt_of_lt_of_le hn (min_le_left _ _))
  have hA : |inner ℝ (A h) h| ≤ ‖A‖*‖h‖^2 := by
    calc
      _ ≤ ‖A h‖*‖h‖ := abs_real_inner_le_norm _ _
      _ ≤ (‖A‖*‖h‖)*‖h‖ := mul_le_mul_of_nonneg_right (A.le_opNorm h) (norm_nonneg _)
      _ = _ := by ring
  have heq : f h-f 0-inner ℝ p h =
      (f h-quadraticTaylor (f 0) p A h)+inner ℝ (A h) h/2 := by
    simp only [quadraticTaylor]
    ring
  have hb' : |f h-f 0-inner ℝ p h| ≤ K*‖h‖^2 := by
    rw [heq]
    have ht := abs_add_le (f h-quadraticTaylor (f 0) p A h) (inner ℝ (A h) h/2)
    rw [abs_div,abs_of_pos (by norm_num : (0:ℝ)<2)] at ht
    dsimp [K]
    nlinarith
  have hmul : ‖h‖*K ≤ c := (le_div_iff₀ hK).mp (le_of_lt (lt_of_lt_of_le hn (min_le_right _ _)))
  have hbc : K*‖h‖^2 ≤ c*‖h‖ := by
    nlinarith [mul_le_mul_of_nonneg_right hmul (norm_nonneg h)]
  simpa only [zero_add,innerSL_apply_apply,Real.norm_eq_abs] using hb'.trans hbc

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Convexity_AlexandrovDerivative
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
section AlexandrovDerivative
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma semiconvex_selection_hasFDerivWithinAt {f : E → ℝ} {p : E}
    {A : E →L[ℝ] E} (hA : ∀ x y, inner ℝ (A x) y=inner ℝ x (A y))
    (hexp : HasQuadraticExpansion f p A) {R : ℝ} (hR : 0<R) (K : ℝ)
    {s : Set E} {g : E → E} (hg0 : g 0=p)
    (hg : ∀ z∈s, IsSemiconvexSubgradientOn f (Metric.ball 0 R) K z (g z)) :
    HasFDerivWithinAt g A s 0 := by
  rw [hasFDerivWithinAt_iff_isLittleO,Asymptotics.isLittleO_iff]
  intro eps heps
  obtain ⟨d,hd,H⟩ := semiconvex_subgradient_uniform_differential hA hexp hR K eps heps
  filter_upwards [self_mem_nhdsWithin,
    nhdsWithin_le_nhds (Metric.ball_mem_nhds (0:E) hd)]
      with z hz hzd
  simpa only [sub_zero,hg0] using H z (g z)
    (by simpa only [Metric.mem_ball,dist_zero_right] using hzd) (hg z hz)
variable [CompleteSpace E]

lemma gradient_subgradient_on {f : E → ℝ} {s : Set E}
    (hc : ConvexOn ℝ s f) {x : E} (hx : x∈s)
    {f' : E →L[ℝ] ℝ} (hder : HasFDerivAt f f' x) :
    IsSubgradientOn f s x ((InnerProductSpace.toDual ℝ E).symm f') := by
  intro v hv
  rw [InnerProductSpace.toDual_symm_apply]
  have hd : HasDerivAt (fun t : ℝ => f (x+t • (v-x))) (f' (v-x)) 0 := by
    have hp : HasDerivAt (fun t : ℝ => x+t • (v-x)) (v-x) 0 := by
      simpa using ((hasDerivAt_id (0:ℝ)).smul_const (v-x)).const_add x
    exact (show HasFDerivAt f f' (x+(0:ℝ) • (v-x)) from by simpa using hder).comp_hasDerivAt 0 hp
  have hb : ∀ᶠ t : ℝ in 𝓝[>] 0,
      t⁻¹*(f (x+t • (v-x))-f x)≤f v-f x := by
    filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0:ℝ)<1)] with t ht
    have hcv := hc.2 hx hv (by linarith [ht.2] : 0≤1-t) ht.1.le (by ring : 1-t+t=1)
    have heq : (1-t) • x+t • v=x+t • (v-x) := by
      simp only [sub_smul,one_smul,smul_sub]; abel
    rw [heq] at hcv
    simp only [smul_eq_mul] at hcv
    rw [inv_mul_eq_div,div_le_iff₀ ht.1]
    nlinarith
  have ht : Tendsto (fun t : ℝ => t⁻¹*(f (x+t • (v-x))-f x))
      (𝓝[>] 0) (𝓝 (f' (v-x))) := by
    simpa only [zero_add,zero_smul,add_zero,smul_eq_mul] using hd.tendsto_slope_zero_right
  have H := le_of_tendsto ht hb
  linarith

lemma gradient_semiconvex_subgradient_on {f : E → ℝ} {s : Set E} {K : ℝ}
    (hc : ConvexOn ℝ s (fun z => f z+K/2*‖z‖^2)) {x : E} (hx : x∈s)
    (hd : DifferentiableAt ℝ f x) :
    IsSemiconvexSubgradientOn f s K x
      ((InnerProductSpace.toDual ℝ E).symm (fderiv ℝ f x)) := by
  rw [semiconvex_subgradient_iff]
  have hq := ((hasStrictFDerivAt_norm_sq x).hasFDerivAt.const_mul (K/2))
  have h := gradient_subgradient_on hc hx (hd.hasFDerivAt.add hq)
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  apply (InnerProductSpace.toDual ℝ E).injective
  simp only [map_add,map_smul,LinearIsometryEquiv.apply_symm_apply]
  ext z
  simp only [add_apply,smul_apply,
    InnerProductSpace.toDual_apply_apply,innerSL_apply_apply,smul_eq_mul]
  ring

lemma semiconvex_gradient_hasFDerivWithinAt {f : E → ℝ} {p : E}
    {A : E →L[ℝ] E} (hA : ∀ x y, inner ℝ (A x) y=inner ℝ x (A y))
    (hexp : HasQuadraticExpansion f p A) {R : ℝ} (hR : 0<R) {K : ℝ}
    (hc : ConvexOn ℝ (Metric.ball 0 R) (fun z => f z+K/2*‖z‖^2)) :
    HasFDerivWithinAt (fun z => (InnerProductSpace.toDual ℝ E).symm (fderiv ℝ f z)) A
      {z | z∈Metric.ball 0 R ∧ DifferentiableAt ℝ f z} 0 := by
  apply semiconvex_selection_hasFDerivWithinAt hA hexp hR K
  · rw [hexp.hasFDerivAt.fderiv]
    exact (InnerProductSpace.toDual ℝ E).symm_apply_apply p
  · intro z hz
    exact gradient_semiconvex_subgradient_on hc hz.1 hz.2
end AlexandrovDerivative
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
-- module Solutions.OAIQ232_BH.BiholderTransport_LinearAlgebra_MovingSplit
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
open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

namespace WeakMTWTransport

lemma pair_hessian_snd_from_gradient
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {B : E × E → ℝ} {p : E} (hB : ContDiffAt ℝ 2 B (0,p))
    (u : E × E) {g : E → ℝ} {D : E →L[ℝ] ℝ}
    (heq : (fun v : E => fderiv ℝ B (0,v) u) =ᶠ[𝓝 p] g)
    (hg : HasFDerivAt g D p) (k : E) :
    fderiv ℝ (fderiv ℝ B) (0,p) (0,k) u = D k := by
  have hdf := (hB.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hL : HasFDerivAt (fun v : E => ((0:E),v))
      ((0 : E →L[ℝ] E).prod (ContinuousLinearMap.id ℝ E)) p :=
    (hasFDerivAt_const (0:E) p).prodMk (hasFDerivAt_id (𝕜 := ℝ) p)
  have hd := ((hdf.hasFDerivAt.comp (f := fun v : E => ((0:E),v)) p hL).clm_apply
    (hasFDerivAt_const u p)).fderiv
  have H := congrArg (fun A : E →L[ℝ] ℝ => A k)
    (hd.symm.trans (heq.fderiv_eq.trans hg.fderiv))
  simpa only [add_apply,ContinuousLinearMap.comp_apply,zero_apply,map_zero,zero_add,
    ContinuousLinearMap.flip_apply,ContinuousLinearMap.prod_apply,
    ContinuousLinearMap.id_apply] using H

end WeakMTWTransport
end
end
end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Coordinates_Prefix
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
section Prefix
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma prefixNormalCost_contDiffAt {x : M} {p : TangentSpace 𝓘(ℝ,Model n) x}
    {t : ℝ} (hleft : t • p ∈ injectivityDomain x) :
    ContDiffAt ℝ ∞ (prefixNormalCost x t) (0,p) := by
  let V := TangentSpace 𝓘(ℝ,Model n) x
  have he := contMDiff_riemannianExp_fiber (n := n) x
  have hu : ContMDiffAt 𝓘(ℝ,V×V) 𝓘(ℝ,Model n) ∞
      (fun q : V×V => riemannianExp x q.1) (0,p) :=
    (he _).comp (0,p) contDiffAt_fst.contMDiffAt
  have hv : ContMDiffAt 𝓘(ℝ,V×V) 𝓘(ℝ,Model n) ∞
      (fun q : V×V => riemannianExp x (t • q.2)) (0,p) :=
    (he _).comp (0,p) (show ContDiffAt ℝ ∞ (fun q : V×V => t • q.2) (0,p) from by fun_prop).contMDiffAt
  have hc := cost_contMDiffAt_of_injectivityDomain
    (⟨x,t • p⟩ : TangentBundle 𝓘(ℝ,Model n) M) hleft
  have hc' : ContMDiffAt (𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n)) 𝓘(ℝ,ℝ) ∞
      (fun q : M×M => cost q.1 q.2) (riemannianExp x (0:V),riemannianExp x (t • p)) := by
    simpa only [riemannianExp_zero] using hc
  exact ((hc'.comp (0,p) (hu.prodMk hv)).contDiffAt.div_const t)

lemma prefixNormalCost_zero {x : M} {p : TangentSpace 𝓘(ℝ,Model n) x}
    {t : ℝ} (ht : 0 < t) (hp : t • p ∈ injectivityDomain x) :
    prefixNormalCost x t (0,p) = t/2*‖p‖^2 := by
  have H := injectivityDomain_subset_minimizingVectors x hp
  change dist x (riemannianExp x (t • p)) = ‖t • p‖ at H
  simp only [prefixNormalCost,riemannianExp_zero,cost,H,norm_smul_of_nonneg ht.le]
  field_simp

lemma prefixNormalCost_source_gradient {x : M} {p : TangentSpace 𝓘(ℝ,Model n) x}
    {t : ℝ} (ht : t ≠ 0) (hp : t • p ∈ injectivityDomain x)
    (u : TangentSpace 𝓘(ℝ,Model n) x) :
    fderiv ℝ (prefixNormalCost x t) (0,p) (u,0) = -inner ℝ p u := by
  have hB := (prefixNormalCost_contDiffAt hp).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  have hnc := ((normalCost_contDiffAt hp).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).hasFDerivAt
  have H := hnc.mul_const t⁻¹
  have H' : HasFDerivAt (fun a => prefixNormalCost x t (a,p))
      (t⁻¹ • fderiv ℝ (normalCost x (t • p)) 0) 0 := by
    simpa only [prefixNormalCost,normalCost,div_eq_mul_inv] using H
  have hpair := (hasFDerivAt_id (𝕜 := ℝ) (0 : TangentSpace 𝓘(ℝ,Model n) x)).prodMk
    (hasFDerivAt_const p (0 : TangentSpace 𝓘(ℝ,Model n) x))
  have heq := (hB.hasFDerivAt.comp (f := fun a => (a,p)) 0 hpair).unique H'
  have hh := congrArg (fun A : TangentSpace 𝓘(ℝ,Model n) x →L[ℝ] ℝ => A u) heq
  change fderiv ℝ (prefixNormalCost x t) (0,p) (u,0) =
    t⁻¹ * fderiv ℝ (normalCost x (t • p)) 0 u at hh
  rw [normalCost_fderiv_zero hp,real_inner_smul_left] at hh
  rw [hh]
  field_simp

lemma prefixNormalCost_target_gradient {x : M} {p : TangentSpace 𝓘(ℝ,Model n) x}
    {t : ℝ} (ht : 0 < t) (hp : t • p ∈ injectivityDomain x)
    (u : TangentSpace 𝓘(ℝ,Model n) x) :
    fderiv ℝ (prefixNormalCost x t) (0,p) (0,u) = t*inner ℝ p u := by
  let V := TangentSpace 𝓘(ℝ,Model n) x
  have hB := (prefixNormalCost_contDiffAt hp).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  have hnear : ∀ᶠ q : V in 𝓝 p, t • q ∈ injectivityDomain x :=
    (show ContinuousAt (fun q : V => t • q) p from by fun_prop).preimage_mem_nhds
      (isOpen_injectivityDomain x |>.mem_nhds hp)
  have heq : (fun q : V => prefixNormalCost x t (0,q)) =ᶠ[𝓝 p]
      (fun q : V => t/2*‖q‖^2) := hnear.mono (fun _ h => prefixNormalCost_zero ht h)
  have H := ((hasFDerivAt_id (𝕜 := ℝ) p).norm_sq).const_mul (t/2)
  have Hd : HasFDerivAt (fun q : V => prefixNormalCost x t (0,q))
      ((t/2) • (2 • innerSL ℝ p)) p := by
    exact H.congr_of_eventuallyEq heq
  have hpair := (hasFDerivAt_const (0:V) p).prodMk (hasFDerivAt_id (𝕜 := ℝ) p)
  have hh := congrArg (fun A : V →L[ℝ] ℝ => A u)
    ((hB.hasFDerivAt.comp (f := fun q : V => ((0:V),q)) p hpair).unique Hd)
  simp only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.prod_apply,zero_apply,
    smul_apply,innerSL_apply_apply] at hh
  convert! hh using 1
  all_goals try with_reducible_and_instances rfl
  simp only [smul_eq_mul]
  ring

lemma prefixNormalCost_hessian_blocks {x : M} {p : TangentSpace 𝓘(ℝ,Model n) x}
    {t : ℝ} (ht : 0 < t) (hp : t • p ∈ injectivityDomain x)
    (u v : TangentSpace 𝓘(ℝ,Model n) x) :
    fderiv ℝ (fderiv ℝ (prefixNormalCost x t)) (0,p) (u,0) (0,v) = -inner ℝ u v ∧
    fderiv ℝ (fderiv ℝ (prefixNormalCost x t)) (0,p) (0,u) (0,v) = t*inner ℝ u v := by
  let V := TangentSpace 𝓘(ℝ,Model n) x
  have hB₂ := (prefixNormalCost_contDiffAt hp).of_le (m := 2)
    (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  have hnear : ∀ᶠ q : V in 𝓝 p, t • q ∈ injectivityDomain x :=
    (show ContinuousAt (fun q : V => t • q) p from by fun_prop).preimage_mem_nhds
      (isOpen_injectivityDomain x |>.mem_nhds hp)
  constructor
  · have heq : (fun q : V => fderiv ℝ (prefixNormalCost x t) (0,q) (u,0)) =ᶠ[𝓝 p]
        (fun q : V => -inner ℝ u q) := by
      filter_upwards [hnear] with q hq
      rw [prefixNormalCost_source_gradient ht.ne' hq,real_inner_comm]
    have H := pair_hessian_snd_from_gradient hB₂ (u,0) heq
      (((innerSL ℝ u).hasFDerivAt (x := p)).neg) v
    rw [(hB₂.isSymmSndFDerivAt (by simp)).eq] at H
    exact H
  · have heq : (fun q : V => fderiv ℝ (prefixNormalCost x t) (0,q) (0,v)) =ᶠ[𝓝 p]
        (fun q : V => t*inner ℝ v q) := by
      filter_upwards [hnear] with q hq
      rw [prefixNormalCost_target_gradient ht hq,real_inner_comm]
    have H := pair_hessian_snd_from_gradient hB₂ (0,v) heq
      (((innerSL ℝ v).hasFDerivAt (x := p)).const_mul t) u
    simpa only [smul_apply,innerSL_apply_apply,real_inner_comm v u,smul_eq_mul] using H

end Prefix
end WeakMTWTransport

end

end

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_LinearAlgebra_Aggregate
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology BigOperators

namespace WeakMTWTransport

lemma symmetric_bilinear_eq_of_diagonal
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {A B : E →L[ℝ] E →L[ℝ] ℝ}
    (hA : ∀ u v, A u v = A v u) (hB : ∀ u v, B u v = B v u)
    (hd : ∀ u, A u u = B u u) : A = B := by
  ext u v
  have H := hd (u+v)
  simp only [map_add,add_apply,hA v u,hB v u] at H
  linarith [hd u,hd v]

section GeometryJets
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma prefixNormalCost_source_hessian {x : M} {p : TangentSpace 𝓘(ℝ,Model n) x}
    {t : ℝ} (hp : t • p ∈ injectivityDomain x)
    (u : TangentSpace 𝓘(ℝ,Model n) x) :
    fderiv ℝ (fderiv ℝ (prefixNormalCost x t)) (0,p) (u,0) (u,0) =
      normalHessian x (t • p) u u/t := by
  have H := iteratedDeriv_two_affine_line
    ((prefixNormalCost_contDiffAt hp).of_le (m := 2)
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)) (u,0)
  simp only [prefixNormalCost,Prod.fst_add,Prod.smul_fst,Prod.snd_add,Prod.smul_snd,
    zero_add,smul_zero,add_zero,iteratedDeriv_div_const] at H
  rw [← H,← hessianValue_eq_normalHessian hp]
  rfl
end GeometryJets
end WeakMTWTransport

end

end

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_LinearAlgebra_ContactDifferential
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

omit [Nonempty M] [MeasurableSpace M] [BorelSpace M] in
lemma prefixNormalCost_source_hessian_full {x : M} {p : TangentSpace 𝓘(ℝ,Model n) x}
    (hp : p∈injectivityDomain x) (u v : TangentSpace 𝓘(ℝ,Model n) x) :
    fderiv ℝ (fderiv ℝ (prefixNormalCost x 1)) (0,p) (u,0) (v,0)=normalHessian x p u v := by
  let V := TangentSpace 𝓘(ℝ,Model n) x
  have hp1 : (1:ℝ) • p∈injectivityDomain x := by simpa only [one_smul] using hp
  have hsym := (prefixNormalCost_contDiffAt hp1).isSymmSndFDerivAt
    (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  have heq := symmetric_bilinear_eq_of_diagonal
    (A := (fderiv ℝ (fderiv ℝ (prefixNormalCost x 1)) (0,p)).bilinearComp
      (ContinuousLinearMap.inl ℝ V V) (ContinuousLinearMap.inl ℝ V V))
    (B := normalHessian x p)
    (fun a b => hsym.eq (a,0) (b,0)) (normalHessian_symm hp)
    (fun a => by simpa only [ContinuousLinearMap.bilinearComp_apply,
      ContinuousLinearMap.inl_apply,one_smul,div_one] using prefixNormalCost_source_hessian hp1 a)
  exact congrArg (fun D : V →L[ℝ] V →L[ℝ] ℝ => D u v) heq

omit [MeasurableSpace M] [BorelSpace M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M] in
lemma normal_contact_twist {v : M → ℝ} (hv : Continuous v) {x : M}
    {a p : TangentSpace 𝓘(ℝ,Model n) x}
    (hB : DifferentiableAt ℝ (prefixNormalCost x 1) (a,p))
    (hcontact : contactGap (cTransform v) v (riemannianExp x a) (riemannianExp x p)=0)
    {g : TangentSpace 𝓘(ℝ,Model n) x}
    (hg : HasFDerivAt (fun h => cTransform v (riemannianExp x h)) (innerSL ℝ g) a) :
    (fderiv ℝ (prefixNormalCost x 1) (a,p)).comp
      (ContinuousLinearMap.inl ℝ _ _)= -(innerSL ℝ g) := by
  let V := TangentSpace 𝓘(ℝ,Model n) x
  have hmin : IsLocalMin (fun h : V => cTransform v (riemannianExp x h)+
      prefixNormalCost x 1 (h,p)) a := by
    apply Filter.Eventually.of_forall
    intro h
    have H := cTransform_gap_nonneg hv (riemannianExp x h) (riemannianExp x p)
    simp only [contactGap] at H hcontact
    simp only [prefixNormalCost,one_smul,div_one]
    linarith
  have hd := hB.hasFDerivAt.comp (f := fun h : V => (h,p)) a
    ((hasFDerivAt_id a).prodMk (hasFDerivAt_const p a))
  have hz := hmin.hasFDerivAt_eq_zero (hg.add hd)
  have H : innerSL ℝ g+(fderiv ℝ (prefixNormalCost x 1) (a,p)).comp
      (ContinuousLinearMap.inl ℝ V V)=0 := by simpa only [ContinuousLinearMap.inl] using hz
  exact eq_neg_of_add_eq_zero_right H

omit [MeasurableSpace M] [BorelSpace M] in
lemma contact_selection_normal_differential {v : M → ℝ} (hv : Continuous v) {x : M}
    {p : TangentSpace 𝓘(ℝ,Model n) x} (hp : p∈activeLogs (n := n) v x)
    (hpI : p∈injectivityDomain x)
    (hDiff : MDifferentiableAt 𝓘(ℝ,Model n) 𝓘(ℝ,ℝ) (cTransform v) x)
    {A : TangentSpace 𝓘(ℝ,Model n) x →L[ℝ] TangentSpace 𝓘(ℝ,Model n) x}
    (hA : ∀ u w, inner ℝ (A u) w=inner ℝ u (A w))
    (hexp : HasQuadraticExpansion (fun h => cTransform v (riemannianExp x h)) p A)
    {T : M → M} (hT : ∀ z, contactGap (cTransform v) v z (T z)=0) :
    ∃ r>0, ∃ q : TangentSpace 𝓘(ℝ,Model n) x → TangentSpace 𝓘(ℝ,Model n) x,
      q 0=p ∧ ContinuousAt q 0 ∧
      (∀ᶠ h in 𝓝 0, riemannianExp x (q h)=T (riemannianExp x h)) ∧
      HasFDerivWithinAt q (normalHessianOperator x p+A)
        {h | h∈Metric.ball 0 r ∧ DifferentiableAt ℝ (fun z => cTransform v (riemannianExp x z)) h} 0 := by
  let V := TangentSpace 𝓘(ℝ,Model n) x
  let f : V → ℝ := fun h => cTransform v (riemannianExp x h)
  have hTx : T x=riemannianExp x p := contact_unique_of_mdifferentiable hv hDiff (hT x) hp.2
  have hTc : ContinuousAt T x := contact_selection_continuousAt (continuous_cTransform hv) hv hT
    (fun y hy => contact_unique_of_mdifferentiable hv hDiff hy (hT x))
  obtain ⟨κ,hκ0,hκ,hκright⟩ := exists_normal_local_inverse_at hpI
  let q : V → V := fun h => κ (T (riemannianExp x h))
  have hq0 : q 0=p := by simp only [q,riemannianExp_zero,hTx,hκ0]
  have hTc' : ContinuousAt T (riemannianExp (n := n) x (0:V)) := by
    simpa only [riemannianExp_zero] using hTc
  have hcT : ContinuousAt (fun h : V => T (riemannianExp x h)) 0 :=
    hTc'.comp (contMDiff_riemannianExp_fiber x 0).continuousAt
  have hκ' : ContinuousAt κ (T (riemannianExp (n := n) x (0:V))) := by
    simpa only [riemannianExp_zero,hTx] using hκ.continuousAt
  have hqc : ContinuousAt q 0 := hκ'.comp (f := fun h : V => T (riemannianExp x h)) hcT
  have hqright : ∀ᶠ h in 𝓝 (0:V), riemannianExp x (q h)=T (riemannianExp x h) :=
    (show Tendsto (fun h : V => T (riemannianExp x h)) (𝓝 0) (𝓝 (riemannianExp x p)) from by
      simpa only [ContinuousAt,riemannianExp_zero,hTx] using hcT).eventually hκright
  obtain ⟨r,hr,K,hK,hconv⟩ := cTransform_uniform_smooth_coordinate_semiconvex
    (contMDiff_riemannianExp_fiber (n := n) x 0)
  let s : Set V := {h | h∈Metric.ball 0 r ∧ DifferentiableAt ℝ f h}
  let g : V → V := fun h => (InnerProductSpace.toDual ℝ V).symm (fderiv ℝ f h)
  have hg0 : g 0=p := by
    change (InnerProductSpace.toDual ℝ V).symm (fderiv ℝ f 0)=p
    rw [hexp.hasFDerivAt.fderiv]
    exact (InnerProductSpace.toDual ℝ V).symm_apply_apply p
  have hgD (h : V) (hh : h∈s) : HasFDerivAt f (innerSL ℝ (g h)) h := by
    apply hh.2.hasFDerivAt.congr_fderiv
    exact ((InnerProductSpace.toDual ℝ V).apply_symm_apply _).symm
  have hg := semiconvex_gradient_hasFDerivWithinAt hA hexp hr (K := 2*K)
    (by simpa only [mul_div_cancel_left₀ K (show (2:ℝ)≠0 by norm_num)] using hconv v hv)
  have hp1 : (1:ℝ) • p∈injectivityDomain x := by simpa only [one_smul] using hpI
  have hB := (prefixNormalCost_contDiffAt hp1).of_le (m := 2)
    (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  have hnearB : ∀ᶠ h in 𝓝 (0:V), DifferentiableAt ℝ (prefixNormalCost x 1) (h,q h) := by
    have H := (hB.eventually (by norm_num)).mono
      (fun z hz => hz.differentiableAt (by norm_num))
    apply (continuousAt_id.prodMk hqc).tendsto.eventually
    simpa only [hq0,id_eq] using H
  refine ⟨r,hr,q,hq0,hqc,hqright,?_⟩
  apply twist_hasFDerivWithinAt hB
  · intro u w
    rw [prefixNormalCost_source_hessian_full hpI,inner_normalHessianOperator]
  · intro u w
    rw [hB.isSymmSndFDerivAt (by norm_num) |>.eq]
    simpa only [real_inner_comm] using (prefixNormalCost_hessian_blocks (show (0:ℝ)<1 by norm_num) hp1 w u).1
  · exact hq0
  · exact hqc
  · exact hg
  · filter_upwards [self_mem_nhdsWithin,mem_nhdsWithin_of_mem_nhds hqright,
      mem_nhdsWithin_of_mem_nhds hnearB] with h hh he hB'
    apply normal_contact_twist hv hB' _ (hgD h hh)
    rw [he]
    exact hT _
  · apply normal_contact_twist hv (hB.differentiableAt (by norm_num))
    · simpa only [riemannianExp_zero] using hp.2
    · change HasFDerivAt f (innerSL ℝ (g 0)) 0
      rw [hg0]
      exact hexp.hasFDerivAt

end ContactDifferential
end WeakMTWTransport

end

end

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Contact_ContactCharts2
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
open Set Filter Manifold Bundle
open scoped Topology ContDiff

namespace WeakMTWTransport
section ContactCharts
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

omit [MeasurableSpace M] [BorelSpace M] in
lemma contact_selection_chart_differential_full_oai {v : M → ℝ} (hv : Continuous v)
    {T : M → M} (hT : ∀ z, contactGap (cTransform v) v z (T z)=0)
    {G : Set M} (hG : ∀ z∈G, MDifferentiableAt 𝓘(ℝ,Model n) 𝓘(ℝ,ℝ) (cTransform v) z)
    {x : M} (hxG : x∈G) {p : TangentSpace 𝓘(ℝ,Model n) x}
    (hp : p∈activeLogs (n := n) v x) (hpI : p∈injectivityDomain x)
    {A : TangentSpace 𝓘(ℝ,Model n) x →L[ℝ] TangentSpace 𝓘(ℝ,Model n) x}
    (hA : ∀ u w, inner ℝ (A u) w=inner ℝ u (A w))
    (hexp : HasQuadraticExpansion (fun h => cTransform v (riemannianExp x h)) p A)
    (a b : M) (hGs : G⊆(extChartAt 𝓘(ℝ,Model n) a).source)
    (hTxs : T x∈(extChartAt 𝓘(ℝ,Model n) b).source) :
    ∃ R : Model n →L[ℝ] TangentSpace 𝓘(ℝ,Model n) x,
    ∃ S : TangentSpace 𝓘(ℝ,Model n) x →L[ℝ] Model n,
      HasFDerivWithinAt
        ((extChartAt 𝓘(ℝ,Model n) b) ∘ T ∘ (extChartAt 𝓘(ℝ,Model n) a).symm)
        (S.comp ((normalHessianOperator x p+A).comp R))
        ((extChartAt 𝓘(ℝ,Model n) a) '' G) ((extChartAt 𝓘(ℝ,Model n) a) x) ∧
      S=fderiv ℝ ((extChartAt 𝓘(ℝ,Model n) b) ∘ riemannianExp (n := n) x) p ∧
      (fderiv ℝ ((extChartAt 𝓘(ℝ,Model n) a) ∘ riemannianExp (n := n) x) 0).comp R=
        ContinuousLinearMap.id ℝ (Model n) := by
  let V := TangentSpace 𝓘(ℝ,Model n) x
  let d := extChartAt 𝓘(ℝ,Model n) a
  let e := extChartAt 𝓘(ℝ,Model n) b
  have hx : x∈d.source := hGs hxG
  have hDx := hG x hxG
  have hTx : T x=riemannianExp x p := contact_unique_of_mdifferentiable hv hDx (hT x) hp.2
  obtain ⟨r,hr,q,hq0,hqc,hqright,hq⟩ :=
    contact_selection_normal_differential hv hp hpI hDx hA hexp hT
  obtain ⟨κ,hκ0,hκ,hκright⟩ := exists_normal_local_inverse_at (zero_mem_injectivityDomain (n := n) x)
  simp only [riemannianExp_zero] at hκ0 hκ hκright
  let η : Model n → V := κ ∘ d.symm
  let ξ : V → Model n := e ∘ riemannianExp x
  have hη0 : η (d x)=0 := by simp only [η,Function.comp_apply,d.left_inv hx,hκ0]
  have hdi : ContMDiffAt 𝓘(ℝ,Model n) 𝓘(ℝ,Model n) ∞ d.symm (d x) :=
    (contMDiffOn_extChartAt_symm a).contMDiffAt
      ((isOpen_extChartAt_target a).mem_nhds (d.map_source hx))
  have hη : ContDiffAt ℝ ∞ η (d x) := by
    apply ContMDiffAt.contDiffAt
    apply ContMDiffAt.comp (d x) _ hdi
    simpa only [d.left_inv hx] using hκ
  have hξ : ContDiffAt ℝ ∞ ξ p := by
    apply ContMDiffAt.contDiffAt
    apply ContMDiffAt.comp p _ (contMDiff_riemannianExp_fiber x p)
    apply contMDiffAt_extChartAt'
    simpa only [←hTx,extChartAt_source] using hTxs
  have hηt : Tendsto η (𝓝 (d x)) (𝓝 (0:V)) := by
    simpa only [ContinuousAt,hη0] using hη.continuousAt
  have hdiT : Tendsto d.symm (𝓝 (d x)) (𝓝 x) := by
    simpa only [ContinuousAt,d.left_inv hx] using hdi.continuousAt
  have hηright : ∀ᶠ z in 𝓝 (d x), riemannianExp x (η z)=d.symm z := hdiT.eventually hκright
  let s : Set V := {h | h∈Metric.ball 0 r ∧
    DifferentiableAt ℝ (fun z => cTransform v (riemannianExp x z)) h}
  have hηs : ∀ᶠ z in 𝓝[d '' G] (d x), η z∈s := by
    filter_upwards [self_mem_nhdsWithin,mem_nhdsWithin_of_mem_nhds hηright,
      mem_nhdsWithin_of_mem_nhds (hηt.eventually (Metric.ball_mem_nhds 0 hr))] with z hz he hzball
    refine ⟨hzball,?_⟩
    obtain ⟨w,hw,rfl⟩ := hz
    have hew : riemannianExp x (η (d w))=w := by simpa only [d.left_inv (hGs hw)] using he
    have H := (show MDifferentiableAt 𝓘(ℝ,Model n) 𝓘(ℝ,ℝ) (cTransform v)
        (riemannianExp x (η (d w))) from hew.symm ▸ hG w hw).comp (η (d w))
        ((contMDiff_riemannianExp_fiber x _).mdifferentiableAt (by simp))
    exact H.differentiableAt
  have hηwt : Tendsto η (𝓝[d '' G] (d x)) (𝓝[s] (η (d x))) := by
    rw [hη0]
    exact tendsto_nhdsWithin_iff.mpr ⟨hηt.mono_left nhdsWithin_le_nhds,hηs⟩
  let R := fderiv ℝ η (d x)
  let S := fderiv ℝ ξ p
  have hWq : HasFDerivWithinAt q (normalHessianOperator x p+A) s (η (d x)) := by
    simpa only [hη0] using hq
  have hqη := hWq.comp_of_tendsto (d x)
    (hη.differentiableAt (by simp)).hasFDerivAt.hasFDerivWithinAt hηwt
  have hξd : HasFDerivAt ξ S ((q ∘ η) (d x)) := by
    simpa only [Function.comp_apply,hη0,hq0] using
      (hξ.differentiableAt (by simp)).hasFDerivAt
  refine ⟨R,S,?_,rfl,?_⟩
  · apply (hξd.comp_hasFDerivWithinAt (d x) hqη).congr_of_eventuallyEq
    · apply Filter.Eventually.filter_mono nhdsWithin_le_nhds
      filter_upwards [hηright,hηt.eventually hqright] with z hz hqz
      simp only [Function.comp_apply,ξ]
      rw [hqz,hz]
    · change e (T (d.symm (d x)))=ξ (q (η (d x)))
      simp only [ξ,Function.comp_apply,hη0,hq0,d.left_inv hx,hTx]
  · let χ : V → Model n := d ∘ riemannianExp (n := n) x
    have hχ : ContDiffAt ℝ ∞ χ 0 := by
      apply ContMDiffAt.contDiffAt
      apply ContMDiffAt.comp 0 _ (contMDiff_riemannianExp_fiber x 0)
      apply contMDiffAt_extChartAt'
      simpa only [riemannianExp_zero,d,extChartAt_source] using hx
    have hχd : HasFDerivAt χ (fderiv ℝ χ 0) (η (d x)) := by
      simpa only [hη0] using (hχ.differentiableAt (by simp)).hasFDerivAt
    have hprod := hχd.comp (d x) (hη.differentiableAt (by simp)).hasFDerivAt
    have hEq : (χ ∘ η)=ᶠ[𝓝 (d x)] id := by
      filter_upwards [hηright,(isOpen_extChartAt_target a).mem_nhds (d.map_source hx)] with z hz hzt
      change d (riemannianExp x (η z))=z
      rw [hz,d.right_inv hzt]
    exact (hprod.congr_of_eventuallyEq hEq.symm).unique (hasFDerivAt_id (d x))

end ContactCharts
end WeakMTWTransport

end

end

end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.WeakMTWTransport.contact_selection_chart_differential_full_oai.{u_1} := @OAI.WeakMTWTransport.contact_selection_chart_differential_full_oai.{u_1}
