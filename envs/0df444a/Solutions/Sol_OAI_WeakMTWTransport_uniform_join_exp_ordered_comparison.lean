-- Prove2me | solution 1 for OAI.WeakMTWTransport.uniform_join_exp_ordered_comparison
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T19:37:17.466505+00:00
-- url     : https://prove2.me/submissions/0d3587ae-0556-4680-86e7-a05ca7d2b2d9

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
-- module Solutions.OAIQ232_BH.BiholderTransport_Coordinates_FactorNorm
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
section FactorNorm
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma prefix_log_fderiv_exp_norm {x y : M} {t : ℝ}
    {p : TangentSpace 𝓘(ℝ,Model n) x}
    {q : TangentSpace 𝓘(ℝ,Model n) x → TangentSpace 𝓘(ℝ,Model n) y}
    (hq : DifferentiableAt ℝ q p)
    (hqr : ∀ᶠ a in 𝓝 p, riemannianExp y (q a)=riemannianExp x (t • a))
    (v : TangentSpace 𝓘(ℝ,Model n) x) :
    ‖mfderiv 𝓘(ℝ,TangentSpace 𝓘(ℝ,Model n) y) 𝓘(ℝ,Model n)
      (riemannianExp y) (q p) (fderiv ℝ q p v)‖=
    ‖mfderiv 𝓘(ℝ,TangentSpace 𝓘(ℝ,Model n) x) 𝓘(ℝ,Model n)
      (riemannianExp x) (t • p) (t • v)‖ := by
  let X := TangentSpace 𝓘(ℝ,Model n) x
  let Y := TangentSpace 𝓘(ℝ,Model n) y
  have he := (contMDiff_riemannianExp_fiber y (q p)).mdifferentiableAt (by simp)
  have hD := he.hasMFDerivAt.comp p hq.hasFDerivAt.hasMFDerivAt
  have hqr' : (riemannianExp y ∘ q) =ᶠ[𝓝 p] (fun a : X => riemannianExp x (t • a)) := hqr
  have hD' := hD.congr_of_eventuallyEq hqr'.symm
  have hscale : HasFDerivAt (fun a : X => t • a) (t • ContinuousLinearMap.id ℝ X) p :=
    (t • ContinuousLinearMap.id ℝ X).hasFDerivAt
  have hExp := ((contMDiff_riemannianExp_fiber x (t • p)).mdifferentiableAt
    (by simp)).hasMFDerivAt.comp p hscale.hasMFDerivAt
  have hN := congrArg (fun L : X →L[ℝ] TangentSpace 𝓘(ℝ,Model n)
      (riemannianExp x (t • p)) => ‖L v‖) (hD'.mfderiv.symm.trans hExp.mfderiv)
  have he0 := hqr.self_of_nhds
  convert! hN using 1
  all_goals try with_reducible_and_instances rfl
  congr 1
  rw [he0]

end FactorNorm
end WeakMTWTransport

end

end

section

noncomputable section
open Set Filter Manifold Bundle ContinuousLinearMap
open scoped Topology ContDiff

namespace WeakMTWTransport
section UniformPieces
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma suffix_log_total_eq_reverse {x : M}
    {p : TangentSpace 𝓘(ℝ,Model n) x} {t : ℝ}
    (hp : p∈minimizingVectors x) (ht : 0<t) (ht1 : t<1)
    {r : TangentSpace 𝓘(ℝ,Model n) (riemannianExp x p)}
    (hr : r∈injectivityDomain (riemannianExp x p))
    (her : riemannianExp (riemannianExp x p) r=riemannianExp x (t • p)) :
    (⟨riemannianExp x p,r⟩ : TangentBundle 𝓘(ℝ,Model n) M)=
      reverseRay (tangentScale (1-t) (sprayFlow t
        (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M))) := by
  let z : TangentBundle 𝓘(ℝ,Model n) M := ⟨x,p⟩
  let s := tangentScale (1-t) (sprayFlow t z)
  have hs : s.2∈injectivityDomain s.1 := proper_suffix_in_injectivityDomain hp ht ht1 le_rfl
  have hrev := reverseRay_injectivityDomain hs
  have he : (reverseRay s).1=riemannianExp x p := by
    change (sprayFlow 1 s).1=riemannianExp x p
    rw [←riemannianExp_eq_sprayFlow]
    exact shifted_exp_endpoint x p t
  have hEnd := reverseRay_endpoint s
  change riemannianExp (reverseRay s).1 (reverseRay s).2=(sprayFlow t z).1 at hEnd
  rw [←riemannianExp_smul] at hEnd
  change (⟨riemannianExp x p,r⟩ : TangentBundle 𝓘(ℝ,Model n) M)=reverseRay s
  generalize hdef : reverseRay s=w at hrev he hEnd ⊢
  rcases w with ⟨y,w⟩
  dsimp only at he hrev hEnd
  subst y
  have hrw : r=w := riemannianExp_injOn_injectivityDomain _ hr hrev (her.trans hEnd.symm)
  cases hrw
  rfl

lemma uniform_split_exp_bounds :
    ∃ l u : ℝ, 0<l ∧ 0<u ∧ ∀ z : TangentBundle 𝓘(ℝ,Model n) M,
      z.2∈minimizingVectors z.1 → ∀ t∈Icc (1/4:ℝ) (3/4),
      (∀ v, l*‖v‖≤‖mfderiv 𝓘(ℝ,TangentSpace 𝓘(ℝ,Model n) z.1) 𝓘(ℝ,Model n)
        (riemannianExp z.1) (t • z.2) v‖ ∧
        ‖mfderiv 𝓘(ℝ,TangentSpace 𝓘(ℝ,Model n) z.1) 𝓘(ℝ,Model n)
        (riemannianExp z.1) (t • z.2) v‖≤u*‖v‖) ∧
      (∀ v, let r := reverseRay (tangentScale (1-t) (sprayFlow t z));
        l*‖v‖≤‖mfderiv 𝓘(ℝ,TangentSpace 𝓘(ℝ,Model n) r.1) 𝓘(ℝ,Model n)
          (riemannianExp r.1) r.2 v‖ ∧
        ‖mfderiv 𝓘(ℝ,TangentSpace 𝓘(ℝ,Model n) r.1) 𝓘(ℝ,Model n)
          (riemannianExp r.1) r.2 v‖≤u*‖v‖) := by
  let G := {z : TangentBundle 𝓘(ℝ,Model n) M | z.2∈minimizingVectors z.1}
  let S := Icc (1/4:ℝ) (3/4) ×ˢ G
  let P : ℝ × TangentBundle 𝓘(ℝ,Model n) M → TangentBundle 𝓘(ℝ,Model n) M :=
    fun q => tangentScale q.1 q.2
  let R : ℝ × TangentBundle 𝓘(ℝ,Model n) M → TangentBundle 𝓘(ℝ,Model n) M :=
    fun q => reverseRay (tangentScale (1-q.1) (sprayFlow q.1 q.2))
  have hP : Continuous P := contMDiff_tangentScale.continuous
  have hR : Continuous R := continuous_reverseRay.comp (contMDiff_tangentScale.continuous.comp
    ((continuous_const.sub continuous_fst).prodMk contMDiff_sprayFlow.continuous))
  have hS : IsCompact S := isCompact_Icc.prod (isCompact_total_minimizingVectors (n := n) (M := M))
  have hK : IsCompact (P '' S ∪ R '' S) := (hS.image hP).union (hS.image hR)
  have hI : ∀ w∈P '' S ∪ R '' S, w.2∈injectivityDomain w.1 := by
    intro w hw
    rcases hw with hw | hw
    · rcases hw with ⟨⟨t,z⟩,htz,rfl⟩
      exact contracted_minimizer_mem_injectivityDomain htz.2 (by linarith [htz.1.1])
        (by linarith [htz.1.2])
    · rcases hw with ⟨⟨t,z⟩,htz,rfl⟩
      exact reverseRay_injectivityDomain (proper_suffix_in_injectivityDomain htz.2
        (by linarith [htz.1.1]) (by linarith [htz.1.2]) le_rfl)
  obtain ⟨l,u,hl,hu,H⟩ := compact_exp_differential_bounds hK hI
  refine ⟨l,u,hl,hu,?_⟩
  intro z hz t ht
  exact ⟨H (P (t,z)) (Or.inl (mem_image_of_mem _ ⟨ht,hz⟩)),
    H (R (t,z)) (Or.inr (mem_image_of_mem _ ⟨ht,hz⟩))⟩

end UniformPieces
end WeakMTWTransport

end

end

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Coordinates_UniformLog
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
section UniformLog
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma uniform_suffix_log_derivative_bounds :
    ∃ c C : ℝ, 0 < c ∧ 0<C ∧ ∀ x : M, ∀ p : TangentSpace 𝓘(ℝ,Model n) x,
      p∈minimizingVectors x → ∀ t∈Icc (1/4:ℝ) (3/4),
      ∀ q : TangentSpace 𝓘(ℝ,Model n) x → TangentSpace 𝓘(ℝ,Model n) (riemannianExp x p),
      DifferentiableAt ℝ q p → q p∈injectivityDomain (riemannianExp x p) →
      (∀ᶠ a in 𝓝 p, riemannianExp (riemannianExp x p) (q a)=riemannianExp x (t • a)) →
      ∀ v, c*‖v‖≤‖fderiv ℝ q p v‖ ∧ ‖fderiv ℝ q p v‖≤C*‖v‖ := by
  obtain ⟨l,u,hl,hu,H⟩ := uniform_split_exp_bounds (n := n) (M := M)
  refine ⟨l/(4*u),u/l,div_pos hl (mul_pos (by norm_num) hu),div_pos hu hl,?_⟩
  intro x p hp t ht q hq hqI hqr v
  have htpos : 0<t := by linarith [ht.1]
  have htone : t<1 := by linarith [ht.2]
  have htotal := suffix_log_total_eq_reverse hp htpos htone hqI hqr.self_of_nhds
  have hr := (H (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M) hp t ht).2
  change ∀ v, let r := reverseRay (tangentScale (1-t) (sprayFlow t
      (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M)));
      l*‖v‖≤‖mfderiv 𝓘(ℝ,TangentSpace 𝓘(ℝ,Model n) r.1) 𝓘(ℝ,Model n)
        (riemannianExp r.1) r.2 v‖ ∧
      ‖mfderiv 𝓘(ℝ,TangentSpace 𝓘(ℝ,Model n) r.1) 𝓘(ℝ,Model n)
        (riemannianExp r.1) r.2 v‖≤u*‖v‖ at hr
  rw [←htotal] at hr
  have hb := hr (fderiv ℝ q p v)
  dsimp only at hb
  rw [prefix_log_fderiv_exp_norm hq hqr v] at hb
  change l*‖fderiv ℝ q p v‖≤‖mfderiv 𝓘(ℝ,TangentSpace 𝓘(ℝ,Model n) x) 𝓘(ℝ,Model n)
      (riemannianExp x) (t • p) (t • v)‖ ∧
    ‖mfderiv 𝓘(ℝ,TangentSpace 𝓘(ℝ,Model n) x) 𝓘(ℝ,Model n)
      (riemannianExp x) (t • p) (t • v)‖≤u*‖fderiv ℝ q p v‖ at hb
  have hpre := (H (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M) hp t ht).1 (t • v)
  change l*‖t • v‖≤‖mfderiv 𝓘(ℝ,TangentSpace 𝓘(ℝ,Model n) x) 𝓘(ℝ,Model n)
      (riemannianExp x) (t • p) (t • v)‖ ∧
    ‖mfderiv 𝓘(ℝ,TangentSpace 𝓘(ℝ,Model n) x) 𝓘(ℝ,Model n)
      (riemannianExp x) (t • p) (t • v)‖≤u*‖t • v‖ at hpre
  rw [norm_smul_of_nonneg htpos.le] at hpre
  constructor
  · rw [div_mul_eq_mul_div,div_le_iff₀ (mul_pos (by norm_num) hu)]
    have hmul := mul_le_mul_of_nonneg_right ht.1 (norm_nonneg v)
    have hh := mul_le_mul_of_nonneg_left hmul hl.le
    nlinarith [hpre.1.trans hb.2]
  · rw [div_mul_eq_mul_div,le_div_iff₀ hl]
    have hmul := mul_le_mul_of_nonneg_right htone.le (norm_nonneg v)
    have hh := mul_le_mul_of_nonneg_left hmul hu.le
    nlinarith [hb.1.trans hpre.2]

end UniformLog
end WeakMTWTransport

end

end

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_CostGeometry_SplitEndpoint
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
section SplitEndpoint
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma diagonalSplitAction_endpoint_gradient {x : M}
    {p v : TangentSpace 𝓘(ℝ,Model n) x} {t : ℝ}
    {r : TangentSpace 𝓘(ℝ,Model n) (riemannianExp x p)}
    (hr : r∈injectivityDomain (riemannianExp x p))
    (heq : riemannianExp (riemannianExp x p) r=riemannianExp x (t • v))
    (hF : DifferentiableAt ℝ (diagonalSplitAction x t) (p,v))
    (k : TangentSpace 𝓘(ℝ,Model n) x) :
    fderiv ℝ (diagonalSplitAction x t) (p,v) (k,0)=
      -inner ℝ r (mfderiv 𝓘(ℝ,TangentSpace 𝓘(ℝ,Model n) x) 𝓘(ℝ,Model n)
        (riemannianExp x) p k)/(1-t) := by
  let X := TangentSpace 𝓘(ℝ,Model n) x
  let y := riemannianExp x p
  have hc := cost_start_gradient_of_injectivityDomain hr
  rw [heq] at hc
  have hc' : HasMFDerivAt 𝓘(ℝ,Model n) 𝓘(ℝ,ℝ)
      (fun z => cost (riemannianExp x (t • v)) z) y (innerSL ℝ (-r)) := by
    have hswap : (fun z => cost (riemannianExp x (t • v)) z)=
        (fun z => cost z (riemannianExp x (t • v))) := funext (fun z => cost_symm _ _)
    rw [hswap]
    exact hc
  have hE := (contMDiff_riemannianExp_fiber x p).mdifferentiableAt (by simp)
  have hD := hc'.comp p hE.hasMFDerivAt
  have hD' : HasFDerivAt (fun w : X => cost (riemannianExp x (t • v)) (riemannianExp x w))
      ((innerSL ℝ (-r)).comp (mfderiv 𝓘(ℝ,X) 𝓘(ℝ,Model n) (riemannianExp x) p)) p := by
    convert! hD.hasFDerivAt using 1
    all_goals try with_reducible_and_instances rfl
  have hpart := (hD'.mul_const (1-t)⁻¹).const_add
    (cost x (riemannianExp x (t • v))/t)
  have heqfun : (fun w : X => diagonalSplitAction x t (w,v)) =
      (fun w : X => cost x (riemannianExp x (t • v))/t +
        cost (riemannianExp x (t • v)) (riemannianExp x w)*(1-t)⁻¹) := by
    funext w
    simp only [diagonalSplitAction,splitNormalAction,riemannianExp_zero,div_eq_mul_inv]
  rw [←heqfun] at hpart
  have hl := (hasFDerivAt_id (𝕜 := ℝ) p).prodMk (hasFDerivAt_const v p)
  have hfull := hF.hasFDerivAt.comp (f := fun w : X => (w,v)) p hl
  have H := congrArg (fun A : X →L[ℝ] ℝ => A k) (hfull.unique hpart)
  change fderiv ℝ (diagonalSplitAction x t) (p,v) (k,0)=
    (1-t)⁻¹ * inner ℝ (-r) (mfderiv 𝓘(ℝ,X) 𝓘(ℝ,Model n) (riemannianExp x) p k) at H
  rw [H,inner_neg_left,div_eq_mul_inv,mul_comm]

lemma diagonalSplitAction_mixed_endpoint {x : M}
    {p : TangentSpace 𝓘(ℝ,Model n) x} {t : ℝ}
    (hleft : t • p∈injectivityDomain x)
    (hright : (1-t) • (sprayFlow t (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M)).2∈
      injectivityDomain (sprayFlow t (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M)).1)
    {q : TangentSpace 𝓘(ℝ,Model n) x → TangentSpace 𝓘(ℝ,Model n) (riemannianExp x p)}
    (hq : DifferentiableAt ℝ q p)
    (hqI : ∀ᶠ v in 𝓝 p, q v∈injectivityDomain (riemannianExp x p))
    (hqr : ∀ᶠ v in 𝓝 p, riemannianExp (riemannianExp x p) (q v)=riemannianExp x (t • v))
    (a k : TangentSpace 𝓘(ℝ,Model n) x) :
    fderiv ℝ (fderiv ℝ (diagonalSplitAction x t)) (p,p) (0,a) (k,0)=
      -inner ℝ (fderiv ℝ q p a) (mfderiv 𝓘(ℝ,TangentSpace 𝓘(ℝ,Model n) x) 𝓘(ℝ,Model n)
        (riemannianExp x) p k)/(1-t) := by
  let X := TangentSpace 𝓘(ℝ,Model n) x
  let F := diagonalSplitAction (n := n) x t
  let E := mfderiv 𝓘(ℝ,X) 𝓘(ℝ,Model n) (riemannianExp x) p
  have hF : ContDiffAt ℝ 2 F (p,p) := (diagonalSplitAction_contDiffAt hleft hright).of_le
    (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  have hdf := (hF.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hl := (hasFDerivAt_const p p).prodMk (hasFDerivAt_id (𝕜 := ℝ) p)
  have hD := ((hdf.hasFDerivAt.comp (f := fun v : X => (p,v)) p hl).clm_apply
    (hasFDerivAt_const (k,(0:X)) p)).fderiv
  have hnF : ∀ᶠ v : X in 𝓝 p, DifferentiableAt ℝ F (p,v) :=
    (hl.continuousAt.eventually ((hF.of_le (m := 1) (by norm_num)).eventually (by norm_num))).mono
      (fun _ h => h.differentiableAt (by norm_num))
  have heq : (fun v : X => fderiv ℝ F (p,v) (k,0)) =ᶠ[𝓝 p]
      (fun v => -inner ℝ (E k) (q v)*(1-t)⁻¹) := by
    filter_upwards [hnF,hqI,hqr] with v hv hvI hvr
    rw [diagonalSplitAction_endpoint_gradient hvI hvr hv,real_inner_comm,div_eq_mul_inv]
  have hi := (((innerSL ℝ (E k)).hasFDerivAt.comp p hq.hasFDerivAt).neg.mul_const (1-t)⁻¹).fderiv
  have H := congrArg (fun A : X →L[ℝ] ℝ => A a) (hD.symm.trans (heq.fderiv_eq.trans hi))
  simp only [_root_.add_apply,ContinuousLinearMap.comp_apply,_root_.zero_apply,
    map_zero,zero_add,ContinuousLinearMap.flip_apply,ContinuousLinearMap.prod_apply,
    _root_.smul_apply,smul_eq_mul,_root_.neg_apply] at H
  change fderiv ℝ (fderiv ℝ F) (p,p) (0,a) (k,0)=
    (1-t)⁻¹ * (-inner ℝ (E k) (fderiv ℝ q p a)) at H
  rw [H,real_inner_comm,div_eq_mul_inv,mul_comm]

end SplitEndpoint
end WeakMTWTransport

end

end

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Duality_DualFactor
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
namespace WeakMTWTransport
section DualFactor
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

lemma dual_factor_norm_comparison (Q : E →L[ℝ] E) (L A : E →L[ℝ] F)
    {s c C : ℝ} (hs : 0 < s) (hc : 0 < c) (hC : 0 < C)
    (hL : Function.Surjective L)
    (hLn : ∀ k, c * ‖k‖ ≤ ‖L k‖ ∧ ‖L k‖ ≤ C * ‖k‖)
    (h : ∀ a k, s * inner ℝ (Q a) k = inner ℝ (L k) (A a)) (a : E) :
    c * ‖A a‖ ≤ s * ‖Q a‖ ∧ s * ‖Q a‖ ≤ C * ‖A a‖ := by
  constructor
  · obtain ⟨k,hk⟩ := hL (A a)
    have H := h a k
    rw [hk,real_inner_self_eq_norm_sq] at H
    have H1 := real_inner_le_norm (Q a) k
    have H2 := (hLn k).1
    rw [hk] at H2
    by_cases hz : ‖A a‖ = 0
    · rw [hz,mul_zero]; positivity
    · have hp : 0 < ‖A a‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hz)
      have H3 := mul_le_mul_of_nonneg_left H1 hs.le
      have H4 := mul_le_mul_of_nonneg_left H2 (mul_nonneg hs.le (norm_nonneg (Q a)))
      have H5 := mul_le_mul_of_nonneg_left H3 hc.le
      nlinarith
  · have H := h a (Q a)
    rw [real_inner_self_eq_norm_sq] at H
    have H1 := real_inner_le_norm (L (Q a)) (A a)
    have H2 := mul_le_mul_of_nonneg_right (hLn (Q a)).2 (norm_nonneg (A a))
    by_cases hz : ‖Q a‖ = 0
    · rw [hz,mul_zero]; positivity
    · have hp : 0 < ‖Q a‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hz)
      nlinarith

end DualFactor
end WeakMTWTransport

end

end

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_LinearAlgebra_Diagonal
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
open Set Filter Manifold Bundle ContinuousLinearMap
open scoped Topology ContDiff

namespace WeakMTWTransport
section Diagonal
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma diagonal_stationary_hessian_identity {F : E×E → ℝ} {p : E}
    (hF : ContDiffAt ℝ 2 F (p,p))
    (hstat : ∀ᶠ v in 𝓝 p, ∀ k, fderiv ℝ F (v,v) (0,k)=0) (a k : E) :
    fderiv ℝ (fderiv ℝ F) (p,p) (0,a) (0,k)=
      -fderiv ℝ (fderiv ℝ F) (p,p) (a,0) (0,k) := by
  have hdf := (hF.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  let L : E →L[ℝ] E×E := (ContinuousLinearMap.id ℝ E).prod (ContinuousLinearMap.id ℝ E)
  have hD := ((hdf.hasFDerivAt.comp (f := fun v : E => (v,v)) p L.hasFDerivAt).clm_apply
    (hasFDerivAt_const ((0:E),k) p)).fderiv
  have heq : (fun v : E => fderiv ℝ F (v,v) (0,k)) =ᶠ[𝓝 p] (fun _ => (0:ℝ)) :=
    hstat.mono (fun _ h => h k)
  have hz : fderiv ℝ (fun v : E => fderiv ℝ F (v,v) (0,k)) p=0 := by
    rw [heq.fderiv_eq]
    exact (hasFDerivAt_const (0:ℝ) p).fderiv
  have H := congrArg (fun A : E →L[ℝ] ℝ => A a) (hD.symm.trans hz)
  simp only [add_apply,ContinuousLinearMap.comp_apply,zero_apply,map_zero,zero_add,
    ContinuousLinearMap.flip_apply,L,ContinuousLinearMap.prod_apply,ContinuousLinearMap.id_apply] at H
  have hsplit : (a,a)=(a,0)+((0:E),a) := by ext <;> simp
  rw [hsplit,map_add,add_apply] at H
  linarith
end Diagonal
section SplitFactor
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma diagonalSplitAction_hessian_identity {x : M} {p : TangentSpace 𝓘(ℝ,Model n) x}
    {t : ℝ} (ht : 0<t) (ht1 : t<1) (hleft : t • p∈injectivityDomain x)
    (hright : (1-t) • (sprayFlow t (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M)).2∈
      injectivityDomain (sprayFlow t (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M)).1)
    (a k : TangentSpace 𝓘(ℝ,Model n) x) :
    fderiv ℝ (fderiv ℝ (diagonalSplitAction x t)) (p,p) (0,a) (0,k)=
      -fderiv ℝ (fderiv ℝ (diagonalSplitAction x t)) (p,p) (a,0) (0,k) := by
  exact diagonal_stationary_hessian_identity
    ((diagonalSplitAction_contDiffAt hleft hright).of_le
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2))
    ((split_regular_legs_near hleft hright).mono
      (fun v hv k => diagonalSplitAction_stationary ht ht1 hv.1 hv.2 k)) a k

lemma exists_suffix_log_in_prefix_coordinates {x : M}
    {p : TangentSpace 𝓘(ℝ,Model n) x} {t : ℝ}
    (hright : (1-t) • (sprayFlow t (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M)).2∈
      injectivityDomain (sprayFlow t (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M)).1) :
    ∃ q : TangentSpace 𝓘(ℝ,Model n) x →
        TangentSpace 𝓘(ℝ,Model n) (riemannianExp x p),
      ContDiffAt ℝ ∞ q p ∧
      (∀ᶠ v in 𝓝 p, q v∈injectivityDomain (riemannianExp x p)) ∧
      (∀ᶠ v in 𝓝 p, riemannianExp (riemannianExp x p) (q v)=riemannianExp x (t • v)) := by
  let : Nonempty M := ⟨x⟩
  let : MeasurableSpace M := borel M
  let : BorelSpace M := ⟨rfl⟩
  let z : TangentBundle 𝓘(ℝ,Model n) M := ⟨x,p⟩
  let s := tangentScale (1-t) (sprayFlow t z)
  have hs : s.2∈injectivityDomain s.1 := hright
  have hr := reverseRay_injectivityDomain hs
  have he : (reverseRay s).1=riemannianExp x p := by
    change (sprayFlow 1 s).1=riemannianExp x p
    rw [←riemannianExp_eq_sprayFlow]
    exact shifted_exp_endpoint x p t
  have he' := reverseRay_endpoint s
  change riemannianExp (reverseRay s).1 (reverseRay s).2=(sprayFlow t z).1 at he'
  rw [←riemannianExp_smul] at he'
  generalize hrdef : reverseRay s=r at hr he he'
  rcases r with ⟨y,r⟩
  dsimp only at he hr he'
  subst y
  obtain ⟨κ,hκ0,hκ,hκright⟩ := exists_normal_local_inverse_at hr
  rw [he'] at hκ0 hκ hκright
  let q := fun v : TangentSpace 𝓘(ℝ,Model n) x => κ (riemannianExp x (t • v))
  have hE : ContMDiffAt 𝓘(ℝ,TangentSpace 𝓘(ℝ,Model n) x) 𝓘(ℝ,Model n) ∞
      (fun v => riemannianExp x (t • v)) p :=
    (contMDiff_riemannianExp_fiber x _).comp p (show ContDiffAt ℝ ∞ (fun v : TangentSpace 𝓘(ℝ,Model n) x => t • v) p from
      by fun_prop).contMDiffAt
  have hq : ContDiffAt ℝ ∞ q p := (hκ.comp p hE).contDiffAt
  refine ⟨q,hq,?_,hE.continuousAt.eventually hκright⟩
  apply hq.continuousAt.preimage_mem_nhds
  apply (isOpen_injectivityDomain _).mem_nhds
  change κ (riemannianExp x (t • p))∈_
  rw [hκ0]
  exact hr

end SplitFactor
end WeakMTWTransport

end

end

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_LinearAlgebra_JoinOperator
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
section JoinOperator
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

local instance localInst_rbb9510_1 (x : M) : FiniteDimensional ℝ (TangentSpace 𝓘(ℝ,Model n) x) :=
  inferInstanceAs (FiniteDimensional ℝ (Model n))
lemma uniform_join_endpoint_factorization :
    ∃ c C : ℝ, 0 < c ∧ 0<C ∧ ∀ x : M, ∀ p : TangentSpace 𝓘(ℝ,Model n) x,
      p∈minimizingVectors x → ∀ t∈Icc (1/4:ℝ) (3/4),
      ∃ L : TangentSpace 𝓘(ℝ,Model n) x →L[ℝ]
          TangentSpace 𝓘(ℝ,Model n) (riemannianExp x p),
        Function.Bijective L ∧ (∀ v, c*‖v‖≤‖L v‖ ∧ ‖L v‖≤C*‖v‖) ∧ ∀ a k,
          inner ℝ (splitJoinHessianOperator x t p a) k=
            inner ℝ (L k) (mfderiv 𝓘(ℝ,TangentSpace 𝓘(ℝ,Model n) x) 𝓘(ℝ,Model n)
              (riemannianExp x) p a)/(1-t) := by
  obtain ⟨c,C,hc,hC,H⟩ := uniform_suffix_log_derivative_bounds (n := n) (M := M)
  refine ⟨c,C,hc,hC,?_⟩
  intro x p hp t ht
  have htpos : 0<t := by linarith [ht.1]
  have htone : t<1 := by linarith [ht.2]
  have hleft := contracted_minimizer_mem_injectivityDomain hp htpos htone
  have hright := proper_suffix_in_injectivityDomain
    (z := (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M)) hp htpos htone le_rfl
  obtain ⟨q,hq,hqI,hqr⟩ := exists_suffix_log_in_prefix_coordinates hright
  have hqd := hq.differentiableAt (by simp)
  have hLi := prefix_log_fderiv_injective htpos.ne' hleft hqd hqr
  have hLs : Function.Surjective (fderiv ℝ q p) :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (f := (fderiv ℝ q p).toLinearMap) rfl).mp hLi
  refine ⟨fderiv ℝ q p,⟨hLi,hLs⟩,H x p hp t ht q hqd hqI.self_of_nhds hqr,?_⟩
  intro a k
  rw [inner_splitJoinHessianOperator,
    diagonalSplitAction_hessian_identity htpos htone hleft hright]
  have hsym := (diagonalSplitAction_contDiffAt hleft hright).isSymmSndFDerivAt
    (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  rw [hsym.eq (a,0) (0,k),diagonalSplitAction_mixed_endpoint hleft hright hqd hqI hqr]
  ring

end JoinOperator
end WeakMTWTransport

end

end

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Regularity_MinMax
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
open Set
open scoped BigOperators

namespace WeakMTWTransport
section MinMax
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

lemma paired_basis_slice {n : ℕ} (a b : OrthonormalBasis (Fin n) ℝ E) (i : Fin n) :
    ∃ v : E, v ≠ 0 ∧ (∀ j : Fin n, i < j → a.repr v j = 0) ∧
      (∀ j : Fin n, j < i → b.repr v j = 0) :=  by
  classical
  let f : Fin (i.val+1) → Fin n :=  fun j  => ⟨j.val,by omega⟩
  have hf : Function.Injective f :=  by
    intro j k h
    apply Fin.ext
    simpa only [f] using congrArg (fun z : Fin n => z.val) h
  let V :=  Submodule.span ℝ (range (fun j : Fin (i.val+1)  => a (f j)))
  have hdim : Module.finrank ℝ V = i.val+1 :=  by
    exact (finrank_span_eq_card (a.toBasis.linearIndependent.comp f hf)).trans (Fintype.card_fin _)
  let L : V →ₗ[ℝ] (Fin i.val → ℝ) :=
    { toFun :=  fun v j  => b.repr v ⟨j.val,lt_trans j.isLt i.isLt⟩
      map_add' :=  by intros; ext j; simp
      map_smul' :=  by intros; ext j; simp }
  have hk :=  LinearMap.ker_ne_bot_of_finrank_lt (f :=  L) (by
    rw [hdim,Module.finrank_pi,Fintype.card_fin]; omega)
  obtain ⟨v,hv,hv0⟩ :=  (Submodule.ne_bot_iff _).mp hk
  have hvE : (v:E) ≠ 0 :=  by
    intro h
    exact hv0 (Subtype.ext h)
  refine ⟨v,hvE,?_,?_⟩
  · intro j hj
    have H : ∀ w∈V, a.repr w j = 0 :=  by
      intro w hw
      induction hw using Submodule.span_induction with
      | mem w hw  =>
          obtain ⟨k,rfl⟩ :=  hw
          have hne : f k ≠ j :=  by intro h; have :=  congrArg Fin.val h; dsimp [f] at this; omega
          simp [Ne.symm hne]
      | zero  => simp
      | add x y hx hy ihx ihy  => simp [ihx,ihy]
      | smul c x hx ih  => simp [ih]
    exact H v v.property
  · intro j hj
    have H :=  congrFun (show L v = 0 from hv) (⟨j.val,hj⟩ : Fin i.val)
    exact H

lemma eigenvalue_quadratic_expansion {A : E →ₗ[ℝ] E} (hA : A.IsSymmetric)
    {n : ℕ} (hn : Module.finrank ℝ E = n) (v : E) :
    inner ℝ (A v) v = ∑ j, hA.eigenvalues hn j*((hA.eigenvectorBasis hn).repr v j)^2 :=  by
  have H :=  (hA.eigenvectorBasis hn).repr.inner_map_map (A v) v
  rw [←H,PiLp.inner_apply]
  apply Finset.sum_congr rfl
  intro j hj
  rw [hA.eigenvectorBasis_apply_self_apply]
  simp only [RCLike.inner_apply,conj_trivial,RCLike.ofReal_real_eq_id,id_eq]
  ring

omit [FiniteDimensional ℝ E] in
lemma eigenbasis_norm_expansion {n : ℕ} (b : OrthonormalBasis (Fin n) ℝ E) (v : E) :
    ‖v‖^2 = ∑ j, (b.repr v j)^2 :=  by
  rw [←b.repr.norm_map v,EuclideanSpace.real_norm_sq_eq]

end MinMax
end WeakMTWTransport

end

end

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Regularity_NormMinMax
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
open Set
open scoped BigOperators

namespace WeakMTWTransport
section NormMinMax
variable {E F G H : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F] [NormedAddCommGroup G] [InnerProductSpace ℝ G]
  [FiniteDimensional ℝ G] [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [FiniteDimensional ℝ H]

omit [FiniteDimensional ℝ F] in
lemma paired_basis_slice_map {n : ℕ} (a : OrthonormalBasis (Fin n) ℝ E)
    (b : OrthonormalBasis (Fin n) ℝ F) (K : E →ₗ[ℝ] F) (i : Fin n) :
    ∃ v : E, v ≠ 0 ∧ (∀ j : Fin n, i < j → a.repr v j = 0) ∧
      (∀ j : Fin n, j < i → b.repr (K v) j = 0) :=  by
  classical
  let f : Fin (i.val+1) → Fin n :=  fun j  => ⟨j.val,by omega⟩
  have hf : Function.Injective f :=  by
    intro j k h
    apply Fin.ext
    simpa only [f] using congrArg (fun z : Fin n => z.val) h
  let V :=  Submodule.span ℝ (range (fun j : Fin (i.val+1)  => a (f j)))
  have hdim : Module.finrank ℝ V = i.val+1 :=  by
    exact (finrank_span_eq_card (a.toBasis.linearIndependent.comp f hf)).trans (Fintype.card_fin _)
  let L : V →ₗ[ℝ] (Fin i.val → ℝ) :=
    { toFun :=  fun v j  => b.repr (K v) ⟨j.val,lt_trans j.isLt i.isLt⟩
      map_add' :=  by intros; ext j; simp
      map_smul' :=  by intros; ext j; simp }
  have hk :=  LinearMap.ker_ne_bot_of_finrank_lt (f :=  L) (by
    rw [hdim,Module.finrank_pi,Fintype.card_fin]; omega)
  obtain ⟨v,hv,hv0⟩ :=  (Submodule.ne_bot_iff _).mp hk
  have hvE : (v:E) ≠ 0 :=  by
    intro h
    exact hv0 (Subtype.ext h)
  refine ⟨v,hvE,?_,?_⟩
  · intro j hj
    have H : ∀ w∈V, a.repr w j = 0 :=  by
      intro w hw
      induction hw using Submodule.span_induction with
      | mem w hw  =>
          obtain ⟨k,rfl⟩ :=  hw
          have hne : f k ≠ j :=  by intro h; have :=  congrArg Fin.val h; dsimp [f] at this; omega
          simp [Ne.symm hne]
      | zero  => simp
      | add x y hx hy ihx ihy  => simp [ihx,ihy]
      | smul c x hx ih  => simp [ih]
    exact H v v.property
  · intro j hj
    have H :=  congrFun (show L v = 0 from hv) (⟨j.val,hj⟩ : Fin i.val)
    exact H

lemma quadratic_lower_spectral_slice {A : E →ₗ[ℝ] E} (hA : A.IsSymmetric)
    {n : ℕ} (hn : Module.finrank ℝ E = n) (i : Fin n) (v : E)
    (hv : ∀ j : Fin n, i < j → (hA.eigenvectorBasis hn).repr v j = 0) :
    hA.eigenvalues hn i * ‖v‖^2 ≤ inner ℝ (A v) v := by
  rw [eigenvalue_quadratic_expansion hA hn,eigenbasis_norm_expansion (hA.eigenvectorBasis hn),
    Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j hj
  by_cases hji : j ≤ i
  · exact mul_le_mul_of_nonneg_right (hA.eigenvalues_antitone hn hji) (sq_nonneg _)
  · rw [hv j (lt_of_not_ge hji)]; simp

lemma quadratic_upper_spectral_slice {A : E →ₗ[ℝ] E} (hA : A.IsSymmetric)
    {n : ℕ} (hn : Module.finrank ℝ E = n) (i : Fin n) (v : E)
    (hv : ∀ j : Fin n, j < i → (hA.eigenvectorBasis hn).repr v j = 0) :
    inner ℝ (A v) v ≤ hA.eigenvalues hn i * ‖v‖^2 := by
  rw [eigenvalue_quadratic_expansion hA hn,eigenbasis_norm_expansion (hA.eigenvectorBasis hn),
    Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j hj
  by_cases hij : i ≤ j
  · exact mul_le_mul_of_nonneg_right (hA.eigenvalues_antitone hn hij) (sq_nonneg _)
  · rw [hv j (lt_of_not_ge hij)]; simp

lemma ordered_eigenvalue_pullback_comparison {A : E →ₗ[ℝ] E} {B : F →ₗ[ℝ] F}
    (hA : A.IsSymmetric) (hB : B.IsPositive) (K : E →ₗ[ℝ] F)
    {a b c : ℝ} (ha : 0 ≤ a) (hc : 0 ≤ c)
    (hK : ∀ v, ‖K v‖ ≤ c * ‖v‖)
    (h : ∀ v, inner ℝ (A v) v ≤ a * inner ℝ (B (K v)) (K v) + b * ‖v‖^2)
    {n : ℕ} (hnE : Module.finrank ℝ E = n) (hnF : Module.finrank ℝ F = n) (i : Fin n) :
    hA.eigenvalues hnE i ≤ a * c^2 * hB.isSymmetric.eigenvalues hnF i + b := by
  obtain ⟨v,hv,hav,hbv⟩ := paired_basis_slice_map (hA.eigenvectorBasis hnE)
    (hB.isSymmetric.eigenvectorBasis hnF) K i
  have hAv := quadratic_lower_spectral_slice hA hnE i v hav
  have hBv := quadratic_upper_spectral_slice hB.isSymmetric hnF i (K v) hbv
  have hBp := hB.nonneg_eigenvalues hnF i
  have hnorm := sq_le_sq₀ (norm_nonneg (K v)) (mul_nonneg hc (norm_nonneg v)) |>.mpr (hK v)
  have hmul := mul_le_mul_of_nonneg_left hnorm hBp
  have hmul' := mul_le_mul_of_nonneg_left (hBv.trans hmul) ha
  have hpos : 0 < ‖v‖^2 := sq_pos_of_ne_zero (norm_ne_zero_iff.mpr hv)
  have H := h v
  nlinarith

lemma ordered_singularValues_pullback {A : E →ₗ[ℝ] G} {B : F →ₗ[ℝ] H}
    (K : E →ₗ[ℝ] F) {a c : ℝ} (ha : 0 ≤ a) (hc : 0 ≤ c)
    (hK : ∀ v, ‖K v‖ ≤ c * ‖v‖) (h : ∀ v, ‖A v‖ ≤ a * ‖B (K v)‖)
    {n : ℕ} (hnE : Module.finrank ℝ E = n) (hnF : Module.finrank ℝ F = n)
    (i : Fin n) : A.singularValues i ≤ a * c * B.singularValues i := by
  have H := ordered_eigenvalue_pullback_comparison A.isSymmetric_adjoint_comp_self
    B.isPositive_adjoint_comp_self K (sq_nonneg a) hc hK (b := 0) (fun v => by
      simp only [LinearMap.comp_apply,LinearMap.adjoint_inner_left,real_inner_self_eq_norm_sq,
        zero_mul,add_zero]
      nlinarith [h v,norm_nonneg (A v),norm_nonneg (B (K v))]) hnE hnF i
  rw [←A.sq_singularValues_fin hnE,←B.sq_singularValues_fin hnF] at H
  have hAp := A.singularValues_nonneg i
  have hBp := B.singularValues_nonneg i
  have hprod := mul_nonneg (mul_nonneg ha hc) hBp
  nlinarith

end NormMinMax
end WeakMTWTransport

end

end

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_LinearAlgebra_PositiveSingular
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
open scoped BigOperators

namespace WeakMTWTransport
section PositiveSingular
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

lemma eigenbasis_operator_norm_expansion {A : E →ₗ[ℝ] E} (hA : A.IsSymmetric)
    {n : ℕ} (hn : Module.finrank ℝ E=n) (v : E) :
    ‖A v‖^2 = ∑ j, (hA.eigenvalues hn j)^2*((hA.eigenvectorBasis hn).repr v j)^2 := by
  rw [eigenbasis_norm_expansion (hA.eigenvectorBasis hn)]
  apply Finset.sum_congr rfl
  intro j hj
  rw [hA.eigenvectorBasis_apply_self_apply]
  simp only [RCLike.ofReal_real_eq_id,id_eq,mul_pow]

lemma positive_norm_lower_spectral_slice {A : E →ₗ[ℝ] E} (hA : A.IsPositive)
    {n : ℕ} (hn : Module.finrank ℝ E=n) (i : Fin n) (v : E)
    (hv : ∀ j : Fin n, i < j → (hA.isSymmetric.eigenvectorBasis hn).repr v j=0) :
    (hA.isSymmetric.eigenvalues hn i)^2*‖v‖^2≤‖A v‖^2 := by
  rw [eigenbasis_operator_norm_expansion hA.isSymmetric hn,
    eigenbasis_norm_expansion (hA.isSymmetric.eigenvectorBasis hn),Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j hj
  by_cases hji : j ≤ i
  · apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
    exact pow_le_pow_left₀ (hA.nonneg_eigenvalues hn i)
      (hA.isSymmetric.eigenvalues_antitone hn hji) 2
  · rw [hv j (lt_of_not_ge hji)]; simp

lemma positive_norm_upper_spectral_slice {A : E →ₗ[ℝ] E} (hA : A.IsPositive)
    {n : ℕ} (hn : Module.finrank ℝ E=n) (i : Fin n) (v : E)
    (hv : ∀ j : Fin n, j < i → (hA.isSymmetric.eigenvectorBasis hn).repr v j=0) :
    ‖A v‖^2≤(hA.isSymmetric.eigenvalues hn i)^2*‖v‖^2 := by
  rw [eigenbasis_operator_norm_expansion hA.isSymmetric hn,
    eigenbasis_norm_expansion (hA.isSymmetric.eigenvectorBasis hn),Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j hj
  by_cases hij : i ≤ j
  · apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
    exact pow_le_pow_left₀ (hA.nonneg_eigenvalues hn j)
      (hA.isSymmetric.eigenvalues_antitone hn hij) 2
  · rw [hv j (lt_of_not_ge hij)]; simp

lemma positive_singularValues_eq_eigenvalues {A : E →ₗ[ℝ] E} (hA : A.IsPositive)
    {n : ℕ} (hn : Module.finrank ℝ E=n) (i : Fin n) :
    A.singularValues i=hA.isSymmetric.eigenvalues hn i := by
  have hG := A.isSymmetric_adjoint_comp_self
  have hApos := hA.nonneg_eigenvalues hn i
  have hspos := A.singularValues_nonneg i
  apply le_antisymm
  · obtain ⟨v,hv,hgv,hav⟩ := paired_basis_slice (hG.eigenvectorBasis hn)
      (hA.isSymmetric.eigenvectorBasis hn) i
    have h1 := quadratic_lower_spectral_slice hG hn i v hgv
    have h2 := positive_norm_upper_spectral_slice hA hn i v hav
    simp only [LinearMap.comp_apply,LinearMap.adjoint_inner_left,
      real_inner_self_eq_norm_sq] at h1
    rw [←A.sq_singularValues_fin hn] at h1
    have hp : 0<‖v‖^2 := sq_pos_of_ne_zero (norm_ne_zero_iff.mpr hv)
    have hsq := (mul_le_mul_iff_left₀ hp).mp (h1.trans h2)
    nlinarith
  · obtain ⟨v,hv,hav,hgv⟩ := paired_basis_slice (hA.isSymmetric.eigenvectorBasis hn)
      (hG.eigenvectorBasis hn) i
    have h1 := positive_norm_lower_spectral_slice hA hn i v hav
    have h2 := quadratic_upper_spectral_slice hG hn i v hgv
    simp only [LinearMap.comp_apply,LinearMap.adjoint_inner_left,
      real_inner_self_eq_norm_sq] at h2
    rw [←A.sq_singularValues_fin hn] at h2
    have hp : 0<‖v‖^2 := sq_pos_of_ne_zero (norm_ne_zero_iff.mpr hv)
    have hsq := (mul_le_mul_iff_left₀ hp).mp (h1.trans h2)
    nlinarith

end PositiveSingular
end WeakMTWTransport

end

end

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_LinearAlgebra_JoinSpectrum
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
section JoinSpectrum
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma uniform_join_exp_norm_comparison :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ x : M, ∀ p : TangentSpace 𝓘(ℝ,Model n) x,
      p ∈ minimizingVectors x → ∀ t ∈ Icc (1/4:ℝ) (3/4), ∀ v,
      ‖splitJoinHessianOperator x t p v‖ ≤ C * ‖mfderiv 𝓘(ℝ,TangentSpace 𝓘(ℝ,Model n) x)
        𝓘(ℝ,Model n) (riemannianExp x) p v‖ ∧
      ‖mfderiv 𝓘(ℝ,TangentSpace 𝓘(ℝ,Model n) x) 𝓘(ℝ,Model n) (riemannianExp x) p v‖ ≤
        c * ‖splitJoinHessianOperator x t p v‖ := by
  obtain ⟨l,u,hl,hu,H⟩ := uniform_join_endpoint_factorization (n := n) (M := M)
  refine ⟨1/l,4*u,div_pos (by norm_num) hl,mul_pos (by norm_num) hu,?_⟩
  intro x p hp t ht v
  obtain ⟨L,hL,hLn,hfac⟩ := H x p hp t ht
  have hs : 0 < 1-t := by linarith [ht.2]
  have hn := dual_factor_norm_comparison (splitJoinHessianOperator x t p) L
    (mfderiv 𝓘(ℝ,TangentSpace 𝓘(ℝ,Model n) x) 𝓘(ℝ,Model n) (riemannianExp x) p)
    hs hl hu hL.2 hLn (fun a k => by rw [hfac]; field_simp [hs.ne']; rfl) v
  change l * ‖mfderiv 𝓘(ℝ,TangentSpace 𝓘(ℝ,Model n) x) 𝓘(ℝ,Model n)
      (riemannianExp x) p v‖ ≤ (1-t)*‖splitJoinHessianOperator x t p v‖ ∧
    (1-t)*‖splitJoinHessianOperator x t p v‖ ≤ u*‖mfderiv 𝓘(ℝ,TangentSpace 𝓘(ℝ,Model n) x)
      𝓘(ℝ,Model n) (riemannianExp x) p v‖ at hn
  constructor
  · have hm := mul_le_mul_of_nonneg_right (show (1/4:ℝ) ≤ 1-t by linarith [ht.2])
      (norm_nonneg (splitJoinHessianOperator x t p v))
    have hh := hm.trans hn.2
    linarith only [hh]
  · rw [one_div,mul_comm,←div_eq_mul_inv,le_div_iff₀ hl]
    have hm := mul_le_mul_of_nonneg_right (show 1-t ≤ 1 by linarith [ht.1])
      (norm_nonneg (splitJoinHessianOperator x t p v))
    have hh := hn.1.trans hm
    nlinarith only [hh]

local instance localInst_rbb9510_2 (x : M) : FiniteDimensional ℝ (TangentSpace 𝓘(ℝ,Model n) x) :=
  inferInstanceAs (FiniteDimensional ℝ (Model n))
lemma uniform_join_exp_ordered_comparison_oai :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ x : M, ∀ p : TangentSpace 𝓘(ℝ,Model n) x,
      ∀ hp : p ∈ minimizingVectors x, ∀ t : ℝ, ∀ ht : t ∈ Icc (1/4:ℝ) (3/4),
      ∀ i : Fin (Module.finrank ℝ (TangentSpace 𝓘(ℝ,Model n) x)),
      (splitJoinHessianOperator_positive hp (by linarith [ht.1])
        (by linarith [ht.2])).isSymmetric.eigenvalues rfl i ≤ C *
        (endpointExpDifferential x p).toLinearMap.singularValues i ∧
      (endpointExpDifferential x p).toLinearMap.singularValues i ≤ c *
        (splitJoinHessianOperator_positive hp (by linarith [ht.1])
          (by linarith [ht.2])).isSymmetric.eigenvalues rfl i := by
  obtain ⟨c,C,hc,hC,H⟩ := uniform_join_exp_norm_comparison (n := n) (M := M)
  refine ⟨c,C,hc,hC,?_⟩
  intro x p hp t ht i
  let Q := splitJoinHessianOperator x t p
  let E := endpointExpDifferential x p
  have hQ := splitJoinHessianOperator_positive hp
    (show 0 < t by linarith [ht.1]) (show t < 1 by linarith [ht.2])
  have h1 := ordered_singularValues_pullback (A := Q.toLinearMap) (B := E.toLinearMap)
    (LinearMap.id) hC.le (by norm_num : (0:ℝ) ≤ 1)
    (fun v => by change ‖v‖ ≤ 1 * ‖v‖; simp) (fun v => (H x p hp t ht v).1) rfl rfl i
  have h2 := ordered_singularValues_pullback (A := E.toLinearMap) (B := Q.toLinearMap)
    (LinearMap.id) hc.le (by norm_num : (0:ℝ) ≤ 1)
    (fun v => by change ‖v‖ ≤ 1 * ‖v‖; simp) (fun v => (H x p hp t ht v).2) rfl rfl i
  rw [positive_singularValues_eq_eigenvalues hQ rfl i] at h1 h2
  simpa only [mul_one] using And.intro h1 h2

end JoinSpectrum
end WeakMTWTransport

end

end

end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.WeakMTWTransport.uniform_join_exp_ordered_comparison_oai.{u_1} := @OAI.WeakMTWTransport.uniform_join_exp_ordered_comparison_oai.{u_1}
