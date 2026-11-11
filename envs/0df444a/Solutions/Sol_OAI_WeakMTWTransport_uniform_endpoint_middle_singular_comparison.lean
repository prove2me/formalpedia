-- Prove2me | solution 1 for OAI.WeakMTWTransport.uniform_endpoint_middle_singular_comparison
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T19:37:16.100717+00:00
-- url     : https://prove2.me/submissions/2676b368-3cc3-4b5c-a972-ec63ce4720cd

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
import Definitions.Def_OAIQ232A020
import Definitions.Def_OAIQ232A029
import Theorems.Thm_OAI_WeakMTWTransport_uniform_join_exp_ordered_comparison

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

lemma prefix_zero_log_fderiv_norm {x y : M} {t : ℝ}
    {p : TangentSpace 𝓘(ℝ,Model n) x}
    {q : TangentSpace 𝓘(ℝ,Model n) x → TangentSpace 𝓘(ℝ,Model n) y}
    (hq : DifferentiableAt ℝ q p) (hqp : q p=0)
    (hqr : ∀ᶠ a in 𝓝 p, riemannianExp y (q a)=riemannianExp x (t • a))
    (v : TangentSpace 𝓘(ℝ,Model n) x) :
    ‖fderiv ℝ q p v‖=
    ‖mfderiv 𝓘(ℝ,TangentSpace 𝓘(ℝ,Model n) x) 𝓘(ℝ,Model n)
      (riemannianExp x) (t • p) (t • v)‖ := by
  have H := prefix_log_fderiv_exp_norm hq hqr v
  rw [hqp,mfderiv_exp_zero_norm] at H
  exact H

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

lemma uniform_prefix_log_derivative_bounds :
    ∃ c C : ℝ, 0 < c ∧ 0<C ∧ ∀ x : M, ∀ p : TangentSpace 𝓘(ℝ,Model n) x,
      p∈minimizingVectors x → ∀ t∈Icc (1/4:ℝ) (3/4), ∀ y : M,
      ∀ q : TangentSpace 𝓘(ℝ,Model n) x → TangentSpace 𝓘(ℝ,Model n) y,
      DifferentiableAt ℝ q p → q p=0 →
      (∀ᶠ a in 𝓝 p, riemannianExp y (q a)=riemannianExp x (t • a)) →
      ∀ v, c*‖v‖≤‖fderiv ℝ q p v‖ ∧ ‖fderiv ℝ q p v‖≤C*‖v‖ := by
  obtain ⟨l,u,hl,hu,H⟩ := uniform_split_exp_bounds (n := n) (M := M)
  refine ⟨l/4,u,div_pos hl (by norm_num),hu,?_⟩
  intro x p hp t ht y q hq hqp hqr v
  have htpos : 0<t := by linarith [ht.1]
  have htone : t≤1 := by linarith [ht.2]
  have hb := (H (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M) hp t ht).1 (t • v)
  rw [←prefix_zero_log_fderiv_norm hq hqp hqr v] at hb
  change l*‖t • v‖≤‖fderiv ℝ q p v‖ ∧ ‖fderiv ℝ q p v‖≤u*‖t • v‖ at hb
  rw [norm_smul_of_nonneg htpos.le] at hb
  constructor
  · have hmul := mul_le_mul_of_nonneg_right ht.1 (norm_nonneg v)
    have hh := mul_le_mul_of_nonneg_left hmul hl.le
    nlinarith [hb.1]
  · have hmul := mul_le_mul_of_nonneg_right htone (norm_nonneg v)
    have hh := mul_le_mul_of_nonneg_left hmul hu.le
    nlinarith [hb.2]

end UniformLog
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
section UniformCongruence
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

local instance instFiniteDimensionalRealTangentSpaceModelModelWithCornersSelf_6 (x : M) : FiniteDimensional ℝ (TangentSpace 𝓘(ℝ,Model n) x) :=
  inferInstanceAs (FiniteDimensional ℝ (Model n))

lemma uniform_split_join_hessian_congruence :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ x : M, ∀ p : TangentSpace 𝓘(ℝ,Model n) x,
      p ∈ minimizingVectors x → ∀ h ∈ Icc (1/4:ℝ) (3/4),
    ∃ P : TangentSpace 𝓘(ℝ,Model n) x →L[ℝ]
        TangentSpace 𝓘(ℝ,Model n) (sprayFlow h (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M)).1,
      Function.Bijective P ∧ (∀ v, c*‖v‖ ≤ ‖P v‖ ∧ ‖P v‖ ≤ C*‖v‖) ∧ ∀ a,
      fderiv ℝ (fderiv ℝ (diagonalSplitAction x h)) (p,p) (0,a) (0,a)=
        middleHessian (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M) h 1 (P a) (P a) := by
  obtain ⟨c,C,hc,hC,H⟩ := uniform_prefix_log_derivative_bounds (n := n) (M := M)
  refine ⟨c,C,hc,hC,?_⟩
  intro x p hp h ht
  have hh : 0 < h := by linarith [ht.1]
  have hh1 : h < 1 := by linarith [ht.2]
  let z : TangentBundle 𝓘(ℝ,Model n) M := ⟨x,p⟩
  have hleft := contracted_minimizer_mem_injectivityDomain hp hh hh1
  obtain ⟨q,hqp,hq,hqinj,hqr⟩ := exists_join_normal_coordinates hh.ne' hleft
  have hf := middleCenteredAction_contDiffAt (z := z) hp hh hh1
  have hf' : ContDiffAt ℝ 2 (middleCenteredAction z h) (q p) := by rwa [hqp]
  have hz : fderiv ℝ (middleCenteredAction z h) (q p)=0 := by
    rw [hqp]
    exact (middleCenteredAction_minimum (z := z) hp hh hh1).fderiv_eq_zero
  have hF : ContDiffAt ℝ 2 (diagonalSplitAction x h) (p,p) :=
    (diagonalSplitAction_contDiffAt hleft (proper_suffix_in_injectivityDomain
      (z := z) hp hh hh1 le_rfl)).of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  have he := middle_action_in_join_coordinates hp hh hh1 hqr
  have heD := he.fderiv (𝕜 := ℝ)
  have heDD := heD.fderiv_eq (𝕜 := ℝ)
  change fderiv ℝ (fderiv ℝ (middleCenteredAction z h ∘ q)) p =
    fderiv ℝ (fderiv ℝ (fun a => diagonalSplitAction x h (p,a)-cost x (riemannianExp x p))) p at heDD
  have hsub : fderiv ℝ (fun a => diagonalSplitAction x h (p,a)-cost x (riemannianExp x p))=
      fderiv ℝ (fun a => diagonalSplitAction x h (p,a)) := by
    funext a; exact fderiv_sub_const _
  rw [hsub] at heDD
  have hqs : Function.Surjective (fderiv ℝ q p) :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (f := (fderiv ℝ q p).toLinearMap) rfl).mp hqinj
  refine ⟨fderiv ℝ q p,⟨hqinj,hqs⟩,
    H x p hp h ht _ q (hq.differentiableAt (by simp)) hqp hqr,?_⟩
  intro a
  have H := second_fderiv_comp_at_critical hf' (hq.of_le
    (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)) hz a a
  rw [heDD,hqp,second_derivative_target_slice hF] at H
  exact H.trans (middleCenteredAction_hessian (z := z) hp hh hh1 _)

end UniformCongruence
end WeakMTWTransport

end

end

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_LinearAlgebra_CongruenceSpectrum
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
namespace WeakMTWTransport
section CongruenceSpectrum
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F]

lemma ordered_eigenvalues_bounded_congruence {A : E →ₗ[ℝ] E} {B : F →ₗ[ℝ] F}
    (hA : A.IsPositive) (hB : B.IsPositive) (P : E →ₗ[ℝ] F)
    (hP : Function.Bijective P) {l u : ℝ} (hl : 0 < l) (hu : 0 ≤ u)
    (hPn : ∀ v, l*‖v‖ ≤ ‖P v‖ ∧ ‖P v‖ ≤ u*‖v‖)
    (h : ∀ v, inner ℝ (A v) v = inner ℝ (B (P v)) (P v))
    {n : ℕ} (hnE : Module.finrank ℝ E = n) (hnF : Module.finrank ℝ F = n) (i : Fin n) :
    hA.isSymmetric.eigenvalues hnE i ≤ u^2 * hB.isSymmetric.eigenvalues hnF i ∧
    hB.isSymmetric.eigenvalues hnF i ≤ (1/l)^2 * hA.isSymmetric.eigenvalues hnE i := by
  constructor
  · have H := ordered_eigenvalue_pullback_comparison hA.isSymmetric hB P
      (by norm_num : (0:ℝ) ≤ 1) hu (fun v => (hPn v).2)
      (a := 1) (b := 0) (fun v => by simp [h]) hnE hnF i
    simpa only [one_mul,add_zero] using H
  · let e := LinearEquiv.ofBijective P hP
    have hnorm : ∀ w, ‖e.symm w‖ ≤ (1/l)*‖w‖ := by
      intro w
      rw [one_div,mul_comm,←div_eq_mul_inv,le_div_iff₀ hl]
      have H := (hPn (e.symm w)).1
      change l*‖e.symm w‖ ≤ ‖e (e.symm w)‖ at H
      simpa only [e.apply_symm_apply,mul_comm] using H
    have heq : ∀ w, inner ℝ (B w) w = inner ℝ (A (e.symm w)) (e.symm w) := by
      intro w
      have H := h (e.symm w)
      change inner ℝ (A (e.symm w)) (e.symm w) = inner ℝ (B (e (e.symm w))) (e (e.symm w)) at H
      simpa only [e.apply_symm_apply] using H.symm
    have H := ordered_eigenvalue_pullback_comparison hB.isSymmetric hA e.symm.toLinearMap
      (by norm_num : (0:ℝ) ≤ 1) (div_nonneg (by norm_num) hl.le) hnorm
      (a := 1) (b := 0) (fun v => by simp [heq]) hnF hnE i
    simpa only [one_mul,add_zero] using H

end CongruenceSpectrum
end WeakMTWTransport

end

end

section

noncomputable section
open Set Filter Manifold Bundle ContinuousLinearMap
open scoped Topology ContDiff

namespace WeakMTWTransport
section EndpointMiddle
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

attribute [local instance] OAI.WeakMTWTransport.instFiniteDimensionalRealTangentSpaceModelModelWithCornersSelf_7
lemma uniform_join_middle_ordered_comparison :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ x : M, ∀ p : TangentSpace 𝓘(ℝ,Model n) x,
      ∀ hp : p ∈ minimizingVectors x, ∀ t : ℝ, ∀ ht : t ∈ Icc (1/4:ℝ) (3/4),
      ∀ i : Fin (Module.finrank ℝ (TangentSpace 𝓘(ℝ,Model n) x)),
      (splitJoinHessianOperator_positive hp (by linarith [ht.1])
        (by linarith [ht.2])).isSymmetric.eigenvalues rfl i ≤ C *
        (middleHessianOperator_positive_one (z := ⟨x,p⟩) hp (by linarith [ht.1])
          (by linarith [ht.2])).isSymmetric.eigenvalues rfl i ∧
      (middleHessianOperator_positive_one (z := ⟨x,p⟩) hp (by linarith [ht.1])
          (by linarith [ht.2])).isSymmetric.eigenvalues rfl i ≤ c *
        (splitJoinHessianOperator_positive hp (by linarith [ht.1])
          (by linarith [ht.2])).isSymmetric.eigenvalues rfl i := by
  obtain ⟨c,C,hc,hC,H⟩ := uniform_split_join_hessian_congruence (n := n) (M := M)
  refine ⟨(1 / c)^2, C ^ 2, sq_pos_of_pos (div_pos (by norm_num) hc),sq_pos_of_pos hC,?_⟩
  intro x p hp t ht i
  obtain ⟨P,hP,hPn,h⟩ := H x p hp t ht
  have hpQ := splitJoinHessianOperator_positive hp
    (show 0 < t by linarith [ht.1]) (show t < 1 by linarith [ht.2])
  have hpD := middleHessianOperator_positive_one (z := ⟨x,p⟩) hp
    (show 0 < t by linarith [ht.1]) (show t < 1 by linarith [ht.2])
  exact ordered_eigenvalues_bounded_congruence hpQ hpD P.toLinearMap hP hc hC.le hPn
    (fun v => by
      change inner ℝ (splitJoinHessianOperator x t p v) v =
        inner ℝ (middleHessianOperator (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M) t 1 (P v)) (P v)
      rw [inner_splitJoinHessianOperator,inner_middleHessianOperator,h]) rfl rfl i

lemma uniform_endpoint_middle_ordered_comparison :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ x : M, ∀ p : TangentSpace 𝓘(ℝ,Model n) x,
      ∀ hp : p ∈ minimizingVectors x, ∀ t : ℝ, ∀ ht : t ∈ Icc (1/4:ℝ) (3/4),
      ∀ i : Fin (Module.finrank ℝ (TangentSpace 𝓘(ℝ,Model n) x)),
      (endpointExpDifferential x p).toLinearMap.singularValues i ≤ C *
        (middleHessianOperator_positive_one (z := ⟨x,p⟩) hp (by linarith [ht.1])
          (by linarith [ht.2])).isSymmetric.eigenvalues rfl i ∧
      (middleHessianOperator_positive_one (z := ⟨x,p⟩) hp (by linarith [ht.1])
          (by linarith [ht.2])).isSymmetric.eigenvalues rfl i ≤ c *
        (endpointExpDifferential x p).toLinearMap.singularValues i := by
  obtain ⟨a,b,ha,hb,H⟩ := uniform_join_middle_ordered_comparison (n := n) (M := M)
  obtain ⟨d,e,hd,he,J⟩ := uniform_join_exp_ordered_comparison (n := n) (M := M)
  refine ⟨a*e,d*b,mul_pos ha he,mul_pos hd hb,?_⟩
  intro x p hp t ht i
  have H1 := H x p hp t ht i
  have J1 := J x p hp t ht i
  constructor
  · simpa only [mul_assoc] using J1.2.trans (mul_le_mul_of_nonneg_left H1.1 hd.le)
  · simpa only [mul_assoc] using H1.2.trans (mul_le_mul_of_nonneg_left J1.1 ha.le)

end EndpointMiddle
end WeakMTWTransport

end

end

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_CostGeometry_RadialSingular
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
section RadialSingular
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

attribute [local instance] OAI.WeakMTWTransport.instFiniteDimensionalRealTangentSpaceModelModelWithCornersSelf_8
lemma uniform_endpoint_middle_singular_comparison_oai :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ x : M, ∀ p : TangentSpace 𝓘(ℝ,Model n) x,
      p ∈ minimizingVectors x → ∀ t ∈ Icc (1/4:ℝ) (3/4),
      ∀ i : Fin (Module.finrank ℝ (Model n)),
      (endpointExpDifferential x p).toLinearMap.singularValues i ≤ C *
        middleSingularValue (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M) t 1 i ∧
      middleSingularValue (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M) t 1 i ≤ c *
        (endpointExpDifferential x p).toLinearMap.singularValues i := by
  obtain ⟨c,C,hc,hC,H⟩ := uniform_endpoint_middle_ordered_comparison (n := n) (M := M)
  refine ⟨c,C,hc,hC,?_⟩
  intro x p hp t ht i
  have hD := middleHessianOperator_positive_one (z := ⟨x,p⟩) hp
    (show 0 < t by linarith [ht.1]) (show t < 1 by linarith [ht.2])
  have hE := positive_singularValues_eq_eigenvalues hD rfl i
  change middleSingularValue (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M) t 1 i = _ at hE
  simpa only [hE] using H x p hp t ht i

end RadialSingular
end WeakMTWTransport

end

end

end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.WeakMTWTransport.uniform_endpoint_middle_singular_comparison_oai.{u_1} := @OAI.WeakMTWTransport.uniform_endpoint_middle_singular_comparison_oai.{u_1}
