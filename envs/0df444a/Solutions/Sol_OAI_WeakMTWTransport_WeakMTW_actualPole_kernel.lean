-- Prove2me | solution 1 for OAI.WeakMTWTransport.WeakMTW.actualPole_kernel
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T19:41:16.203998+00:00
-- url     : https://prove2.me/submissions/579399d3-d166-4874-989e-9bc263cc3b24

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
import Definitions.Def_OAIQ232A031
import Theorems.Thm_OAI_WeakMTWTransport_WeakMTW_actualPole_taylor

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Calculus_JetPullback
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace WeakMTWTransport

open Set Filter
open scoped Topology ContDiff

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma half_norm_sq_hasFDerivAt (p : E) :
    HasFDerivAt (fun v : E => ‖v‖^2/2) (innerSL ℝ p) p := by
  have H := ((hasFDerivAt_id (𝕜 := ℝ) p).norm_sq).const_smul (1/2:ℝ)
  convert! H using 1
  · ext v; simp only [Pi.smul_apply,smul_eq_mul,id_eq] <;> ring
  · ext a
    simp only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.id_apply,
      smul_apply,smul_eq_mul,innerSL_apply_apply,id_eq]
    ring

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Calculus_PoleJetAlgebra
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter
open scoped Topology ContDiff

namespace WeakMTWTransport
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma pole_kernel_of_active_support {B : E×E → ℝ} {D f : E → ℝ}
    {a : E → E} {p pj : E} {t : ℝ} {R : E →L[ℝ] E}
    (ha : HasFDerivAt a R p) (ha0 : a p=0)
    (hf : HasFDerivAt f (t • innerSL ℝ p) p)
    (hB : DifferentiableAt ℝ B (0,p))
    (hBa : ∀ u v:E, fderiv ℝ B (0,p) (u,v) = -inner ℝ p u+t*inner ℝ p v)
    (hD : HasFDerivAt D (-innerSL ℝ pj) 0)
    (hm : IsLocalMin (fun q => f q-B (a q,q)+D (a q)) p)
    (hsym : ∀ u v:E, inner ℝ (R u) v=inner ℝ u (R v)) : R (pj-p)=0 := by
  have hB' : HasFDerivAt B (fderiv ℝ B (0,p)) (a p,p) := by
    rw [ha0]; exact hB.hasFDerivAt
  have hD' : HasFDerivAt D (-innerSL ℝ pj) (a p) := by rwa [ha0]
  have hder := (hf.sub (hB'.comp (f := fun q => (a q,q)) p
    (ha.prodMk (hasFDerivAt_id (𝕜 := ℝ) p)))).add (hD'.comp p ha)
  have H := hm.hasFDerivAt_eq_zero hder
  apply (inner_self_eq_zero (𝕜 := ℝ)).mp
  have he := congrArg (fun l : E →L[ℝ] ℝ => l (R (pj-p))) H
  simp only [add_apply,sub_apply,smul_apply,neg_apply,zero_apply,
    smul_eq_mul,ContinuousLinearMap.comp_apply,ContinuousLinearMap.prod_apply,
    ContinuousLinearMap.id_apply,innerSL_apply_apply] at he
  rw [hBa] at he
  have horth : inner ℝ (pj-p) (R (R (pj-p)))=0 := by
    rw [inner_sub_left]
    linarith
  rw [←hsym] at horth
  exact horth

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Contact_EnvelopePole
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter
open scoped Topology ContDiff

namespace WeakMTWTransport
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma upper_contact_fderiv {f g : E → ℝ} {x : E}
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x)
    (hle : f ≤ᶠ[𝓝 x] g) (heq : f x=g x) : fderiv ℝ f x=fderiv ℝ g x := by
  have hmin : IsLocalMin (g-f) x := by
    filter_upwards [hle] with y hy
    change g x-f x≤g y-f y
    rw [heq,sub_self]
    exact sub_nonneg.mpr hy
  have H := hmin.hasFDerivAt_eq_zero (hg.hasFDerivAt.sub hf.hasFDerivAt)
  exact (sub_eq_zero.mp H).symm

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Regularity_PrefixAction
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.WeakMTWTransport.fixedJoinMiddle_apply _root_.OAI.WeakMTWTransport.normalEndpointMixedOperator_inner
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Manifold Bundle
open scoped Topology ContDiff

namespace WeakMTWTransport
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma prefixAction_contDiffAt {x : M} {p : TangentSpace 𝓘(ℝ,Model n) x}
    {t : ℝ} (hp : t • p ∈ injectivityDomain x) :
    ContDiffAt ℝ ∞ (prefixAction x t) (0,p) := by
  let V := TangentSpace 𝓘(ℝ,Model n) x
  have he := contMDiff_riemannianExp_fiber (n := n) x
  have hu : ContMDiffAt 𝓘(ℝ,V×V) 𝓘(ℝ,Model n) ∞
      (fun q : V×V => riemannianExp x q.1) (0,p) :=
    (he _).comp (0,p) contDiffAt_fst.contMDiffAt
  have hv : ContMDiffAt 𝓘(ℝ,V×V) 𝓘(ℝ,Model n) ∞
      (fun q : V×V => riemannianExp x (t • q.2)) (0,p) :=
    (he _).comp (0,p) (show ContDiffAt ℝ ∞ (fun q : V×V => t • q.2) (0,p) from by fun_prop).contMDiffAt
  have hc := cost_contMDiffAt_of_injectivityDomain
    (⟨x,t • p⟩ : TangentBundle 𝓘(ℝ,Model n) M) hp
  have hc' : ContMDiffAt (𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n)) 𝓘(ℝ,ℝ) ∞
      (fun q : M×M => cost q.1 q.2) (riemannianExp x (0:V),riemannianExp x (t • p)) := by
    simpa only [riemannianExp_zero] using hc
  exact ((hc'.comp (0,p) (hu.prodMk hv)).contDiffAt.div_const t)

lemma prefixAction_axis {x : M} {p : TangentSpace 𝓘(ℝ,Model n) x}
    {t : ℝ} (hp : t • p ∈ injectivityDomain x) :
    prefixAction x t (0,p)=t*(‖p‖^2/2) := by
  have hm := injectivityDomain_subset_minimizingVectors x hp
  change dist x (riemannianExp x (t • p))=‖t • p‖ at hm
  simp only [prefixAction,riemannianExp_zero,cost,hm,norm_smul,Real.norm_eq_abs,
    mul_pow,sq_abs]
  by_cases ht : t=0
  · simp [ht]
  · field_simp

lemma prefixAction_axis_near {x : M} {p : TangentSpace 𝓘(ℝ,Model n) x}
    {t : ℝ} (hp : t • p ∈ injectivityDomain x) :
    (fun v => prefixAction x t (0,v)) =ᶠ[𝓝 p] (fun v => t*(‖v‖^2/2)) := by
  have hn : ∀ᶠ v : TangentSpace 𝓘(ℝ,Model n) x in 𝓝 p, t • v ∈ injectivityDomain x :=
    (continuous_const_smul t).continuousAt.eventually ((isOpen_injectivityDomain x).mem_nhds hp)
  filter_upwards [hn] with v hv
  exact prefixAction_axis hv

lemma prefixAction_source_gradient {x : M} {p : TangentSpace 𝓘(ℝ,Model n) x}
    {t : ℝ} (ht : t≠0) (hp : t • p ∈ injectivityDomain x)
    (a : TangentSpace 𝓘(ℝ,Model n) x) :
    fderiv ℝ (prefixAction x t) (0,p) (a,0) = -inner ℝ p a := by
  have hnc := ((normalCost_contDiffAt hp).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).hasFDerivAt
  have H := hnc.mul_const t⁻¹
  have hp₀ := (hasFDerivAt_id (𝕜 := ℝ) (0 : TangentSpace 𝓘(ℝ,Model n) x)).prodMk
    (hasFDerivAt_const p (0 : TangentSpace 𝓘(ℝ,Model n) x))
  have H' : HasFDerivAt (fun u => prefixAction x t (u,p))
      (t⁻¹ • fderiv ℝ (normalCost x (t • p)) 0) 0 := by
    simpa only [prefixAction,normalCost,div_eq_mul_inv] using H
  have hB := (prefixAction_contDiffAt hp).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  have heq := (hB.hasFDerivAt.comp (f := fun u => (u,p)) 0 hp₀).unique H'
  have hh := congrArg (fun A : TangentSpace 𝓘(ℝ,Model n) x →L[ℝ] ℝ => A a) heq
  change fderiv ℝ (prefixAction x t) (0,p) (a,0) =
    t⁻¹ * fderiv ℝ (normalCost x (t • p)) 0 a at hh
  rw [normalCost_fderiv_zero hp,real_inner_smul_left] at hh
  rw [hh]
  field_simp

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_LinearAlgebra_PrefixActionJets
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.WeakMTWTransport.fixedJoinMiddle_apply _root_.OAI.WeakMTWTransport.normalEndpointMixedOperator_inner
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Manifold Bundle
open scoped Topology ContDiff

namespace WeakMTWTransport
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma prefixAction_endpoint_gradient {x : M} {p : TangentSpace 𝓘(ℝ,Model n) x}
    {t : ℝ} (hp : t • p ∈ injectivityDomain x)
    (d : TangentSpace 𝓘(ℝ,Model n) x) :
    fderiv ℝ (prefixAction x t) (0,p) (0,d) = t*inner ℝ p d := by
  let V := TangentSpace 𝓘(ℝ,Model n) x
  have hD := (prefixAction_contDiffAt hp).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  have hL := (hasFDerivAt_const (0:V) p).prodMk (hasFDerivAt_id (𝕜 := ℝ) p)
  have H := (hD.hasFDerivAt.comp (f := fun v : V => ((0:V),v)) p hL).congr_of_eventuallyEq
    (prefixAction_axis_near hp).symm
  have he := congrArg (fun A : V →L[ℝ] ℝ => A d)
    (H.unique ((half_norm_sq_hasFDerivAt p).const_smul t))
  simp only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.prod_apply,
    zero_apply,smul_apply,smul_eq_mul,innerSL_apply_apply] at he
  exact he

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_CostGeometry_ActualPole
attribute [-simp] _root_.OAI.WeakMTWTransport.fixedJoinMiddle_apply _root_.OAI.WeakMTWTransport.normalEndpointMixedOperator_inner
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Manifold Bundle
open scoped Topology ContDiff

namespace WeakMTWTransport
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma WeakMTW.hopfPole_minimizer (hmtw : WeakMTW (n := n) (M := M))
    {u v : M → ℝ} (hu : Continuous u) (hv : Continuous v) (hdual : IsCostDualPair u v)
    {t : ℝ} (ht : 0<t) (ht1 : t<1) (z:M) :
    hopfLax t u z=u (hopfPole (n := n) t u z)+cost (hopfPole (n := n) t u z) z/t := by
  rw [hdual.1] at hu ⊢
  obtain ⟨q,hq⟩ := surjective_graphProjection (n := n) hu ht z
  have H := congrArg Bundle.TotalSpace.proj (hmtw.hopfLax_backward_flow hv ht ht1 q)
  have He : hopfPole (n := n) t (cTransform v) z=q.1.1 := by
    change hopfPole (n := n) t (cTransform v) (graphProjection (cTransform v) t q)=q.1.1 at H
    rwa [hq] at H
  rw [He,←hq]
  exact hmtw.hopfLax_graph_value hv ht ht1 q

lemma WeakMTW.prefix_hopfLax_differentiable (hmtw : WeakMTW (n := n) (M := M))
    {u v : M → ℝ} (hu : Continuous u) (hv : Continuous v) (hdual : IsCostDualPair u v)
    {t : ℝ} (ht : 0<t) (ht1 : t<1) (x:M) :
    Differentiable ℝ (fun q : TangentSpace 𝓘(ℝ,Model n) x =>
      hopfLax t u (riemannianExp x (t • q))) := by
  intro q
  have he := (contMDiff_riemannianExp_fiber (n := n) x (t • q)).mdifferentiableAt (by simp)
  have hl : MDifferentiableAt 𝓘(ℝ,TangentSpace 𝓘(ℝ,Model n) x)
      𝓘(ℝ,TangentSpace 𝓘(ℝ,Model n) x) (fun q => t • q) q :=
    (show ContDiffAt ℝ ∞ (fun q : TangentSpace 𝓘(ℝ,Model n) x => t • q) q from by
      fun_prop).contMDiffAt.mdifferentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  exact ((hmtw.mdifferentiable_hopfLax hu hv hdual ht ht1 _).comp q
    (he.comp q hl)).differentiableAt

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Contact_ActualPoleJet
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Manifold Bundle
open scoped Topology ContDiff

namespace WeakMTWTransport
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma WeakMTW.actualPole_fixed_support (hmtw : WeakMTW (n := n) (M := M))
    {u v : M → ℝ} (hu : Continuous u) (hv : Continuous v) (hdual : IsCostDualPair u v)
    {t : ℝ} (ht : 0<t) (ht1 : t<1) {x:M}
    {p : TangentSpace 𝓘(ℝ,Model n) x} (hp : t • p∈injectivityDomain x)
    (hpole : hopfPole (n := n) t u (riemannianExp x (t • p))=x) :
    hopfLax t u (riemannianExp x (t • p))=u x+t*(‖p‖^2/2) ∧
    ∀ᶠ q in 𝓝 p, hopfLax t u (riemannianExp x (t • q))≤
      hopfLax t u (riemannianExp x (t • p))+t*(‖q‖^2/2-‖p‖^2/2) := by
  have He := hmtw.hopfPole_minimizer hu hv hdual ht ht1 (riemannianExp x (t • p))
  rw [hpole] at He
  have hb : cost x (riemannianExp x (t • p))/t=t*(‖p‖^2/2) := by
    simpa only [prefixAction,riemannianExp_zero] using prefixAction_axis hp
  rw [hb] at He
  refine ⟨He,?_⟩
  filter_upwards [prefixAction_axis_near hp] with q hq
  have H := hopfLax_le hu t (riemannianExp x (t • q)) x
  have hbq : cost x (riemannianExp x (t • q))/t=t*(‖q‖^2/2) := by
    simpa only [prefixAction,riemannianExp_zero] using hq
  rw [hbq] at H
  rw [He]
  linarith

lemma WeakMTW.actualPole_first_derivative (hmtw : WeakMTW (n := n) (M := M))
    {u v : M → ℝ} (hu : Continuous u) (hv : Continuous v) (hdual : IsCostDualPair u v)
    {t : ℝ} (ht : 0<t) (ht1 : t<1) {x:M}
    {p : TangentSpace 𝓘(ℝ,Model n) x} (hp : t • p∈injectivityDomain x)
    (hpole : hopfPole (n := n) t u (riemannianExp x (t • p))=x) :
    HasFDerivAt (fun q : TangentSpace 𝓘(ℝ,Model n) x =>
      hopfLax t u (riemannianExp x (t • q))) (t • innerSL ℝ p) p := by
  let V := TangentSpace 𝓘(ℝ,Model n) x
  let f : V → ℝ := fun q => hopfLax t u (riemannianExp x (t • q))
  have hd := hmtw.prefix_hopfLax_differentiable hu hv hdual ht ht1 x p
  have hsup := (hmtw.actualPole_fixed_support hu hv hdual ht ht1 hp hpole).2
  have hg : HasFDerivAt (fun q : V => f p+t*(‖q‖^2/2-‖p‖^2/2))
      (t • innerSL ℝ p) p := by
    convert! (((half_norm_sq_hasFDerivAt p).sub_const (‖p‖^2/2)).const_smul t).const_add (f p) using 1
    all_goals try with_reducible_and_instances rfl
  have he := upper_contact_fderiv hd hg.differentiableAt hsup (by simp only [sub_self,mul_zero,add_zero]; rfl)
  exact hd.hasFDerivAt.congr_fderiv (he.trans hg.fderiv)

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Regularity_SplitEndpointCost
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.WeakMTWTransport.fixedJoinMiddle_apply _root_.OAI.WeakMTWTransport.normalEndpointMixedOperator_inner
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Manifold Bundle
open scoped Topology ContDiff

namespace WeakMTWTransport
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma splitEndpointCost_contDiffAt {x : M} {p : TangentSpace 𝓘(ℝ,Model n) x}
    {s : ℝ} (hleft : s • p ∈ injectivityDomain x)
    (hright : (1-s) • (sprayFlow s (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M)).2 ∈
      injectivityDomain (sprayFlow s (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M)).1) :
    ContDiffAt ℝ ∞ (splitEndpointCost x s) (0,p) := by
  exact (splitNormalAction_contDiffAt hleft hright).comp
    (f := fun q : TangentSpace 𝓘(ℝ,Model n) x × TangentSpace 𝓘(ℝ,Model n) x =>
      (q.2,(q.1,q.2))) (0,p)
    (contDiffAt_snd.prodMk (contDiffAt_fst.prodMk contDiffAt_snd))

lemma splitEndpointCost_axis {x : M} {p : TangentSpace 𝓘(ℝ,Model n) x}
    {s : ℝ} (hs : 0 < s) (hs1 : s < 1)
    (hleft : s • p ∈ injectivityDomain x)
    (hright : (1-s) • (sprayFlow s (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M)).2 ∈
      injectivityDomain (sprayFlow s (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M)).1) :
    splitEndpointCost x s (0,p)=‖p‖^2/2 := by
  have hm := injectivityDomain_subset_minimizingVectors x hleft
  have hn := injectivityDomain_subset_minimizingVectors _ hright
  change dist x (riemannianExp x (s • p))=‖s • p‖ at hm
  change dist (sprayFlow s (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M)).1
    (riemannianExp _ ((1-s) • (sprayFlow s (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M)).2)) = _ at hn
  rw [shifted_exp_endpoint] at hn
  simp only [norm_smul,Real.norm_eq_abs,abs_of_pos hs] at hm
  rw [norm_smul,Real.norm_eq_abs,abs_of_pos (sub_pos.mpr hs1),sprayFlow_speed] at hn
  simp only [splitEndpointCost,splitNormalAction,riemannianExp_zero,cost]
  rw [hm,riemannianExp_smul,hn]
  field_simp
  ring

lemma splitEndpointCost_source_gradient {x : M} {p : TangentSpace 𝓘(ℝ,Model n) x}
    {s : ℝ} (hs : s ≠ 0) (hleft : s • p ∈ injectivityDomain x)
    (hright : (1-s) • (sprayFlow s (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M)).2 ∈
      injectivityDomain (sprayFlow s (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M)).1)
    (a : TangentSpace 𝓘(ℝ,Model n) x) :
    fderiv ℝ (splitEndpointCost x s) (0,p) (a,0) = -inner ℝ p a := by
  let V := TangentSpace 𝓘(ℝ,Model n) x
  have hC := (splitEndpointCost_contDiffAt hleft hright).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  have hB := (splitNormalAction_contDiffAt hleft hright).comp (0,p)
    (contDiffAt_const.prodMk contDiffAt_id)
  have hL : HasFDerivAt (fun b : V => (b,p))
      ((ContinuousLinearMap.id ℝ V).prod 0) 0 :=
    (hasFDerivAt_id (𝕜 := ℝ) (0:V)).prodMk (hasFDerivAt_const p (0:V))
  have hc := hC.hasFDerivAt.comp (f := fun b : V => (b,p)) 0 hL
  have hb := (hB.differentiableAt (by simp)).hasFDerivAt.comp (f := fun b : V => (b,p)) 0 hL
  have he := congrArg (fun A : V →L[ℝ] ℝ => A a) (hc.unique hb)
  change fderiv ℝ (splitEndpointCost x s) (0,p) (a,0) =
    fderiv ℝ (splitNormalAction x s p) (0,p) (a,0) at he
  rw [he]
  exact splitNormalAction_source_gradient hs hleft (hB.differentiableAt (by simp)) a

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_CostGeometry_ActualPoleKernel
attribute [-simp] _root_.OAI.WeakMTWTransport.fixedJoinMiddle_apply _root_.OAI.WeakMTWTransport.normalEndpointMixedOperator_inner
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Manifold Bundle
open scoped Topology ContDiff

namespace WeakMTWTransport
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma WeakMTW.actualPole_kernel_oai (hmtw : WeakMTW (n := n) (M := M))
    {u v : M → ℝ} (hu : Continuous u) (hv : Continuous v) (hdual : IsCostDualPair u v)
    {t s : ℝ} (ht : 0<t) (ht1 : t<1) (hs : 0 < s) (hs1 : s<1) {x:M}
    {p pj : TangentSpace 𝓘(ℝ,Model n) x} (hp : t • p∈injectivityDomain x)
    (hmin : pj∈minimizingVectors x)
    (hactive : contactGap u v x (riemannianExp x pj)=0)
    (hleft : s • pj∈injectivityDomain x)
    (hright : (1-s) • (sprayFlow s (⟨x,pj⟩ : TangentBundle 𝓘(ℝ,Model n) M)).2 ∈
      injectivityDomain (sprayFlow s (⟨x,pj⟩ : TangentBundle 𝓘(ℝ,Model n) M)).1)
    {a : TangentSpace 𝓘(ℝ,Model n) x → TangentSpace 𝓘(ℝ,Model n) x}
    {R : TangentSpace 𝓘(ℝ,Model n) x →L[ℝ] TangentSpace 𝓘(ℝ,Model n) x}
    (ha : HasFDerivAt a R p) (ha0 : a p=0)
    (harep : ∀ᶠ q in 𝓝 p, riemannianExp x (a q)=
      hopfPole (n := n) t u (riemannianExp x (t • q))) : R (pj-p)=0 := by
  let V := TangentSpace 𝓘(ℝ,Model n) x
  let f : V → ℝ := fun q => hopfLax t u (riemannianExp x (t • q))
  let B : V×V → ℝ := prefixAction x t
  let D : V → ℝ := fun b => splitEndpointCost x s (b,pj)
  have hpole : hopfPole (n := n) t u (riemannianExp x (t • p))=x := by
    have H := harep.self_of_nhds
    rw [ha0,riemannianExp_zero] at H
    exact H.symm
  have hB : DifferentiableAt ℝ B (0,p) :=
    (prefixAction_contDiffAt hp).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  have hBa : ∀ b d:V, fderiv ℝ B (0,p) (b,d) = -inner ℝ p b+t*inner ℝ p d := by
    intro b d
    rw [show (b,d)=((b,0):V×V)+(0,d) by simp,map_add]
    rw [prefixAction_source_gradient ht.ne' hp,prefixAction_endpoint_gradient hp]
  have hD : HasFDerivAt D (-innerSL ℝ pj) 0 := by
    have HD := ((splitEndpointCost_contDiffAt hleft hright).differentiableAt
      (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).hasFDerivAt.comp (f := fun b : V => (b,pj)) 0
        ((hasFDerivAt_id (𝕜 := ℝ) (0:V)).prodMk (hasFDerivAt_const pj (0:V)))
    apply HD.congr_fderiv
    ext b
    change fderiv ℝ (splitEndpointCost x s) (0,pj) (b,0) = -inner ℝ pj b
    exact splitEndpointCost_source_gradient hs.ne' hleft hright b
  have henv : ∀ᶠ q in 𝓝 p, f q-B (a q,q)=u (riemannianExp x (a q)) := by
    filter_upwards [harep] with q hq
    have H := hmtw.hopfPole_minimizer hu hv hdual ht ht1 (riemannianExp x (t • q))
    rw [←hq] at H
    dsimp [f,B,prefixAction]
    linarith
  have hm : IsLocalMin (fun q => f q-B (a q,q)+D (a q)) p := by
    have hpEq := henv.self_of_nhds
    have hc : D 0=cost x (riemannianExp x pj) := by
      change splitEndpointCost x s (0,pj)=cost x (riemannianExp x pj)
      rw [splitEndpointCost_axis hs hs1 hleft hright]
      have H := hmin
      change dist x (riemannianExp x pj)=‖pj‖ at H
      rw [cost,H]
    filter_upwards [henv] with q hq
    rw [hpEq,ha0,riemannianExp_zero,hc,hq]
    have HG := dualPair_gap_nonneg hv hdual (riemannianExp x (a q)) (riemannianExp x pj)
    have HC : cost (riemannianExp x (a q)) (riemannianExp x pj)≤D (a q) :=
      normalCost_le_splitNormalAction x pj (a q) pj hs hs1
    dsimp only [contactGap] at HG hactive
    linarith
  exact pole_kernel_of_active_support ha ha0
    (hmtw.actualPole_first_derivative hu hv hdual ht ht1 hp hpole) hB hBa hD hm
    (hmtw.actualPole_taylor hu hv hdual ht ht1 hp ha ha0 harep).2.2

end WeakMTWTransport

end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.WeakMTWTransport.WeakMTW.actualPole_kernel_oai.{u_1} := @OAI.WeakMTWTransport.WeakMTW.actualPole_kernel_oai.{u_1}
