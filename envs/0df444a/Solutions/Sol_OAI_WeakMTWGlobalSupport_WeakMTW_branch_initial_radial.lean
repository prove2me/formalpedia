-- Prove2me | solution 1 for OAI.WeakMTWGlobalSupport.WeakMTW.branch_initial_radial
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-23T12:59:20.50649+00:00
-- url     : https://prove2.me/submissions/f125dce0-6f11-486b-80cd-342a15d8edef

import Mathlib
import Definitions.Def_WeakMTWGlobalSupport
import Definitions.Def_OAIQWMTW003
import Theorems.Thm_OAI_WeakMTWGlobalSupport_WeakMTW_branch_initial_gradient

section
-- module Solutions.OAIQW_WeakMTW.Coordinates_TangentCoordinates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace WeakMTWGlobalSupport

section

open Set Filter Manifold Bundle
open scoped Topology ContDiff Manifold
namespace RiemannianLocal
noncomputable section
open ChartMetric CoordinateGeometry
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {M : Type*} [MetricSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

 theorem stateChart_target (x : M) (q : E × E) :
    q ∈ (stateChart x).target ↔ q.1 ∈ (chartAt E x).target :=
  TangentBundle.mem_chart_target_iff _ _

end
end RiemannianLocal
end

end WeakMTWGlobalSupport

end OAI
end

section
-- module Solutions.OAIQW_WeakMTW.Coordinates_ChartGlobalVariation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace WeakMTWGlobalSupport

section

open Set Filter Manifold Bundle
open scoped Topology ContDiff Manifold
namespace WeakMTW
noncomputable section
open RiemannianLocal ChartMetric CoordinateGeometry
variable {n : ℕ} {M : Type*} [MetricSpace M] [ChartedSpace (Model n) M]
  [IsManifold (model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace (model n) x)]
  [IsContMDiffRiemannianBundle (model n) ∞ (Model n) (fun x : M => TangentSpace (model n) x)]
  [IsRiemannianManifold (model n) M] [CompactSpace M]

 omit [IsRiemannianManifold (model n) M] [CompactSpace M] in
 theorem chartKinetic_smooth (x : M) :
    ContDiffOn ℝ ∞ (chartKinetic (n := n) x) (stateChart (E := Model n) x).target := by
  have hg : ContDiffOn ℝ ∞ (fun q : Model n × Model n => metric x q.1) (stateChart (E := Model n) x).target :=
    (metric_smooth x).comp contDiffOn_fst (fun q hq => (stateChart_target x q).mp hq)
  exact ((hg.clm_apply contDiffOn_snd).clm_apply contDiffOn_snd).div_const 2

end
end WeakMTW
end

end WeakMTWGlobalSupport

end OAI
end

section
-- module Solutions.OAIQW_WeakMTW.Variations_BranchAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace WeakMTWGlobalSupport

section

open Set Filter Manifold Bundle
open scoped Topology ContDiff Manifold
namespace WeakMTW
noncomputable section
open RiemannianLocal ChartMetric CoordinateGeometry
variable {n : ℕ} {M : Type*} [MetricSpace M] [ChartedSpace (Model n) M]
  [IsManifold (model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace (model n) x)]
  [IsContMDiffRiemannianBundle (model n) ∞ (Model n) (fun x : M => TangentSpace (model n) x)]
  [IsRiemannianManifold (model n) M] [CompactSpace M]

 theorem pair_inverse_fst (x y : M)
    (e : OpenPartialHomeomorph (Model n × Model n) (Model n × Model n))
    (he : (e : (Model n × Model n) → (Model n × Model n)) = pairExpCoordinates (n := n) x y)
    {q : Model n × Model n} (hq : q ∈ e.target) : (e.symm q).1 = q.1 := by
  have hh := congrArg Prod.fst (e.right_inv hq)
  simpa only [he,pairExpCoordinates] using hh

 theorem branchAction_smooth (x y : M)
    (e : OpenPartialHomeomorph (Model n × Model n) (Model n × Model n))
    (hes : e.source ⊆ pairExpDomain (n := n) x y)
    (hei : ContDiffOn ℝ ∞ e.symm e.target) : ContDiffOn ℝ ∞ (branchAction x e) e.target :=
  (chartKinetic_smooth x).comp hei (fun _ hq => (hes (e.map_target hq)).1)

 theorem branchAction_is_kinetic (x y : M)
    (e : OpenPartialHomeomorph (Model n × Model n) (Model n × Model n))
    (he : (e : (Model n × Model n) → (Model n × Model n)) = pairExpCoordinates (n := n) x y)
    {q : Model n × Model n} (hq : q ∈ e.target) :
    branchAction x e q = metric x q.1 (e.symm q).2 (e.symm q).2 / 2 := by
  unfold branchAction chartKinetic
  rw [pair_inverse_fst x y e he hq]

end
end WeakMTW
end

end WeakMTWGlobalSupport

end OAI
end

section
-- module Solutions.OAIQW_WeakMTW.Variations_QuadraticHessian
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace WeakMTWGlobalSupport

section

open Filter
open scoped Topology ContDiff
namespace QuadraticHessian
variable {P E : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

 theorem first (B : P → E →L[ℝ] E →L[ℝ] ℝ) (ν : P → E) {q : P}
    (hB : DifferentiableAt ℝ B q) (hν : DifferentiableAt ℝ ν q) (k : P) :
    fderiv ℝ (fun z => B z (ν z) (ν z)) q k =
      fderiv ℝ B q k (ν q) (ν q) + B q (fderiv ℝ ν q k) (ν q) +
        B q (ν q) (fderiv ℝ ν q k) := by
  rw [fderiv_clm_apply (hB.clm_apply hν) hν, fderiv_clm_apply hB hν]
  simp only [add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.flip_apply]
  abel

end QuadraticHessian
end

end WeakMTWGlobalSupport

end OAI
end

section
-- module Solutions.OAIQW_WeakMTW.Variations_RadialHessianCalculus
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace WeakMTWGlobalSupport

section

open Filter Set
open scoped Topology ContDiff
namespace RadialHessianCalculus
open CoordinateGeometry
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

 omit [FiniteDimensional ℝ E] in
 theorem coordinate_radial (G : E → MetricTensor E) (ν : E → E) (f : E → ℝ) {a : E}
    (hG : DifferentiableAt ℝ G a) (hν : DifferentiableAt ℝ ν a)
    (hf : ContDiffAt ℝ 2 f a)
    (hsym : ∀ v w, G a v w = G a w v)
    (henergy : f =ᶠ[𝓝 a] (fun r => G r (ν r) (ν r) / 2))
    (hgrad : ∀ᶠ r in 𝓝 a, ∀ w, fderiv ℝ f r w = -G r (ν r) w) (ξ : E) :
    fderiv ℝ (fderiv ℝ f) a ξ (ν a) =
      G a (ν a) ξ - fderiv ℝ G a ξ (ν a) (ν a) / 2 := by
  have hD := ((hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num))
  have he : fderiv ℝ f a = fderiv ℝ (fun r => G r (ν r) (ν r) / 2) a := henergy.fderiv_eq
  have hQ := ((hG.clm_apply hν).clm_apply hν)
  have hQD : HasFDerivAt (fun r => G r (ν r) (ν r) / 2)
      ((1/2 : ℝ) • fderiv ℝ (fun r => G r (ν r) (ν r)) a) a := by
    convert! hQ.hasFDerivAt.const_smul (1/2 : ℝ) using 1
    ext r
    simp [smul_eq_mul,div_eq_mul_inv,mul_comm]
  have heval := congrArg (fun L : E →L[ℝ] ℝ => L ξ) he
  rw [hQD.fderiv, smul_apply,smul_eq_mul,
    QuadraticHessian.first G ν hG hν, hgrad.self_of_nhds] at heval
  rw [hsym (fderiv ℝ ν a ξ) (ν a)] at heval
  have hge : (fun r => fderiv ℝ f r (ν a)) =ᶠ[𝓝 a]
      (fun r => -G r (ν r) (ν a)) := hgrad.mono (fun _ h => h (ν a))
  have hleft := hD.hasFDerivAt.clm_apply (hasFDerivAt_const (ν a) a)
  have hright := ((hG.hasFDerivAt.clm_apply hν.hasFDerivAt).clm_apply
    (hasFDerivAt_const (ν a) a)).neg
  have hEq := congrArg (fun L : E →L[ℝ] ℝ => L ξ)
    (hleft.unique (hright.congr_of_eventuallyEq hge))
  simp only [add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.flip_apply, neg_apply,
    zero_apply, map_zero, zero_add] at hEq
  rw [hsym (fderiv ℝ ν a ξ) (ν a)] at hEq
  linarith

 theorem covariant_radial (G : E → MetricTensor E) (ν : E → E) (f : E → ℝ)
    {S : Set E} (hS : IsOpen S) (hG : DifferentiableOn ℝ G S)
    (hsym : ∀ r ∈ S, ∀ v w, G r v w = G r w v)
    {a : E} (ha : a ∈ S) (hpos : ∀ v : E, v ≠ 0 → 0 < G a v v)
    (hν : DifferentiableAt ℝ ν a) (hf : ContDiffAt ℝ 2 f a)
    (henergy : f =ᶠ[𝓝 a] (fun r => G r (ν r) (ν r) / 2))
    (hgrad : ∀ᶠ r in 𝓝 a, ∀ w, fderiv ℝ f r w = -G r (ν r) w) (ξ : E) :
    fderiv ℝ (fderiv ℝ f) a ξ (ν a) +
        G a (ν a) (christoffel G a ξ (ν a)) = G a ξ (ν a) := by
  have hr := coordinate_radial G ν f ((hG a ha).differentiableAt (hS.mem_nhds ha))
    hν hf (hsym a ha) henergy hgrad ξ
  have hc := metric_christoffel hpos ξ (ν a) (ν a)
  rw [derivative_metric_symmetric hS hG hsym ha (ν a) ξ (ν a)] at hc
  rw [hsym a ha (ν a) (christoffel G a ξ (ν a)),hc,hsym a ha ξ (ν a)]
  linarith

end RadialHessianCalculus
end

end WeakMTWGlobalSupport

end OAI
end

section
-- module Solutions.OAIQW_WeakMTW.Variations_CovariantActionHessian
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace WeakMTWGlobalSupport

section

open Filter Set
open scoped Topology ContDiff
namespace RadialHessianCalculus
open CoordinateGeometry
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

 theorem actionForm_eq (G : E → MetricTensor E) (f : E → ℝ) (a ν v w : E)
    (hpos : ∀ z : E, z ≠ 0 → 0 < G a z z)
    (hsymm : ∀ z z', G a z z' = G a z' z) :
    actionForm G f a ν v w = fderiv ℝ (fderiv ℝ f) a v w +
      G a ν (christoffel G a v w) := by
  change _ + lowerChristoffel (fderiv ℝ G a) v w ν = _
  rw [hsymm ν,metric_christoffel hpos,lowerChristoffel_apply]

 theorem actionForm_radial (G : E → MetricTensor E) (ν : E → E) (f : E → ℝ)
    {S : Set E} (hS : IsOpen S) (hG : DifferentiableOn ℝ G S)
    (hsym : ∀ r ∈ S, ∀ v w, G r v w = G r w v)
    {a : E} (ha : a ∈ S) (hpos : ∀ v : E, v ≠ 0 → 0 < G a v v)
    (hν : DifferentiableAt ℝ ν a) (hf : ContDiffAt ℝ 2 f a)
    (henergy : f =ᶠ[𝓝 a] (fun r => G r (ν r) (ν r) / 2))
    (hgrad : ∀ᶠ r in 𝓝 a, ∀ w, fderiv ℝ f r w = -G r (ν r) w) (ξ : E) :
    actionForm G f a (ν a) ξ (ν a) = G a ξ (ν a) := by
  rw [actionForm_eq G f a (ν a) ξ (ν a) hpos (hsym a ha)]
  exact covariant_radial G ν f hS hG hsym ha hpos hν hf henergy hgrad ξ

end
end RadialHessianCalculus
end

end WeakMTWGlobalSupport

end OAI
end

section
-- module Solutions.OAIQW_WeakMTW.Variations_BranchInitialGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace WeakMTWGlobalSupport

section

open Set Filter Manifold Bundle
open scoped Topology ContDiff Manifold
namespace WeakMTW
noncomputable section
open RiemannianLocal ChartMetric CoordinateGeometry RadialHessianCalculus
variable {n : ℕ} {M : Type*} [MetricSpace M] [ChartedSpace (Model n) M]
  [IsManifold (model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace (model n) x)]
  [IsContMDiffRiemannianBundle (model n) ∞ (Model n) (fun x : M => TangentSpace (model n) x)]
  [IsRiemannianManifold (model n) M] [CompactSpace M]

 theorem branch_initial_smooth (x y : M)
    (e : OpenPartialHomeomorph (Model n × Model n) (Model n × Model n))
    (hes : e.source ⊆ pairExpDomain (n := n) x y)
    (hei : ContDiffOn ℝ ∞ e.symm e.target)
    {q : Model n × Model n} (hq : q ∈ e.target) :
    ContDiffAt ℝ ∞ (fun a => branchAction x e (a,q.2)) q.1 :=
  ContDiffAt.comp (f := fun a => (a,q.2)) (g := branchAction x e) q.1
    ((branchAction_smooth x y e hes hei q hq).contDiffAt (e.open_target.mem_nhds hq))
    (contDiffAt_id.prodMk contDiffAt_const)

 theorem branch_initial_radial_oai (x y : M)
    (e : OpenPartialHomeomorph (Model n × Model n) (Model n × Model n))
    (he : (e : (Model n × Model n) → (Model n × Model n)) = pairExpCoordinates (n := n) x y)
    (hes : e.source ⊆ pairExpDomain (n := n) x y)
    (hei : ContDiffOn ℝ ∞ e.symm e.target)
    {q : Model n × Model n} (hq : q ∈ e.target) (w : Model n) :
    actionForm (metric x) (fun a => branchAction x e (a,q.2)) q.1 (e.symm q).2
      w (e.symm q).2 = metric x q.1 w (e.symm q).2 := by
  let ν : Model n → Model n := fun a => (e.symm (a,q.2)).2
  let f : Model n → ℝ := fun a => branchAction x e (a,q.2)
  have hν : ContDiffAt ℝ ∞ ν q.1 :=
    ContDiffAt.comp (f := fun a => (a,q.2)) (g := fun z => (e.symm z).2) q.1
      (((hei q hq).contDiffAt (e.open_target.mem_nhds hq)).snd)
      (contDiffAt_id.prodMk contDiffAt_const)
  have hf := branch_initial_smooth x y e hes hei hq
  have hqT : q.1 ∈ (chartAt (Model n) x).target := by
    rw [← pair_inverse_fst x y e he hq]
    exact (stateChart_target x _).mp (hes (e.map_target hq)).1
  have hnear : ∀ᶠ a : Model n in 𝓝 q.1, (a,q.2) ∈ e.target :=
    (continuousAt_id.prodMk continuousAt_const).preimage_mem_nhds (e.open_target.mem_nhds hq)
  have henergy : f =ᶠ[𝓝 q.1] (fun a => metric x a (ν a) (ν a) / 2) := by
    filter_upwards [hnear] with a ha
    exact branchAction_is_kinetic x y e he ha
  have hgrad : ∀ᶠ a in 𝓝 q.1, ∀ w, fderiv ℝ f a w = -metric x a (ν a) w := by
    filter_upwards [hnear] with a ha w
    exact branch_initial_gradient x y e he hes hei ha w
  exact actionForm_radial (metric x) ν f (chartAt (Model n) x).open_target
    ((metric_smooth x).differentiableOn (by simp)) (fun a _ => metric_symmetric x a)
    hqT (fun v hv => metric_positive x hqT hv) (hν.differentiableAt (by simp))
    (hf.of_le (by first | simp | exact WithTop.coe_le_coe.mpr le_top)) henergy hgrad w

end
end WeakMTW
end

end WeakMTWGlobalSupport

end OAI
end

theorem solution.{u_1} : type_of% @OAI.WeakMTWGlobalSupport.WeakMTW.branch_initial_radial_oai.{u_1} := @OAI.WeakMTWGlobalSupport.WeakMTW.branch_initial_radial_oai.{u_1}
