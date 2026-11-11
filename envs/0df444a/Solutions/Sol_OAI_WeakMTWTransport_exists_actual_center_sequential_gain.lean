-- Prove2me | solution 1 for OAI.WeakMTWTransport.exists_actual_center_sequential_gain
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T19:26:46.243986+00:00
-- url     : https://prove2.me/submissions/3b017f38-461a-4d88-a1cd-b677055c6077

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
import Theorems.Thm_OAI_WeakMTWTransport_exists_uniform_center_support_pullback
import Theorems.Thm_OAI_WeakMTWTransport_moving_center_sequential_semibound
import Theorems.Thm_OAI_WeakMTWTransport_parametric_short_center_pole_limit

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Calculus_JetPullback
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace WeakMTWTransport

section
open Set Filter
open scoped Topology ContDiff

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

lemma second_fderiv_comp_affine {f : F → ℝ} (L : E →L[ℝ] F) (b : F) (x : E)
    (hf : ContDiffAt ℝ 2 f (b+L x)) (v w : E) :
    fderiv ℝ (fderiv ℝ (fun h => f (b+L h))) x v w =
      fderiv ℝ (fderiv ℝ f) (b+L x) (L v) (L w) := by
  have hL : ∀ y:E, HasFDerivAt (fun h : E => b+L h) L y :=
    fun y => (L.hasFDerivAt (x := y)).const_add b
  have hd := ((hf.fderiv_right (m := 1) (by norm_num)).differentiableAt
      (by norm_num)).hasFDerivAt.comp (f := fun h : E => b+L h) x (hL x)
  have H := hd.clm_comp (hasFDerivAt_const L x)
  have heq : (fun h => fderiv ℝ f (b+L h) |>.comp L) =ᶠ[𝓝 x]
      (fderiv ℝ (fun h => f (b+L h))) := by
    have hn := (hL x).continuousAt.eventually (hf.eventually (by norm_num))
    filter_upwards [hn] with h hh
    exact ((hh.differentiableAt (by norm_num)).hasFDerivAt.comp
      (f := fun h : E => b+L h) h (hL h)).fderiv.symm
  have he := congrArg (fun B : E →L[ℝ] E →L[ℝ] ℝ => B v w)
    (H.congr_of_eventuallyEq heq.symm).fderiv
  simpa only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.compL_apply,
    ContinuousLinearMap.flip_apply,map_zero,ContinuousLinearMap.comp_zero,
    zero_add,add_apply,zero_apply] using he

end

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

lemma half_norm_sq_fderiv :
    fderiv ℝ (fun v : E => ‖v‖^2/2) = innerSL ℝ := by
  funext p
  exact (half_norm_sq_hasFDerivAt p).fderiv

lemma half_norm_sq_second_fderiv (p a d : E) :
    fderiv ℝ (fderiv ℝ (fun v : E => ‖v‖^2/2)) p a d=inner ℝ a d := by
  rw [half_norm_sq_fderiv]
  rw [(innerSL ℝ).hasFDerivAt.fderiv]
  rfl

lemma half_norm_sq_contDiff : ContDiff ℝ ∞ (fun v : E => ‖v‖^2/2) := by
  simpa only [one_div,Pi.smul_apply,smul_eq_mul,div_eq_mul_inv,mul_comm,one_mul] using
    ((contDiff_norm_sq (𝕜 := ℝ) (E := E) (n := ∞)).const_smul (1/2:ℝ))

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Calculus_SecondFderivScalarComp
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Manifold Bundle
open scoped Topology ContDiff

namespace WeakMTWTransport

lemma second_fderiv_scalar_comp {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → ℝ} {φ : ℝ → ℝ} {x : E} (hf : ContDiffAt ℝ 2 f x)
    (hφ : ContDiffAt ℝ 2 φ (f x)) (ξ : E) :
    fderiv ℝ (fderiv ℝ (fun h => φ (f h))) x ξ ξ =
      iteratedDeriv 2 φ (f x)*(fderiv ℝ f x ξ)^2+
        deriv φ (f x)*fderiv ℝ (fderiv ℝ f) x ξ ξ := by
  let g := fun t : ℝ => f (x+t • ξ)
  have hg : ContDiffAt ℝ 2 g 0 := by
    change ContDiffAt ℝ 2 (f ∘ fun t : ℝ => x+t • ξ) 0
    exact (show ContDiffAt ℝ 2 f (x+(0:ℝ) • ξ) from by simpa using hf).comp (0:ℝ)
      (contDiffAt_const.add (contDiffAt_id.smul contDiffAt_const))
  have hg0 : g 0=f x := by simp [g]
  have hline : HasDerivAt (fun t : ℝ => x+t • ξ) ξ 0 := by
    convert! (hasDerivAt_const (0:ℝ) x).add ((hasDerivAt_id (0:ℝ)).smul_const ξ) using 1
    all_goals try with_reducible_and_instances rfl
    simp
  have hd : deriv g 0=fderiv ℝ f x ξ := by
    simpa only [Function.comp_def,g,zero_smul,add_zero] using
      ((show HasFDerivAt f (fderiv ℝ f x) (x+(0:ℝ) • ξ) from by
        simpa only [zero_smul,add_zero] using (hf.differentiableAt (by norm_num)).hasFDerivAt).comp_hasDerivAt (0:ℝ) hline).deriv
  have H := iteratedDeriv_comp_two (show ContDiffAt ℝ 2 φ (g 0) from hg0.symm ▸ hφ) hg
  rw [hg0,hd,show iteratedDeriv 2 g 0=fderiv ℝ (fderiv ℝ f) x ξ ξ from
    iteratedDeriv_two_affine_line hf ξ] at H
  change fderiv ℝ (fderiv ℝ (φ ∘ f)) x ξ ξ = _
  rw [←iteratedDeriv_two_affine_line (hφ.comp x hf) ξ]
  exact H

end WeakMTWTransport
end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Contact_CenterSupport
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

lemma scalarCostSupport_normal_jet {φ : ℝ → ℝ} {v0 l : ℝ} {x : M}
    {p : TangentSpace 𝓘(ℝ,Model n) x} {s : ℝ} (hs : s≠0)
    (hp : s • p∈injectivityDomain x) (hφ : ContDiffAt ℝ 2 φ v0)
    (hl : deriv φ v0=l) :
    ContDiffAt ℝ 2 (fun h : TangentSpace 𝓘(ℝ,Model n) x =>
      scalarCostSupport φ v0 x p s (riemannianExp x h)) 0 ∧
    HasFDerivAt (fun h : TangentSpace 𝓘(ℝ,Model n) x =>
      scalarCostSupport φ v0 x p s (riemannianExp x h)) (innerSL ℝ (l • p)) 0 ∧
    ∀ ξ : TangentSpace 𝓘(ℝ,Model n) x,
      fderiv ℝ (fderiv ℝ (fun h => scalarCostSupport φ v0 x p s (riemannianExp x h))) 0 ξ ξ =
        -(l/s)*hessianValue x (s • p) ξ+iteratedDeriv 2 φ v0*(inner ℝ p ξ)^2 := by
  let C := normalCost x (s • p)
  let f := fun h : TangentSpace 𝓘(ℝ,Model n) x => v0+C 0/s+(-s⁻¹)*C h
  have hf0 : f 0=v0 := by dsimp [f] <;> ring
  have hC : ContDiffAt ℝ 2 C 0 :=
    (normalCost_contDiffAt hp).of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  have hf : ContDiffAt ℝ 2 f 0 := contDiffAt_const.add (contDiffAt_const.mul hC)
  have hD : HasFDerivAt f (innerSL ℝ p) 0 := by
    apply (((normalCost_hasFDerivAt_zero hp).const_mul (-s⁻¹)).const_add (v0+C 0/s)).congr_fderiv
    ext h
    simp only [_root_.smul_apply,smul_eq_mul,innerSL_apply_apply,inner_neg_left,real_inner_smul_left]
    field_simp
  have he (h : TangentSpace 𝓘(ℝ,Model n) x) :
      scalarCostSupport φ v0 x p s (riemannianExp x h)=φ (f h) := by
    dsimp [scalarCostSupport,f,C,normalCost]
    rw [riemannianExp_zero]
    congr 1
    ring
  have heq : (fun h => scalarCostSupport φ v0 x p s (riemannianExp x h))=fun h => φ (f h) := funext he
  rw [heq]
  have hφf : ContDiffAt ℝ 2 φ (f 0) := hf0.symm ▸ hφ
  refine ⟨hφf.comp 0 hf,?_,?_⟩
  · have H := (hφf.differentiableAt (by norm_num)).hasDerivAt.comp_hasFDerivAt 0 hD
    rw [hf0,hl] at H
    apply H.congr_fderiv
    ext h
    simp only [_root_.smul_apply,smul_eq_mul,innerSL_apply_apply,real_inner_smul_left]
  · intro ξ
    rw [second_fderiv_scalar_comp hf hφf ξ,hf0,hl,hD.fderiv]
    have H : fderiv ℝ (fderiv ℝ f) 0 ξ ξ=(-s⁻¹)*hessianValue x (s • p) ξ := by
      have hd : fderiv ℝ f=fun h => (-s⁻¹) • fderiv ℝ C h := by
        funext h
        dsimp only [f]
        rw [fderiv_const_add]
        exact congrFun (fderiv_const_smul_field (𝕜 := ℝ) (f := C) (-s⁻¹)) h
      rw [hd]
      change fderiv ℝ ((-s⁻¹) • fderiv ℝ C) 0 ξ ξ = _
      rw [fderiv_const_smul_field (𝕜 := ℝ) (f := fderiv ℝ C) (-s⁻¹)]
      rw [hessianValue_eq_normalHessian hp]
      rfl
    rw [H]
    simp only [innerSL_apply_apply]
    ring

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Contact_CoordinateScalarSupport
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
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

lemma coordinateScalarSupport_contDiffAt {a : M} {b p : Model n} {v s : ℝ} {φ : ℝ → ℝ}
    (hb : b∈(extChartAt 𝓘(ℝ,Model n) a).target) (hs : s≠0)
    (hp : s • (trivializationAt (Model n) (TangentSpace 𝓘(ℝ,Model n)) a).symmL ℝ
      ((extChartAt 𝓘(ℝ,Model n) a).symm b) p∈
        injectivityDomain ((extChartAt 𝓘(ℝ,Model n) a).symm b))
    (hφ : ContDiffAt ℝ ∞ φ v) :
    ContDiffAt ℝ ∞ (coordinateScalarSupport a φ) (((v,s),(b,p)),b) := by
  let χ := extChartAt 𝓘(ℝ,Model n) a
  let Q := ((ℝ×ℝ)×(Model n×Model n))×Model n
  let q : Q := (((v,s),(b,p)),b)
  have hi : ContMDiffAt 𝓘(ℝ,Model n) 𝓘(ℝ,Model n) ∞ χ.symm b :=
    (contMDiffOn_extChartAt_symm a).contMDiffAt ((isOpen_extChartAt_target a).mem_nhds hb)
  have hA : ContMDiffAt 𝓘(ℝ,Q) 𝓘(ℝ,Model n) ∞
      (fun q : Q => movingNormal a (q.1.2.1,q.1.1.2 • q.1.2.2)) q :=
    (movingNormal_contMDiffAt (q := (b,s • p)) hb).comp
      (f := fun q : Q => (q.1.2.1,q.1.1.2 • q.1.2.2)) q
      (contDiffAt_fst.snd.fst.prodMk (contDiffAt_fst.fst.snd.smul contDiffAt_fst.snd.snd)).contMDiffAt
  have hc := cost_contMDiffAt_of_injectivityDomain
    (⟨χ.symm b,s • (trivializationAt (Model n) (TangentSpace 𝓘(ℝ,Model n)) a).symmL ℝ (χ.symm b) p⟩ :
      TangentBundle 𝓘(ℝ,Model n) M) hp
  have he : movingNormal a (b,s • p)=riemannianExp (χ.symm b)
      (s • (trivializationAt (Model n) (TangentSpace 𝓘(ℝ,Model n)) a).symmL ℝ (χ.symm b) p) := by
    rw [movingNormal_eq hb,map_smul]
  rw [←he] at hc
  have hC : ContDiffAt ℝ ∞ (fun q : Q => cost (χ.symm q.1.2.1)
      (movingNormal a (q.1.2.1,q.1.1.2 • q.1.2.2))) q :=
    (hc.comp (f := fun q : Q => (χ.symm q.1.2.1,
      movingNormal a (q.1.2.1,q.1.1.2 • q.1.2.2))) q
      ((hi.comp (f := fun q : Q => q.1.2.1) q
        contDiffAt_fst.snd.fst.contMDiffAt).prodMk hA)).contDiffAt
  have hD : ContDiffAt ℝ ∞ (fun q : Q => cost (χ.symm q.2)
      (movingNormal a (q.1.2.1,q.1.1.2 • q.1.2.2))) q :=
    (hc.comp (f := fun q : Q => (χ.symm q.2,
      movingNormal a (q.1.2.1,q.1.1.2 • q.1.2.2))) q
      ((hi.comp (f := fun q : Q => q.2) q contDiffAt_snd.contMDiffAt).prodMk hA)).contDiffAt
  have hF := (contDiffAt_fst.fst.fst.add (hC.div contDiffAt_fst.fst.snd hs)).sub
    (hD.div contDiffAt_fst.fst.snd hs)
  have hv : q.1.1.1+cost (χ.symm q.1.2.1) (movingNormal a (q.1.2.1,q.1.1.2 • q.1.2.2))/q.1.1.2-
      cost (χ.symm q.2) (movingNormal a (q.1.2.1,q.1.1.2 • q.1.2.2))/q.1.1.2=v := by
    dsimp only [q] <;> ring
  exact (show ContDiffAt ℝ ∞ φ _ from hv.symm ▸ hφ).comp q hF

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Contact_ActualEnvelopeJets
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



noncomputable section
open Set Filter Manifold Bundle
open scoped Topology ContDiff NNReal

namespace WeakMTWTransport
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]
variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [CompleteSpace P]

omit [Nonempty M] [CompleteSpace P] in
lemma jointScalarSupport_contDiffAt {a : M} {b p : Model n} {v s : ℝ}
    {param : P} {Φ : P×ℝ → ℝ}
    (hb : b∈(extChartAt 𝓘(ℝ,Model n) a).target) (hs : s≠0)
    (hp : s • (trivializationAt (Model n) (TangentSpace 𝓘(ℝ,Model n)) a).symmL ℝ
      ((extChartAt 𝓘(ℝ,Model n) a).symm b) p∈
        injectivityDomain ((extChartAt 𝓘(ℝ,Model n) a).symm b))
    (hΦ : ContDiffAt ℝ ∞ Φ (param,v)) :
    ContDiffAt ℝ ∞ (jointScalarSupport a Φ) ((param,((v,s),(b,p))),b) := by
  have hF := (coordinateScalarSupport_contDiffAt hb hs hp contDiffAt_id).comp
    ((param,((v,s),(b,p))),b) (contDiffAt_fst.snd.prodMk contDiffAt_snd)
  have hpair := contDiffAt_fst.fst.prodMk hF
  exact (show ContDiffAt ℝ ∞ Φ
    (param,coordinateScalarSupport a id (((v,s),(b,p)),b)) from by
      simpa only [coordinateScalarSupport_self,id_eq] using hΦ).comp
        (f := fun q : (P×((ℝ×ℝ)×(Model n×Model n)))×Model n =>
          (q.1.1,coordinateScalarSupport a id (q.1.2,q.2))) _ hpair
end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Regularity_StationaryPullback
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace WeakMTWTransport

section
open Set Filter
open scoped Topology ContDiff

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

lemma second_fderiv_comp_stationary {f : F → ℝ} {g : E → F} {x : E}
    (hf : ContDiffAt ℝ 2 f (g x)) (hg : ContDiffAt ℝ 2 g x)
    (hzero : fderiv ℝ f (g x)=0) (v w : E) :
    fderiv ℝ (fderiv ℝ (fun a => f (g a))) x v w =
      fderiv ℝ (fderiv ℝ f) (g x) (fderiv ℝ g x v) (fderiv ℝ g x w) := by
  have hgd := (hg.differentiableAt (by norm_num)).hasFDerivAt
  have hd1 := ((hf.fderiv_right (m := 1) (by norm_num)).differentiableAt
      (by norm_num)).hasFDerivAt.comp (f := g) x hgd
  have hd2 := ((hg.fderiv_right (m := 1) (by norm_num)).differentiableAt
      (by norm_num)).hasFDerivAt
  have hd := hd1.clm_comp hd2
  have heq : (fun a => (fderiv ℝ f (g a)).comp (fderiv ℝ g a)) =ᶠ[𝓝 x]
      fderiv ℝ (fun a => f (g a)) := by
    filter_upwards [hgd.continuousAt.eventually (hf.eventually (by norm_num)),
      hg.eventually (by norm_num)] with a hfa hga
    exact ((hfa.differentiableAt (by norm_num)).hasFDerivAt.comp (f := g) a
      (hga.differentiableAt (by norm_num)).hasFDerivAt).fderiv.symm
  have H := congrArg (fun A : E →L[ℝ] E →L[ℝ] ℝ => A v w)
    (hd.congr_of_eventuallyEq heq.symm).fderiv
  simpa only [Function.comp_apply,hzero,ContinuousLinearMap.comp_apply,ContinuousLinearMap.compL_apply,
    ContinuousLinearMap.flip_apply,ContinuousLinearMap.zero_comp,zero_apply,
    zero_add,add_zero,add_apply] using H

end

open Set Filter Manifold Bundle
open scoped Topology ContDiff

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Regularity_ActiveGraphLimit
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
open Set Filter Manifold Bundle
open scoped Topology ContDiff

namespace WeakMTWTransport
variable {n : ℕ} {M : Type*} [MetricSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]

lemma chartFiberInverse_at_center (a : M) (p : Model n) :
    chartFiberInverse a ((extChartAt 𝓘(ℝ,Model n) a) a) p=p := by
  dsimp only [chartFiberInverse]
  rw [(extChartAt 𝓘(ℝ,Model n) a).left_inv (mem_extChartAt_source a)]
  rw [TangentBundle.symmL_trivializationAt_eq_core (mem_chart_source (Model n) a)]
  exact tangentCoordChange_self (I := 𝓘(ℝ,Model n)) (mem_extChartAt_source a)
end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Contact_CenterSupportFamily
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
open Set Filter Manifold Bundle
open scoped Topology ContDiff NNReal

namespace WeakMTWTransport
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

omit [CompactSpace M] [Nonempty M]
  [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M] in
lemma center_row_parameter_tendsto {c : M} {v : M → ℝ} (hv : Continuous v)
    {γj lj : ℕ → ℝ} {xj rj : ℕ → Model n} {γ l : ℝ} {r : Model n}
    (hγ : Tendsto γj atTop (𝓝 γ)) (hl : Tendsto lj atTop (𝓝 l))
    (hx : Tendsto xj atTop (𝓝 (extChartAt 𝓘(ℝ,Model n) c c)))
    (hr : Tendsto rj atTop (𝓝 r)) :
    Tendsto (fun i=>centerRowParameter c v (γj i) (lj i) (xj i) (rj i)) atTop
      (𝓝 (γ,((v c,(1+l)/2),(extChartAt 𝓘(ℝ,Model n) c c,r)))) := by
  have hb := (extChartAt 𝓘(ℝ,Model n) c).map_source (mem_extChartAt_source c)
  have hy := (continuousAt_extChartAt_symm'' hb).tendsto.comp hx
  rw [(extChartAt 𝓘(ℝ,Model n) c).left_inv (mem_extChartAt_source c)] at hy
  exact hγ.prodMk_nhds (((hv.tendsto c).comp hy).prodMk_nhds
    ((tendsto_const_nhds.add hl).div_const 2) |>.prodMk_nhds (hx.prodMk_nhds hr))

omit [Nonempty M] in
lemma center_limit_support_smooth {c : M} {r : Model n} {γ l : ℝ} {v : M → ℝ}
    {Φ : ℝ×ℝ → ℝ} (hΦ : ContDiffAt ℝ ∞ Φ (γ,v c))
    (hr : (show TangentSpace 𝓘(ℝ,Model n) c from r)∈minimizingVectors c)
    (hl : 0<l) (hl1 : l<1) :
    ContDiffAt ℝ ∞ (jointScalarSupport c Φ)
      ((γ,((v c,(1+l)/2),(extChartAt 𝓘(ℝ,Model n) c c,r))),extChartAt 𝓘(ℝ,Model n) c c) := by
  have hb := (extChartAt 𝓘(ℝ,Model n) c).map_source (mem_extChartAt_source c)
  have hp : ((1+l)/2) • chartFiberInverse c (extChartAt 𝓘(ℝ,Model n) c c) r∈
      injectivityDomain ((extChartAt 𝓘(ℝ,Model n) c).symm (extChartAt 𝓘(ℝ,Model n) c c)) := by
    rw [chartFiberInverse_at_center,(extChartAt 𝓘(ℝ,Model n) c).left_inv (mem_extChartAt_source c)]
    exact contracted_minimizer_mem_injectivityDomain hr (by linarith) (by linarith)
  exact jointScalarSupport_contDiffAt hb (by linarith) hp hΦ

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Regularity_SecondFderivAdd
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Manifold Bundle
open scoped Topology ContDiff

namespace WeakMTWTransport

lemma second_fderiv_add_eq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f g : E → ℝ} {z : E} (hf : ContDiffAt ℝ 2 f z) (hg : ContDiffAt ℝ 2 g z) :
    fderiv ℝ (fderiv ℝ (fun w => f w+g w)) z =
      fderiv ℝ (fderiv ℝ f) z+fderiv ℝ (fderiv ℝ g) z := by
  have he : fderiv ℝ (fun w => f w+g w) =ᶠ[𝓝 z]
      (fun w => fderiv ℝ f w+fderiv ℝ g w) := by
    filter_upwards [hf.eventually (by norm_num),hg.eventually (by norm_num)] with w hw hw'
    exact fderiv_fun_add (hw.differentiableAt (by norm_num)) (hw'.differentiableAt (by norm_num))
  rw [he.fderiv_eq]
  exact fderiv_fun_add ((hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num))
    ((hg.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num))

end WeakMTWTransport
end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Regularity_CenterFullPullback
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one
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
section CenterFullPullback
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

omit [Nonempty M] in
lemma scalar_support_full_pullback_identity {a b : M}
    {p : TangentSpace 𝓘(ℝ,Model n) a} {q : TangentSpace 𝓘(ℝ,Model n) b}
    {l s : ℝ} {φ : ℝ → ℝ} {v : ℝ}
    (hs : s≠0) (hp : s • p∈injectivityDomain a)
    (hlp : l • p∈injectivityDomain a) (hq : q∈injectivityDomain b)
    (hab : riemannianExp a (l • p)=b)
    (hφ : ContDiffAt ℝ 2 φ v) (hφd : deriv φ v=l)
    {R : TangentSpace 𝓘(ℝ,Model n) b → TangentSpace 𝓘(ℝ,Model n) a}
    (hR : ContDiffAt ℝ ∞ R q) (hR0 : R q=0)
    (hRe : ∀ᶠ w in 𝓝 q,riemannianExp a (R w)=riemannianExp b w)
    (d : TangentSpace 𝓘(ℝ,Model n) b) :
    ‖d‖^2+fderiv ℝ (fderiv ℝ (fun w=>scalarCostSupport φ v a p s
      (riemannianExp b w))) q d d=
      fderiv ℝ (fderiv ℝ (fun h=>scalarCostSupport φ v a p s
        (riemannianExp a h))) 0 (fderiv ℝ R q d) (fderiv ℝ R q d)+
      hessianValue a (l • p) (fderiv ℝ R q d) := by
  let S := fun h:TangentSpace 𝓘(ℝ,Model n) a=>scalarCostSupport φ v a p s (riemannianExp a h)
  let C := normalCost a (l • p)
  have hc : ContDiffAt ℝ 2 C 0 :=
    (normalCost_contDiffAt hlp).of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  obtain ⟨hsC,hsD,_⟩ := scalarCostSupport_normal_jet hs hp hφ hφd
  have hstat : fderiv ℝ (fun h=>S h+C h) 0=0 := by
    rw [fderiv_fun_add (hsC.differentiableAt (by norm_num)) (hc.differentiableAt (by norm_num)),
      hsD.fderiv,(normalCost_hasFDerivAt_zero hlp).fderiv]
    simp only [map_neg,add_neg_cancel]
  have hR2 := hR.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  have hcomp := second_fderiv_comp_stationary (f := fun h=>S h+C h)
    (hR0.symm ▸ hsC.add hc) hR2 (by rwa [hR0]) d d
  rw [hR0,second_fderiv_add_eq hsC hc] at hcomp
  rw [hessianValue_eq_normalHessian hlp]
  have he : (fun w=>S (R w)+C (R w))=ᶠ[𝓝 q]
      (fun w=>scalarCostSupport φ v a p s (riemannianExp b w)+‖w‖^2/2) := by
    filter_upwards [hRe,(isOpen_injectivityDomain b).mem_nhds hq] with w hw hwi
    dsimp only [S,C,normalCost]
    rw [hw,hab]
    congr 1
    change dist (riemannianExp b w) b^2/2=‖w‖^2/2
    rw [dist_comm,injectivityDomain_subset_minimizingVectors b hwi]
  have hsE : ContDiffAt ℝ 2 (fun w=>scalarCostSupport φ v a p s (riemannianExp b w)) q :=
    ((hR0.symm ▸ hsC).comp q hR2).congr_of_eventuallyEq
      (hRe.mono (fun w hw=>congrArg (scalarCostSupport φ v a p s) hw.symm))
  rw [he.fderiv.fderiv_eq,second_fderiv_add_eq hsE
    ((half_norm_sq_contDiff.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)).contDiffAt),
    add_apply,add_apply,half_norm_sq_second_fderiv] at hcomp
  simpa only [innerSL_apply_apply,real_inner_self_eq_norm_sq,add_comm,S,C,normalHessian,add_apply] using hcomp

omit [Nonempty M] in
lemma exists_uniform_center_full_pullback :
    ∃ c>0,∀ᶠ l : ℝ in 𝓝 1, 0<l → l<1 → ∀ a b : M,
      ∀ p : TangentSpace 𝓘(ℝ,Model n) a,
      ∀ q : TangentSpace 𝓘(ℝ,Model n) b,
      p∈minimizingVectors a → q∈injectivityDomain b →
      riemannianExp a (l • p)=b → riemannianExp b q=a →
      ∀ (φ : ℝ → ℝ) (v : ℝ), ContDiffAt ℝ 2 φ v → deriv φ v=l →
      ∀ d : TangentSpace 𝓘(ℝ,Model n) b,
        c*(1-l)*‖d‖^2+(iteratedDeriv 2 φ v/l^2)*(inner ℝ q d)^2≤
          ‖d‖^2+fderiv ℝ (fderiv ℝ (fun w=>scalarCostSupport φ v a p ((1+l)/2)
            (riemannianExp b w))) q d d := by
  obtain ⟨c,hc,H⟩ := exists_uniform_center_support_pullback (n := n) (M := M)
  refine ⟨c,hc,?_⟩
  filter_upwards [H] with l hl
  intro hl0 hl1 a b p q hp hq hab hba φ v hφ hφd d
  obtain ⟨R,hR,hR0,hRe,HR⟩ := hl hl1 a b p q hp hq hab hba φ v hφ hφd
  have hs : 0<(1+l)/2 := by linarith
  have hs1 : (1+l)/2<1 := by linarith
  rw [scalar_support_full_pullback_identity hs.ne'
    (contracted_minimizer_mem_injectivityDomain hp hs hs1)
    (contracted_minimizer_mem_injectivityDomain hp hl0 hl1) hq hab hφ hφd hR hR0 hRe]
  exact HR d

end CenterFullPullback
end WeakMTWTransport

end
end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_LocalFlow_ModelTangentJet
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
section ModelTangentJet
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

omit [CompactSpace M] [Nonempty M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M] in
lemma center_frame_identity (a : M) (d : Model n) :
    (trivializationAt (Model n) (TangentSpace 𝓘(ℝ,Model n)) a).symmL ℝ a d=d := by
  rw [TangentBundle.symmL_trivializationAt_eq_core (mem_chart_source (Model n) a)]
  exact tangentCoordChange_self (I := 𝓘(ℝ,Model n)) (mem_extChartAt_source a)

omit [CompactSpace M] [Nonempty M]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M] in
lemma model_tangent_second_fderiv {a : M} {f : TangentSpace 𝓘(ℝ,Model n) a → ℝ}
    {q : Model n} (hf : ContDiffAt ℝ 2 f q) (d e : Model n) :
    fderiv ℝ (fderiv ℝ (fun r : Model n=>f r)) q d e=
      fderiv ℝ (fderiv ℝ f) q d e := by
  let A := (trivializationAt (Model n) (TangentSpace 𝓘(ℝ,Model n)) a).symmL ℝ a
  have hA (r : Model n) : A r=r := center_frame_identity a r
  have hz (r : Model n) : (0 : TangentSpace 𝓘(ℝ,Model n) a)+A r=r :=
    (zero_add (A r)).trans (hA r)
  have H := second_fderiv_comp_affine (E := Model n) (F := TangentSpace 𝓘(ℝ,Model n) a) (f := f) A 0 q
    (by simpa only [hz] using hf) d e
  have he : (fun h : Model n => f ((0 : TangentSpace 𝓘(ℝ,Model n) a)+A h))=
      (fun h : Model n => f h) := by funext h; rw [hz h]
  rw [he,hz q,hA d,hA e] at H
  exact H

omit [Nonempty M] in
lemma scalarCostSupport_endpoint_contDiffAt {a c : M}
    {q : TangentSpace 𝓘(ℝ,Model n) a} {r : TangentSpace 𝓘(ℝ,Model n) c}
    {v s : ℝ} {φ : ℝ → ℝ} (hr : s • r∈injectivityDomain c)
    (he : riemannianExp a q=c) (hφ : ContDiffAt ℝ 2 φ v) :
    ContDiffAt ℝ 2 (fun w=>scalarCostSupport φ v c r s (riemannianExp a w)) q := by
  have hC := cost_contMDiffAt_of_injectivityDomain
    (⟨c,s • r⟩ : TangentBundle 𝓘(ℝ,Model n) M) hr
  have hC' : ContMDiffAt (𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n)) 𝓘(ℝ,ℝ) ∞
      (fun z:M×M=>cost z.1 z.2) (riemannianExp a q,riemannianExp c (s • r)) := by
    rwa [he]
  have hpair : ContMDiffAt 𝓘(ℝ,TangentSpace 𝓘(ℝ,Model n) a)
      (𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n)) ∞
      (fun w : TangentSpace 𝓘(ℝ,Model n) a => (riemannianExp a w,riemannianExp c (s • r))) q :=
    (contMDiff_riemannianExp_fiber a q).prodMk contMDiffAt_const
  have hcost : ContDiffAt ℝ ∞ (fun w : TangentSpace 𝓘(ℝ,Model n) a =>
      cost (riemannianExp a w) (riemannianExp c (s • r))) q :=
    (hC'.comp (g := fun z:M×M=>cost z.1 z.2) q hpair).contDiffAt
  have hf : ContDiffAt ℝ ∞ (fun w=>v+cost c (riemannianExp c (s • r))/s-
      cost (riemannianExp a w) (riemannianExp c (s • r))/s) q :=
    contDiffAt_const.sub (hcost.div_const s)
  have hval : v+cost c (riemannianExp c (s • r))/s-cost (riemannianExp a q) (riemannianExp c (s • r))/s=v := by
    rw [he,add_sub_cancel_right]
  exact (hval.symm ▸ hφ).comp q (hf.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2))

omit [Nonempty M] in
lemma model_riemannianExp_continuous (a : M) :
    Continuous (fun w : Model n=>riemannianExp a w) := by
  let A := (trivializationAt (Model n) (TangentSpace 𝓘(ℝ,Model n)) a).symmL ℝ a
  have H := (continuous_riemannianExp a).comp A.continuous
  have he : riemannianExp a ∘ A=(fun w : Model n=>riemannianExp a w) := by
    funext w
    exact congrArg (riemannianExp a) (center_frame_identity a w)
  rwa [he] at H

omit [CompactSpace M] [Nonempty M]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M] in
lemma coordinateScalarSupport_center_value (c : M) (v s : ℝ) (φ : ℝ → ℝ)
    (r z : Model n) :
    coordinateScalarSupport c φ (((v,s),(extChartAt 𝓘(ℝ,Model n) c c,r)),z)=
      scalarCostSupport φ v c r s ((extChartAt 𝓘(ℝ,Model n) c).symm z) := by
  have hx := (extChartAt 𝓘(ℝ,Model n) c).map_source (mem_extChartAt_source c)
  have hb := (extChartAt 𝓘(ℝ,Model n) c).left_inv (mem_extChartAt_source c)
  rw [coordinateScalarSupport_eq hx,hb,center_frame_identity]

omit [Nonempty M] in
lemma coordinate_support_endpoint_germ {a c : M} {q r : Model n}
    (v s : ℝ) (φ : ℝ → ℝ) (he : riemannianExp a q=c) :
    (fun w : Model n=>coordinateScalarSupport c φ
      (((v,s),(extChartAt 𝓘(ℝ,Model n) c c,r)),extChartAt 𝓘(ℝ,Model n) c (riemannianExp a w)))=ᶠ[𝓝 q]
      (fun w : Model n=>scalarCostSupport φ v c r s (riemannianExp a w)) := by
  have hx := (extChartAt 𝓘(ℝ,Model n) c).map_source (mem_extChartAt_source c)
  have hb := (extChartAt 𝓘(ℝ,Model n) c).left_inv (mem_extChartAt_source c)
  have hExp := (model_riemannianExp_continuous a).continuousAt (x := q)
  have hqc : riemannianExp a q∈(extChartAt 𝓘(ℝ,Model n) c).source := by
    rw [he]
    exact mem_extChartAt_source c
  have hsource := hExp.eventually ((isOpen_extChartAt_source c).mem_nhds hqc)
  filter_upwards [hsource] with w hw
  rw [coordinateScalarSupport_center_value,(extChartAt 𝓘(ℝ,Model n) c).left_inv hw]

omit [Nonempty M] in
lemma coordinate_support_endpoint_hessian {a c : M} {q r : Model n}
    {v s : ℝ} {φ : ℝ → ℝ}
    (hr : s • (show TangentSpace 𝓘(ℝ,Model n) c from r)∈injectivityDomain c)
    (he : riemannianExp a q=c) (hφ : ContDiffAt ℝ 2 φ v) (d e : Model n) :
    fderiv ℝ (fderiv ℝ (fun w : Model n=>coordinateScalarSupport c φ
      (((v,s),(extChartAt 𝓘(ℝ,Model n) c c,r)),extChartAt 𝓘(ℝ,Model n) c (riemannianExp a w)))) q d e=
      fderiv ℝ (fderiv ℝ (fun w : TangentSpace 𝓘(ℝ,Model n) a=>
        scalarCostSupport φ v c r s (riemannianExp a w))) q d e := by
  rw [(coordinate_support_endpoint_germ v s φ he).fderiv.fderiv_eq]
  exact model_tangent_second_fderiv (scalarCostSupport_endpoint_contDiffAt hr he hφ) d e

omit [Nonempty M] in
lemma exists_uniform_coordinate_center_full_pullback :
    ∃ c0>0,∀ᶠ l : ℝ in 𝓝 1, 0<l → l<1 → ∀ a c : M,∀ r q : Model n,
      (show TangentSpace 𝓘(ℝ,Model n) c from r)∈minimizingVectors c →
      (show TangentSpace 𝓘(ℝ,Model n) a from q)∈injectivityDomain a →
      riemannianExp c (l • r)=a → riemannianExp a q=c →
      ∀ (φ : ℝ → ℝ) (v : ℝ), ContDiffAt ℝ 2 φ v → deriv φ v=l → ∀ d : Model n,
        c0*(1-l)*‖show TangentSpace 𝓘(ℝ,Model n) a from d‖^2+
          (iteratedDeriv 2 φ v/l^2)*(inner ℝ (show TangentSpace 𝓘(ℝ,Model n) a from q) d)^2 ≤
        inner ℝ (show TangentSpace 𝓘(ℝ,Model n) a from d) d+
          fderiv ℝ (fderiv ℝ (fun w : Model n=>coordinateScalarSupport c φ
            (((v,(1+l)/2),(extChartAt 𝓘(ℝ,Model n) c c,r)),
              extChartAt 𝓘(ℝ,Model n) c (riemannianExp a w)))) q d d := by
  obtain ⟨c0,hc0,H⟩ := exists_uniform_center_full_pullback (n := n) (M := M)
  refine ⟨c0,hc0,?_⟩
  filter_upwards [H] with l hl
  intro hl0 hl1 a c r q hr hq hac hca φ v hφ hd d
  rw [coordinate_support_endpoint_hessian
    (contracted_minimizer_mem_injectivityDomain hr (by linarith) (by linarith)) hca hφ,
    real_inner_self_eq_norm_sq]
  exact hl hl0 hl1 c a r q hr hq hac hca φ v hφ hd d

end ModelTangentJet
end WeakMTWTransport

end
end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Regularity_CenterPoleLimit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open Set Filter Manifold Bundle
open scoped Topology ContDiff NNReal

namespace WeakMTWTransport
section CenterPoleLimit
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]
variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [CompleteSpace P]

omit [Nonempty M] in
lemma reverse_minimizer_regular {a c : M}
    {r : TangentSpace 𝓘(ℝ,Model n) c} {q : TangentSpace 𝓘(ℝ,Model n) a}
    (hr : r∈injectivityDomain c) (hq : q∈minimizingVectors a)
    (ha : riemannianExp c r=a) (hc : riemannianExp a q=c) : q∈injectivityDomain a := by
  let z : TangentBundle 𝓘(ℝ,Model n) M := ⟨c,r⟩
  have hb : (reverseRay z).1=a := (reverseRay_base z).trans ha
  have hR := reverseRay_regular (z := z) hr
  have hE := reverseRay_endpoint z
  generalize hw : reverseRay z=w
  rw [hw] at hb hR hE
  rcases w with ⟨b,p⟩
  change b=a at hb
  subst b
  have he := riemannianExp_interior_unique hR hq (hE.trans hc.symm)
  exact he ▸ hR

end CenterPoleLimit
end WeakMTWTransport

end
end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Convexity_ActualCenterSemibound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open Set Filter Manifold Bundle
open scoped Topology ContDiff NNReal

namespace WeakMTWTransport
section ActualCenterSemibound
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma exists_actual_center_sequential_gain_oai :
    ∃ c0>0,∀ᶠ l : ℝ in 𝓝 1, 0<l → l<1 →
      ∀ (a c : M) (u v : M → ℝ) (Φ : ℝ×ℝ → ℝ) (γ : ℝ),
      Continuous v → ContDiffAt ℝ ∞ Φ (γ,v c) →
      deriv (fun s=>Φ (γ,s)) (v c)=l →
      ∀ (γj lj τj tj : ℕ → ℝ) (xj bj qj : ℕ → Model n) (zj : ℕ → M)
        (F : ℕ → Model n → ℝ),
      ∀ D : CenterSequenceData a c u v Φ γj lj τj tj xj bj qj zj F,
      ∀ (r q : Model n),
      (show TangentSpace 𝓘(ℝ,Model n) c from r)∈minimizingVectors c →
      (show TangentSpace 𝓘(ℝ,Model n) a from q)∈minimizingVectors a →
      riemannianExp a q=c →
      Tendsto γj atTop (𝓝 γ) → Tendsto lj atTop (𝓝 l) →
      Tendsto τj atTop (𝓝 0) → Tendsto tj atTop (𝓝 1) →
      Tendsto xj atTop (𝓝 (extChartAt 𝓘(ℝ,Model n) c c)) →
      Tendsto bj atTop (𝓝 (extChartAt 𝓘(ℝ,Model n) a a)) →
      Tendsto qj atTop (𝓝 q) → Tendsto (fun i=>(D.row i).r) atTop (𝓝 r) →
      (∀ᶠ i in atTop,0<τj i) → ∀ L : ℝ≥0,
      (∀ᶠ i in atTop,LipschitzWith L (fun y=>Φ (γj i,v y))) →
      ∀ ε : ℝ,0<ε →
      ∀ᶠ i in atTop,∀ d : Model n,
        c0*(1-l)*‖show TangentSpace 𝓘(ℝ,Model n) a from d‖^2+
          (iteratedDeriv 2 (fun s=>Φ (γ,s)) (v c)/l^2)*
            (inner ℝ (show TangentSpace 𝓘(ℝ,Model n) a from q) d)^2-ε*‖d‖^2 ≤
        coordinateCenterMatrix a (tj i) (hopfLax (τj i) (fun y=>Φ (γj i,v y)))
          (bj i) (qj i) d d := by
  obtain ⟨c0,hc0,H⟩ := exists_uniform_coordinate_center_full_pullback (n := n) (M := M)
  refine ⟨c0,hc0,?_⟩
  filter_upwards [H] with l hgain
  intro hl hl1 a c u v Φ γ hv hΦ hder γj lj τj tj xj bj qj zj F D r q hr hq he
    hγ hlm hτ ht hx hb hqq hrr hτpos L hLip ε hε
  let p := (γ,((v c,(1+l)/2),(extChartAt 𝓘(ℝ,Model n) c c,r)))
  let pj := fun i=>centerRowParameter c v (γj i) (lj i) (xj i) (D.row i).r
  let ψ := jointScalarSupport (n := n) c Φ
  have hp : Tendsto pj atTop (𝓝 p) := center_row_parameter_tendsto hv hγ hlm hx hrr
  have hψ : ContDiffAt ℝ ∞ ψ (p,extChartAt 𝓘(ℝ,Model n) c c) :=
    center_limit_support_smooth hΦ hr hl hl1
  have hs : ((1+l)/2)≠0 := by linarith
  have hr' := contracted_minimizer_mem_injectivityDomain hr (t := (1+l)/2)
    (by linarith) (by linarith)
  have hc := (extChartAt 𝓘(ℝ,Model n) c).map_source (mem_extChartAt_source c)
  have hφinf : ContDiffAt ℝ ∞ (fun s=>Φ (γ,s)) (v c) :=
    hΦ.comp (v c) (contDiffAt_const.prodMk contDiffAt_id)
  have hφ2 : ContDiffAt ℝ 2 (fun s=>Φ (γ,s)) (v c) :=
    hφinf.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  have hφ : HasDerivAt (fun s=>Φ (γ,s)) l (v c) := by
    rw [←hder]
    exact (hφinf.differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).hasDerivAt
  have hforward (i : ℕ) : parametricShortForward c ψ ((pj i,τj i),xj i)=
      extChartAt 𝓘(ℝ,Model n) c (zj i) := (D.row i).forward
  have hbelow : ∀ᶠ i in atTop,∀ w,ψ (pj i,w)≤Φ (γj i,v ((extChartAt 𝓘(ℝ,Model n) c).symm w)) :=
    Eventually.of_forall (fun i=>(D.row i).below)
  have htouch : ∀ᶠ i in atTop,
      Φ (γj i,v ((extChartAt 𝓘(ℝ,Model n) c).symm (xj i)))=ψ (pj i,xj i) :=
    Eventually.of_forall (fun i=>(D.row i).touching.symm)
  have ha : Tendsto (fun i=>(extChartAt 𝓘(ℝ,Model n) a).symm (bj i)) atTop (𝓝 a) := by
    have hb0 := (extChartAt 𝓘(ℝ,Model n) a).map_source (mem_extChartAt_source a)
    have hy := (continuousAt_extChartAt_symm'' hb0).tendsto.comp hb
    rw [(extChartAt 𝓘(ℝ,Model n) a).left_inv (mem_extChartAt_source a)] at hy
    exact hy
  have hd : ∀ᶠ i in atTop,DifferentiableAt ℝ
      (fun w=>hopfLax (τj i) (fun y=>Φ (γj i,v y)) ((extChartAt 𝓘(ℝ,Model n) c).symm w))
        (parametricShortForward c ψ ((pj i,τj i),xj i)) := by
    filter_upwards [D.derivative] with i hi
    rw [hforward]
    exact hi.1.self_of_nhds
  have herr := D.gradient.congr' (Eventually.of_forall (fun i=>by rw [←hforward i]))
  have hback : ∀ᶠ i in atTop,coordinateBackward c (tj i,
      parametricShortForward c ψ ((pj i,τj i),xj i),
      fderiv ℝ (F i) (parametricShortForward c ψ ((pj i,τj i),xj i)))=
        (extChartAt 𝓘(ℝ,Model n) a).symm (bj i) := by
    simpa only [hforward] using D.backward
  have hstationary : a=riemannianExp c (l • r) :=
    parametric_short_center_pole_limit L hψ hs hr' hφ rfl hp hx ht hτ ha hτpos hLip
      hbelow htouch hd herr hback
  have hregular : (show TangentSpace 𝓘(ℝ,Model n) a from q)∈injectivityDomain a :=
    reverse_minimizer_regular (contracted_minimizer_mem_injectivityDomain hr hl hl1)
      hq hstationary.symm he
  have hsource : riemannianExp a q∈(extChartAt 𝓘(ℝ,Model n) c).source := by
    rw [he]
    exact mem_extChartAt_source c
  have hz : ∀ᶠ i in atTop,movingPrefixChart a c (tj i) (bj i) (qj i)=
      parametricShortForward c ψ ((pj i,τj i),xj i) := Eventually.of_forall (fun i=>by
    rw [hforward,movingPrefixChart,D.endpoint])
  have hjet : ∀ᶠ i in atTop,
      (∀ᶠ z in 𝓝 (movingPrefixChart a c (tj i) (bj i) (qj i)),DifferentiableAt ℝ
        (fun z=>hopfLax (τj i) (fun y=>Φ (γj i,v y)) ((extChartAt 𝓘(ℝ,Model n) c).symm z)) z) ∧
      DifferentiableAt ℝ (fderiv ℝ
        (fun z=>hopfLax (τj i) (fun y=>Φ (γj i,v y)) ((extChartAt 𝓘(ℝ,Model n) c).symm z)))
          (movingPrefixChart a c (tj i) (bj i) (qj i)) := by
    simpa only [movingPrefixChart,D.endpoint] using D.derivative
  have Hlow := moving_center_sequential_semibound L hc hψ hregular
    (congrArg (extChartAt 𝓘(ℝ,Model n) c) he) hsource hp hx hb hqq ht hτ hτpos hLip
      hbelow htouch hz hjet hε
  have HG := hgain hl hl1 a c r q hr hregular hstationary.symm he
    (fun s=>Φ (γ,s)) (v c) hφ2 hder
  filter_upwards [Hlow] with i hi
  intro d
  exact (sub_le_sub_right (HG d) _).trans (hi d)

end ActualCenterSemibound
end WeakMTWTransport

end
end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.WeakMTWTransport.exists_actual_center_sequential_gain_oai.{u_1} := @OAI.WeakMTWTransport.exists_actual_center_sequential_gain_oai.{u_1}
