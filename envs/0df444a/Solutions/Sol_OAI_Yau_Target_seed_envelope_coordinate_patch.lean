-- Prove2me | solution 1 for OAI.Yau.Target.seed_envelope_coordinate_patch
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T00:30:42.151084+00:00
-- url     : https://prove2.me/submissions/ef41e71d-b9ed-4137-8bbb-0c0c1f359b23

import Mathlib
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.Finsupp.Weight
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.ColumnRowPartitioned
import Mathlib.Geometry.Manifold.Algebra.LieGroup
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Geometry.Manifold.Riemannian.Basic
import Mathlib.Geometry.Manifold.VectorBundle.Riemannian
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Definitions.Def_YauCounterexample
import Definitions.Def_OAIQ237Ny004

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_StereographicSecondDerivative
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open scoped ContDiff RealInnerProductSpace
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma stereoReciprocal_zero_hasFDerivAt :
    HasFDerivAt (stereoReciprocal : E → ℝ) (0 : E →L[ℝ] ℝ) (0:E) := by
  simpa [stereoReciprocal] using (stereoReciprocal_hasFDerivAt (0:E))

lemma stereoInvFunAux_second (v w u : E) :
    fderiv ℝ (fun x ↦ fderiv ℝ (stereoInvFunAux v) x w) 0 u = ⟪u,w⟫ • v := by
  simp_rw [stereoInvFunAux_fderiv]
  have hb : HasFDerivAt (fun x : E ↦ ⟪x,w⟫) (innerSL ℝ w) 0 := by
    convert! (innerSL ℝ w).hasFDerivAt (x := (0:E)) using 1
    all_goals try with_reducible_and_instances rfl
    funext y
    exact (real_inner_comm y w).symm
  have hA := (((stereoReciprocal_zero_hasFDerivAt (E := E)).pow 2).const_mul (-2:ℝ)).mul hb
  have hB := (hasFDerivAt_const ((4:ℝ) • w) (0:E)).add ((hb.const_mul (2:ℝ)).smul_const v)
  have hd := (hA.smul (stereoNumerator_hasFDerivAt v (0:E))).add
    (stereoReciprocal_zero_hasFDerivAt.smul hB)
  change HasFDerivAt (fun x : E ↦
    (-2 * stereoReciprocal x^2 * ⟪x,w⟫) • stereoNumerator v x +
      stereoReciprocal x • ((4:ℝ) • w + (2*⟪x,w⟫) • v)) _ 0 at hd
  rw [hd.fderiv]
  simp [stereoReciprocal,stereoNumerator,smul_smul,real_inner_comm]
  module

lemma stereoInvFunAux_second_fderiv (v w u : E) :
    fderiv ℝ (fderiv ℝ (stereoInvFunAux v)) 0 u w = ⟪u,w⟫ • v := by
  have hd := (contDiff_stereoInvFunAux (v := v) (m := ∞)).fderiv_right
    (show (∞ : WithTop ℕ∞)+1 ≤ ∞ by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  have he := (hd.differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) (0:E)).hasFDerivAt.clm_apply
    (hasFDerivAt_const w (0:E))
  have h := congrArg (fun L : E →L[ℝ] E ↦ L u) he.fderiv
  simp only [ContinuousLinearMap.comp_zero,zero_add,ContinuousLinearMap.flip_apply] at h
  rw [← h]
  exact stereoInvFunAux_second v w u

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Charts_CenteredSphereChart
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Manifold
open scoped ContDiff RealInnerProductSpace
noncomputable section

lemma centeredSphereChart_derivative (p : Base) :
    sphereChartDerivative p 0 = (centeredSphereIsometry p).toContinuousLinearMap := by
  let : ContinuousSMul ℝ BaseModel := IsBoundedSMul.continuousSMul
  let : ContinuousSMul ℝ AmbientBase := IsBoundedSMul.continuousSMul
  rw [sphereChartDerivative_eq_fderiv p (by rw [centeredSphereChart_target]; trivial),
    centeredSphereChart_inverse]
  have hs : HasFDerivAt (stereoInvFunAux (-(p : AmbientBase)))
      (ContinuousLinearMap.id ℝ AmbientBase) ((centeredSphereIsometry p).toContinuousLinearMap 0) := by
    simpa using hasFDerivAt_stereoInvFunAux (-(p : AmbientBase))
  have h := hs.comp (0:BaseModel)
    (centeredSphereIsometry p).toContinuousLinearMap.hasFDerivAt
  simpa using h.fderiv

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Charts_CenteredSphereSecondJet
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Manifold
open scoped ContDiff RealInnerProductSpace
noncomputable section

lemma centeredSphereChart_frame_function (p : Base) :
    sphereChartDerivative p = fderiv ℝ
      (stereoInvFunAux (-(p : AmbientBase)) ∘ (centeredSphereIsometry p)) := by
  funext y
  rw [sphereChartDerivative_eq_fderiv p (by rw [centeredSphereChart_target]; trivial),
    centeredSphereChart_inverse]

lemma centeredSphereChart_second (p : Base) (v w : BaseModel) :
    fderiv ℝ (sphereChartDerivative p) 0 w v = -⟪w,v⟫ • (p : AmbientBase) := by
  rw [centeredSphereChart_frame_function]
  have h := (centeredSphereIsometry p).toContinuousLinearMap.iteratedFDeriv_comp_right
    (contDiff_stereoInvFunAux (v := -(p : AmbientBase)) (m := ∞)) (0:BaseModel)
    (i := 2) (show (2:WithTop ℕ∞) ≤ ∞ from WithTop.coe_le_coe.mpr le_top)
  have he := congrArg (fun D : ContinuousMultilinearMap ℝ (fun _ : Fin 2 ↦ BaseModel) AmbientBase ↦
    D ![w,v]) h
  simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply,iteratedFDeriv_two_apply,
    Matrix.cons_val_zero,Matrix.cons_val_one,map_zero] at he
  calc
    _ = fderiv ℝ (fderiv ℝ (stereoInvFunAux (-(p : AmbientBase)))) 0
        (centeredSphereIsometry p w) (centeredSphereIsometry p v) := he
    _ = _ := by
      rw [stereoInvFunAux_second_fderiv,(centeredSphereIsometry p).inner_map_map]
      simp

attribute [local instance] OAI.Yau.Target.instContinuousSMulRealAmbientBase
lemma centeredSphereChart_direction_hasFDerivAt (p : Base) (v : BaseModel) :
    HasFDerivAt (fun y ↦ sphereChartDerivative p y v)
      ((-(innerSL ℝ v)).smulRight (p : AmbientBase)) 0 := by
  have hd := (sphereChartDerivative_smooth_at p
    (y := 0) (by rw [centeredSphereChart_target]; trivial)).differentiableAt (by simp)
  have h := hd.hasFDerivAt.clm_apply (hasFDerivAt_const v (0:BaseModel))
  convert! h using 1
  all_goals try with_reducible_and_instances rfl
  ext w
  simp [centeredSphereChart_second,real_inner_comm]

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Charts_CenteredSphereMetricLemmas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Yau.Target

open Manifold Matrix
open scoped ContDiff RealInnerProductSpace

open Manifold Filter
open scoped Topology

lemma sphere_restriction_chart_second_local (f : AmbientBase → ℝ) (p : Base) (hf : ContDiffAt ℝ ∞ f (p : AmbientBase)) (v w : BaseModel) :
    fderiv ℝ (fderiv ℝ ((fun x : Base ↦ f x) ∘ (extChartAt (𝓡 4) p).symm)) 0 v w =
      fderiv ℝ (fderiv ℝ f) (p : AmbientBase)
        (centeredSphereIsometry p v) (centeredSphereIsometry p w) -
      ⟪v,w⟫ * fderiv ℝ f (p : AmbientBase) (p : AmbientBase) := by
  let : ContinuousSMul ℝ BaseModel := IsBoundedSMul.continuousSMul
  let F : BaseModel → AmbientBase := (Subtype.val : Base → AmbientBase) ∘ (extChartAt (𝓡 4) p).symm
  have hFs : ContDiff ℝ ∞ F := by
    rw [show F = stereoInvFunAux (-(p : AmbientBase)) ∘ (centeredSphereIsometry p) from
      centeredSphereChart_inverse p]
    exact contDiff_stereoInvFunAux.comp (centeredSphereIsometry p).contDiff
  have hF0 : F 0 = (p : AmbientBase) := by exact congrArg (Subtype.val : Base → AmbientBase) (centeredSphereChart_inverse_zero p)
  have hFd (y : BaseModel) : fderiv ℝ F y = sphereChartDerivative p y :=
    (sphereChartDerivative_eq_fderiv p (by rw [centeredSphereChart_target]; trivial)).symm
  have hf0 : ContDiffAt ℝ ∞ f (F 0) := hF0.symm ▸ hf
  have hdf := (hf0.fderiv_right (show (∞ : WithTop ℕ∞)+1 ≤ ∞ by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  have hdF : HasFDerivAt F (centeredSphereIsometry p).toContinuousLinearMap 0 := by
    convert! (hFs.differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) 0).hasFDerivAt using 1
    all_goals try with_reducible_and_instances rfl
    rw [hFd,centeredSphereChart_derivative]
  have hG := hdf.hasFDerivAt.comp 0 hdF
  have h := hG.clm_apply (centeredSphereChart_direction_hasFDerivAt p w)
  have he : (fun y ↦ fderiv ℝ (f ∘ F) y w) =ᶠ[𝓝 0]
      (fun y ↦ fderiv ℝ f (F y) (sphereChartDerivative p y w)) := by
    have hnear := ((hf0.of_le (show (1 : WithTop ℕ∞) ≤ ∞ by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).eventually (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).filter_mono
      (hFs.continuous.continuousAt.tendsto)
    filter_upwards [hnear] with y hy
    change ContDiffAt ℝ 1 f (F y) at hy
    rw [fderiv_comp y (hy.differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)) (hFs.differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) _),hFd]
    rfl
  have hQ := ((hf0.comp 0 hFs.contDiffAt).fderiv_right (show (∞ : WithTop ℕ∞)+1 ≤ ∞ by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  have hE := congrArg (fun L : BaseModel →L[ℝ] ℝ ↦ L v)
    (hQ.hasFDerivAt.clm_apply (hasFDerivAt_const w (0:BaseModel))).fderiv
  simp only [ContinuousLinearMap.comp_zero,zero_add,ContinuousLinearMap.flip_apply] at hE
  change fderiv ℝ (fderiv ℝ (f ∘ F)) 0 v w = _
  change HasFDerivAt (fun y ↦ fderiv ℝ f (F y) (sphereChartDerivative p y w)) _ 0 at h
  rw [← hE,he.fderiv_eq,h.fderiv]
  simp [hF0,centeredSphereChart_derivative,real_inner_comm,sub_eq_add_neg,add_comm]

open Manifold

end Yau.Target

end

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Charts_ChartHessianLemmas
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Yau.Geometry

attribute [local instance] clmTopology clmAdd clmModule
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma christoffelCovector_apply (D : E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) (u v w : E) :
    christoffelCovector D u v w = (D u v w + D v u w - D w u v)/2 := by
  simp [christoffelCovector, ContinuousLinearMap.flip_apply]
  ring

end Yau.Geometry

end

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Charts_LocalMetricJets
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open scoped ContDiff
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma localMetricGradient_eq_of_pair [FiniteDimensional ℝ E] (g : E → E →L[ℝ] E →L[ℝ] ℝ)
    (f : E → ℝ) (x p : E) (hp : ∀ v, v ≠ 0 → 0 < g x v v)
    (he : ∀ v, g x p v = fderiv ℝ f x v) : localMetricGradient g f x = p := by
  have hmap : g x p = fderiv ℝ f x := by ext v; exact he v
  unfold localMetricGradient
  have hi : ContinuousLinearMap.inverse (g x) =
      (positiveMetricEquiv (g x) hp).symm.toContinuousLinearMap :=
    ContinuousLinearMap.inverse_equiv (positiveMetricEquiv (g x) hp)
  rw [← hmap,hi]
  exact (positiveMetricEquiv (g x) hp).symm_apply_apply p

lemma localMetricHessian_of_connection_zero (g : E → E →L[ℝ] E →L[ℝ] ℝ)
    (f : E → ℝ) (x : E) (h : metricConnection (g x) (fderiv ℝ g x) = 0) :
    localMetricHessian g f x = fderiv ℝ (fderiv ℝ f) x := by
  simp [localMetricHessian,h]

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Charts_LocalMetricJetContinuityLemmas
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Yau.Geometry

section

open scoped ContDiff
attribute [local instance] clmTopology clmAdd clmModule
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E]

lemma metric_inverse_continuousAt {T : Type*} [TopologicalSpace T]
    (g : T → E →L[ℝ] E →L[ℝ] ℝ) (x : T) (hg : ContinuousAt g x)
    (hp : ∀ v, v ≠ 0 → 0 < g x v v) :
    ContinuousAt (fun y ↦ ContinuousLinearMap.inverse (g y)) x := by
  have hc := (contDiffAt_map_inverse (n := (1:ℕ∞ω)) (positiveMetricEquiv (g x) hp)).continuousAt
  have hc' : ContinuousAt
      (ContinuousLinearMap.inverse : (E →L[ℝ] E →L[ℝ] ℝ) → ((E →L[ℝ] ℝ) →L[ℝ] E)) (g x) := by
    convert hc using 1
    all_goals try with_reducible_and_instances rfl
    rfl
  exact hc'.comp hg

lemma metric_connection_continuousAt {T : Type*} [TopologicalSpace T]
    (g : T → E →L[ℝ] E →L[ℝ] ℝ) (D : T → E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ)
    (x : T) (hg : ContinuousAt g x) (hD : ContinuousAt D x)
    (hp : ∀ v, v ≠ 0 → 0 < g x v v) :
    ContinuousAt (fun y ↦ metricConnection (g y) (D y)) x := by
  have hflip : ContinuousAt (fun t ↦ (D t).flip) x :=
    (ContinuousLinearMap.flipₗᵢ ℝ E E (E →L[ℝ] ℝ)).continuous.continuousAt.comp hD
  have hcov : ContinuousAt (fun t ↦ christoffelCovector (D t)) x :=
    ((hD.add hflip).sub
      ((continuousAt_const (y := (ContinuousLinearMap.flipₗᵢ ℝ E E ℝ).toContinuousLinearEquiv.toContinuousLinearMap)).clm_comp hflip)).const_smul (1/2:ℝ)
  exact ((ContinuousLinearMap.compL ℝ E (E →L[ℝ] ℝ) E).continuous.continuousAt.comp
    (metric_inverse_continuousAt g x hg hp)).clm_comp hcov

lemma localMetricGradient_continuousAt (g : E → E →L[ℝ] E →L[ℝ] ℝ)
    (f : E → ℝ) (x : E) (hg : ContinuousAt g x) (hf : ContDiffAt ℝ ∞ f x)
    (hp : ∀ v, v ≠ 0 → 0 < g x v v) : ContinuousAt (localMetricGradient g f) x :=
  (metric_inverse_continuousAt g x hg hp).clm_apply (hf.continuousAt_fderiv (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top))

lemma localMetricHessian_continuousAt (g : E → E →L[ℝ] E →L[ℝ] ℝ)
    (f : E → ℝ) (x : E) (hg : ContDiffAt ℝ ∞ g x) (hf : ContDiffAt ℝ ∞ f x)
    (hp : ∀ v, v ≠ 0 → 0 < g x v v) : ContinuousAt (localMetricHessian g f) x := by
  have hD := hf.continuousAt_fderiv (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  exact ((hf.fderiv_right (m := ∞) (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).continuousAt_fderiv (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).sub
    (((ContinuousLinearMap.compL ℝ E E ℝ).continuous.continuousAt.comp hD).clm_comp
      (metric_connection_continuousAt g (fderiv ℝ g) x hg.continuousAt
        (hg.continuousAt_fderiv (by simp)) hp))

end

open scoped ContDiff
attribute [local instance] clmTopology clmAdd clmModule

end Yau.Geometry

end

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Charts_MetricFrameOps
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
noncomputable section
attribute [local instance] clmTopology clmAdd clmModule
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma metricNormalize_unit (g : E →L[ℝ] E →L[ℝ] ℝ) (v : E) (hv : 0 < g v v) :
    g (metricNormalize g v) (metricNormalize g v) = 1 := by
  have hr : Real.sqrt (g v v) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hv)
  have hh := Real.sq_sqrt hv.le
  simp only [metricNormalize, map_smul, smul_apply, smul_eq_mul]
  field_simp
  nlinarith

lemma metricNormalize_fixed (g : E →L[ℝ] E →L[ℝ] ℝ) (v : E) (hv : g v v = 1) :
    metricNormalize g v = v := by simp [metricNormalize, hv]

lemma metricNormalize_orthogonal (g : E →L[ℝ] E →L[ℝ] ℝ) (u v : E) (huv : g u v = 0) :
    g u (metricNormalize g v) = 0 := by simp [metricNormalize, huv]

variable {ι : Type*} [Fintype ι]

variable {T : Type*} [TopologicalSpace T]
lemma metricNormalize_continuousAt (g : T → E →L[ℝ] E →L[ℝ] ℝ) (v : T → E) {t : T}
    (hg : ContinuousAt g t) (hv : ContinuousAt v t) (hpos : 0 < g t (v t) (v t)) :
    ContinuousAt (fun s ↦ metricNormalize (g s) (v s)) t := by
  exact (((hg.clm_apply hv).clm_apply hv).sqrt.inv₀
    (ne_of_gt (Real.sqrt_pos.mpr hpos))).smul hv

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Persistence_LocalAdmissibilityPersistence
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Filter
open scoped Topology
noncomputable section
variable {E T : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace T]

lemma admissibility_eventually (g H : T → E →L[ℝ] E →L[ℝ] ℝ) (p : T → E) (x : T)
    (hg : ContinuousAt g x) (hH : ContinuousAt H x) (hp : ContinuousAt p x)
    (hpp : 0 < g x (p x) (p x)) (t : E) (hpt : g x (p x) t = 0)
    (htt : g x t t = 1)
    (hstrict : 0 < H x (p x) (p x) + (g x (p x) (p x)+4)*H x t t) :
    ∀ᶠ y in 𝓝 x, p y ≠ 0 ∧ ∃ u : E, g y (p y) u = 0 ∧ g y u u = 1 ∧
      0 < H y (p y) (p y) + (g y (p y) (p y)+4)*H y u u := by
  let a : T → ℝ := fun y ↦ g y (p y) (p y)
  have ha : ContinuousAt a x := (hg.clm_apply hp).clm_apply hp
  let z : T → E := fun y ↦ t - (g y (p y) t / a y) • p y
  have hz : ContinuousAt z x := continuousAt_const.sub
    ((((hg.clm_apply hp).clm_apply continuousAt_const).div ha hpp.ne').smul hp)
  have hz0 : z x = t := by simp [z,hpt]
  have hzz : 0 < g x (z x) (z x) := by rw [hz0,htt]; norm_num
  let u : T → E := fun y ↦ metricNormalize (g y) (z y)
  have hu : ContinuousAt u x := metricNormalize_continuousAt g z hg hz hzz
  have hu0 : u x = t := by dsimp [u]; rw [hz0]; exact metricNormalize_fixed _ _ htt
  have hs : ContinuousAt (fun y ↦ H y (p y) (p y) + (a y+4)*H y (u y) (u y)) x :=
    ((hH.clm_apply hp).clm_apply hp).add
      ((ha.add continuousAt_const).mul ((hH.clm_apply hu).clm_apply hu))
  have hsa : ∀ᶠ y in 𝓝 x, 0 < H y (p y) (p y) + (a y+4)*H y (u y) (u y) :=
    hs.preimage_mem_nhds (Ioi_mem_nhds (by simpa [hu0,a] using hstrict))
  have haa : ∀ᶠ y in 𝓝 x, 0 < a y := ha.preimage_mem_nhds (Ioi_mem_nhds hpp)
  have hza : ∀ᶠ y in 𝓝 x, 0 < g y (z y) (z y) :=
    ((hg.clm_apply hz).clm_apply hz).preimage_mem_nhds (Ioi_mem_nhds hzz)
  filter_upwards [haa,hza,hsa] with y hy hyz hys
  have hp0 : p y ≠ 0 := by intro he; simp [a,he] at hy
  refine ⟨hp0,u y,?_,metricNormalize_unit _ _ hyz,hys⟩
  apply metricNormalize_orthogonal
  change g y (p y) (t - (g y (p y) t / a y) • p y) = 0
  simp only [map_sub,map_smul,smul_eq_mul]
  change g y (p y) t - (g y (p y) t / a y) * a y = 0
  rw [div_mul_cancel₀ _ hy.ne',sub_self]

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Charts_MetricJetAdmissibility
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Filter
open scoped ContDiff Topology
noncomputable section
attribute [local instance] clmTopology clmAdd clmModule
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E]

lemma jetGradient_continuousAt (f : E → ℝ) (j : MetricJet E) (x : E)
    (hf : ContDiffAt ℝ ∞ f x) (hp : ∀ v, v ≠ 0 → 0 < j.1 v v) :
    ContinuousAt (fun z : MetricJet E × E ↦ jetGradient f z.1 z.2) (j,x) := by
  exact (metric_inverse_continuousAt (fun z : MetricJet E × E ↦ z.1.1) (j,x)
    (continuousAt_fst.fst) hp).clm_apply
      ((hf.continuousAt_fderiv (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).comp continuousAt_snd)

lemma jetHessian_continuousAt (f : E → ℝ) (j : MetricJet E) (x : E)
    (hf : ContDiffAt ℝ ∞ f x) (hp : ∀ v, v ≠ 0 → 0 < j.1 v v) :
    ContinuousAt (fun z : MetricJet E × E ↦ jetHessian f z.1 z.2) (j,x) := by
  have hD := (hf.continuousAt_fderiv (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).comp (continuousAt_snd (p := (j,x)))
  exact (((hf.fderiv_right (m := ∞) (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).continuousAt_fderiv (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).comp
    continuousAt_snd).sub
    (((ContinuousLinearMap.compL ℝ E E ℝ).continuous.continuousAt.comp hD).clm_comp
      (metric_connection_continuousAt (fun z : MetricJet E × E ↦ z.1.1)
        (fun z ↦ z.1.2) (j,x) continuousAt_fst.fst continuousAt_fst.snd hp))

theorem jetAdmissible_eventually (f : E → ℝ) (j : MetricJet E) (x : E)
    (hf : ContDiffAt ℝ ∞ f x) (hp : ∀ v, v ≠ 0 → 0 < j.1 v v)
    (ha : JetAdmissible f j x) :
    ∀ᶠ z : MetricJet E × E in 𝓝 (j,x), JetAdmissible f z.1 z.2 := by
  obtain ⟨hp0,t,hpt,htt,hs⟩ := ha
  exact admissibility_eventually (fun z : MetricJet E × E ↦ z.1.1)
    (fun z ↦ jetHessian f z.1 z.2) (fun z ↦ jetGradient f z.1 z.2) (j,x)
    continuousAt_fst.fst (jetHessian_continuousAt f j x hf hp)
    (jetGradient_continuousAt f j x hf hp) (hp _ hp0) t hpt htt hs

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
lemma jetAdmissible_actual (g : E → E →L[ℝ] E →L[ℝ] ℝ) (f : E → ℝ) (x : E) :
    JetAdmissible f (g x,fderiv ℝ g x) x ↔
      localMetricGradient g f x ≠ 0 ∧ ∃ t : E,
        g x (localMetricGradient g f x) t = 0 ∧ g x t t = 1 ∧
        0 < localMetricHessian g f x (localMetricGradient g f x) (localMetricGradient g f x) +
          (g x (localMetricGradient g f x) (localMetricGradient g f x)+4)*
            localMetricHessian g f x t t := Iff.rfl

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Charts_RoundChartConnection
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Manifold Yau.Geometry
open scoped ContDiff RealInnerProductSpace
noncomputable section
local instance instFactAmbientBaseFinrankQ237 : Fact (Module.finrank ℝ AmbientBase = 4+1) := ⟨by simp [AmbientBase]⟩

lemma roundChartMetric_center (p : Base) :
    roundChartMetric p 0 = innerSL ℝ (E := BaseModel) := by
  ext u v
  rw [roundChartMetric_apply,centeredSphereChart_derivative]
  exact (centeredSphereIsometry p).inner_map_map u v

lemma roundChartMetric_smooth (p : Base) : ContDiff ℝ ∞ (roundChartMetric p) := by
  apply contDiff_iff_contDiffAt.mpr
  intro y
  have h := sphereChartDerivative_smooth_at p (y := y) (by rw [centeredSphereChart_target]; trivial)
  have hpre : ContMDiffAt 𝓘(ℝ,BaseModel)
      𝓘(ℝ,(AmbientBase →L[ℝ] ℝ) →L[ℝ] (BaseModel →L[ℝ] ℝ)) ∞
      (fun z ↦ (sphereChartDerivative p z).precomp ℝ) y := h.contMDiffAt.clm_precomp
  have hpost : ContMDiffAt 𝓘(ℝ,BaseModel) 𝓘(ℝ,BaseModel →L[ℝ] AmbientBase →L[ℝ] ℝ) ∞
      (fun z ↦ ambientRoundBilinear.comp (sphereChartDerivative p z)) y :=
    contMDiffAt_const.clm_comp h.contMDiffAt
  exact contMDiffAt_iff_contDiffAt.mp (hpre.clm_comp hpost)

lemma roundChartMetric_derivative_zero (p : Base) : fderiv ℝ (roundChartMetric p) 0 = 0 := by
  let : ContinuousSMul ℝ BaseModel := IsBoundedSMul.continuousSMul
  ext w u v
  have hg := ((roundChartMetric_smooth p).differentiable (by simp) 0).hasFDerivAt
  have he := (hg.clm_apply (hasFDerivAt_const u (0 : BaseModel))).clm_apply
    (hasFDerivAt_const v (0 : BaseModel))
  have hi := (centeredSphereChart_direction_hasFDerivAt p u).inner ℝ
    (centeredSphereChart_direction_hasFDerivAt p v)
  have hh := congrArg (fun L : BaseModel →L[ℝ] ℝ ↦ L w) (he.fderiv.symm.trans hi.fderiv)
  simpa [centeredSphereChart_derivative,centeredSphereIsometry_orthogonal,
    real_inner_comm,inner_smul_left,inner_smul_right] using hh

lemma roundChartMetric_connection_zero (p : Base) :
    metricConnection (roundChartMetric p 0) (fderiv ℝ (roundChartMetric p) 0) = 0 := by
  rw [roundChartMetric_derivative_zero]
  have hz : christoffelCovector (0 : BaseModel →L[ℝ] BaseModel →L[ℝ] BaseModel →L[ℝ] ℝ) = 0 := by
    ext u v w
    rw [christoffelCovector_apply]
    simp
  simp only [metricConnection,hz,ContinuousLinearMap.comp_zero]

lemma centeredSphereIsometry_exists (p : Base) (v : AmbientBase)
    (hv : ⟪(p : AmbientBase),v⟫ = (0:ℝ)) :
    ∃ w : BaseModel, centeredSphereIsometry p w = v := by
  have hm : v ∈ (ℝ ∙ ((-p : Base) : AmbientBase))ᗮ := by
    apply (Submodule.mem_orthogonal_singleton_iff_inner_left (𝕜 := ℝ)).mpr
    simpa [real_inner_comm] using hv
  refine ⟨(OrthonormalBasis.fromOrthogonalSpanSingleton 4
    (ne_zero_of_mem_unit_sphere (-p))).repr ⟨v,hm⟩,?_⟩
  exact congrArg (fun w : (ℝ ∙ ((-p : Base) : AmbientBase))ᗮ ↦ (w : AmbientBase))
    ((OrthonormalBasis.fromOrthogonalSpanSingleton 4
      (ne_zero_of_mem_unit_sphere (-p))).repr.symm_apply_apply ⟨v,hm⟩)

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_SphericalSeed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Manifold
open scoped ContDiff
noncomputable section

local instance instFactEqNatFinrankRealSeedAmbientHAddOfNat_ra03e94_1 : Fact (Module.finrank ℝ SeedAmbient = 4+1) := ⟨by simp [SeedAmbient]⟩
lemma seedZ1_apply (x : SeedAmbient) : seedZ1 x = (x 0 : ℂ) + Complex.I * (x 1 : ℂ) := rfl
lemma seedZ2_apply (x : SeedAmbient) : seedZ2 x = (x 2 : ℂ) + Complex.I * (x 3 : ℂ) := rfl

lemma seedQuadratic_contDiff : ContDiff ℝ ∞ seedQuadratic :=
  seedZ1.contDiff.mul seedZ2.contDiff

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_SeedConcretePoint
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Manifold
open scoped ContDiff RealInnerProductSpace
noncomputable section

lemma seedPoint_z1 : seedZ1 (seedPoint : SeedAmbient) = (1/3:ℂ) := by
  norm_num [seedPoint,seedPointVector,seedZ1_apply]

lemma seedPoint_z2 : seedZ2 (seedPoint : SeedAmbient) = (2/3:ℂ) := by
  rw [seedZ2_apply]
  change ((2/3:ℝ):ℂ) + Complex.I * (0:ℂ) = 2/3
  norm_num

lemma seedPoint_quadratic : seedQuadratic (seedPoint : SeedAmbient) = (2/9:ℂ) := by
  rw [seedQuadratic,seedPoint_z1,seedPoint_z2]; norm_num

lemma seedPoint_slitPlane : seedQuadratic (seedPoint : SeedAmbient) ∈ Complex.slitPlane := by
  rw [seedPoint_quadratic,Complex.mem_slitPlane_iff]
  left; norm_num

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_SeedPolynomialDerivatives
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open scoped ContDiff
noncomputable section

lemma seedQuadratic_hasFDerivAt (x : SeedAmbient) :
    HasFDerivAt seedQuadratic (seedQuadraticDerivative x) x :=
  (seedZ1.hasFDerivAt).mul (seedZ2.hasFDerivAt)

lemma seedQuadraticDerivative_apply_hasFDerivAt (x v : SeedAmbient) :
    HasFDerivAt (fun y ↦ seedQuadraticDerivative y v)
      (seedZ2 v • seedZ1 + seedZ1 v • seedZ2) x := by
  convert! (seedZ1.hasFDerivAt.mul_const (seedZ2 v)).add
    (seedZ2.hasFDerivAt.mul_const (seedZ1 v)) using 1
  all_goals try with_reducible_and_instances rfl

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_SeedLogarithmicBranch
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Manifold Set
open scoped ContDiff
noncomputable section

local instance instFactEqNatFinrankRealSeedAmbientHAddOfNat_1_ra03e94_1 : Fact (Module.finrank ℝ SeedAmbient = 4+1) := ⟨by simp [SeedAmbient]⟩
lemma seedLogDomain_open : IsOpen seedLogDomain :=
  Complex.isOpen_slitPlane.preimage seedQuadratic_contDiff.continuous

lemma seedPoint_mem_logDomain : (seedPoint : SeedAmbient) ∈ seedLogDomain := seedPoint_slitPlane

lemma seedLog_contDiffAt {x : SeedAmbient} (hx : x ∈ seedLogDomain) :
    ContDiffAt ℝ ∞ seedLog x :=
  ((Complex.contDiffAt_log hx (n := ∞)).restrict_scalars ℝ).comp x seedQuadratic_contDiff.contDiffAt

lemma seedLog_hasFDerivAt {x : SeedAmbient} (hx : x ∈ seedLogDomain) :
    HasFDerivAt seedLog ((seedQuadratic x)⁻¹ • seedQuadraticDerivative x) x := by
  convert! ((Complex.hasStrictFDerivAt_log_real hx).hasFDerivAt).comp x
    (seedQuadratic_hasFDerivAt x) using 1
  all_goals try with_reducible_and_instances rfl

lemma seedLog_fderiv {x : SeedAmbient} (hx : x ∈ seedLogDomain) (v : SeedAmbient) :
    fderiv ℝ seedLog x v = (seedQuadraticDerivative x v) / seedQuadratic x := by
  rw [(seedLog_hasFDerivAt hx).fderiv]
  simp [div_eq_mul_inv,mul_comm]

lemma seedLogReal_hasFDerivAt {x : SeedAmbient} (hx : x ∈ seedLogDomain) :
    HasFDerivAt seedLogReal
      (Complex.reCLM.comp ((seedQuadratic x)⁻¹ • seedQuadraticDerivative x)) x :=
  Complex.reCLM.hasFDerivAt.comp x (seedLog_hasFDerivAt hx)

lemma seedLogImag_hasFDerivAt {x : SeedAmbient} (hx : x ∈ seedLogDomain) :
    HasFDerivAt seedLogImag
      (Complex.imCLM.comp ((seedQuadratic x)⁻¹ • seedQuadraticDerivative x)) x :=
  Complex.imCLM.hasFDerivAt.comp x (seedLog_hasFDerivAt hx)

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_SeedLogNonvanishing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Manifold Set
open scoped ContDiff RealInnerProductSpace
noncomputable section

local instance instFactEqNatFinrankRealSeedAmbientHAddOfNat_2_ra03e94_1 : Fact (Module.finrank ℝ SeedAmbient = 4+1) := ⟨by simp [SeedAmbient]⟩
lemma seedImagTest_tangent : ⟪(seedPoint : SeedAmbient),seedImagTestVector⟫ = (0:ℝ) := by
  rw [PiLp.inner_apply]
  first | (simp [seedPoint,seedPointVector,seedImagTestVector,Fin.sum_univ_succ,Matrix.cons_val_succ]; all_goals first | (norm_num [seedPoint,seedPointVector,seedImagTestVector,Fin.sum_univ_succ,Matrix.cons_val_succ]; done) | rfl | decide) | (norm_num [seedPoint,seedPointVector,seedImagTestVector,Fin.sum_univ_succ,Matrix.cons_val_succ]; done) | norm_num [seedPoint,seedPointVector,seedImagTestVector,Fin.sum_univ_succ,Matrix.cons_val_succ]

lemma seedLog_imag_test : fderiv ℝ seedLogImag (seedPoint : SeedAmbient) seedImagTestVector = 3 := by
  rw [(seedLogImag_hasFDerivAt seedPoint_mem_logDomain).fderiv]
  simp only [ContinuousLinearMap.comp_apply,smul_apply,smul_eq_mul,seedPoint_quadratic,
    seedQuadraticDerivative,add_apply,seedPoint_z1,seedPoint_z2]
  have h1 : seedZ1 seedImagTestVector = Complex.I := by
    rw [seedZ1_apply]; change (0:ℂ) + Complex.I*1 = Complex.I; ring
  have h2 : seedZ2 seedImagTestVector = 0 := by
    rw [seedZ2_apply]; change (0:ℂ) + Complex.I*0 = 0; ring
  rw [h1,h2]
  norm_num

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_SeedLogSecondDerivative
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Filter
open scoped ContDiff Topology
noncomputable section

lemma seedLog_direction_hasFDerivAt {x : SeedAmbient} (hx : x ∈ seedLogDomain)
    (v : SeedAmbient) :
    HasFDerivAt (fun y ↦ fderiv ℝ seedLog y v)
      ((seedQuadratic x)⁻¹ • (seedZ2 v • seedZ1 + seedZ1 v • seedZ2) -
        (seedQuadraticDerivative x v / seedQuadratic x ^ 2) • seedQuadraticDerivative x) x := by
  have he : (fun y ↦ fderiv ℝ seedLog y v) =ᶠ[𝓝 x]
      (fun y ↦ seedQuadraticDerivative y v / seedQuadratic y) := by
    filter_upwards [seedLogDomain_open.mem_nhds hx] with y hy
    exact seedLog_fderiv hy v
  have hi := (hasFDerivAt_inv' (𝕜 := ℝ) (Complex.slitPlane_ne_zero hx)).comp x
    (seedQuadratic_hasFDerivAt x)
  have hd := (seedQuadraticDerivative_apply_hasFDerivAt x v).mul hi
  have he' : (fun y ↦ fderiv ℝ seedLog y v) =ᶠ[𝓝 x]
      (fun y ↦ seedQuadraticDerivative y v * (seedQuadratic y)⁻¹) := by
    simpa only [div_eq_mul_inv] using he
  convert! hd.congr_of_eventuallyEq he' using 1
  all_goals try with_reducible_and_instances rfl
  ext w
  simp [ContinuousLinearMap.mulLeftRight_apply,div_eq_mul_inv,pow_two]
  ring

lemma seedLogReal_second {x : SeedAmbient} (hx : x ∈ seedLogDomain) (v w : SeedAmbient) :
    fderiv ℝ (fderiv ℝ seedLogReal) x w v =
      ((seedZ2 v * seedZ1 w + seedZ1 v * seedZ2 w) / seedQuadratic x -
      seedQuadraticDerivative x v * seedQuadraticDerivative x w / seedQuadratic x ^ 2).re := by
  have he : (fun y ↦ fderiv ℝ seedLogReal y v) =ᶠ[𝓝 x]
      (fun y ↦ (fderiv ℝ seedLog y v).re) := by
    filter_upwards [seedLogDomain_open.mem_nhds hx] with y hy
    rw [(seedLogReal_hasFDerivAt hy).fderiv,(seedLog_hasFDerivAt hy).fderiv]
    rfl
  have hs : ContDiffAt ℝ ∞ seedLogReal x :=
    Complex.reCLM.contDiff.contDiffAt.comp x (seedLog_contDiffAt hx)
  have hd := ((hs.fderiv_right (m := ∞) (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).hasFDerivAt.clm_apply
    (hasFDerivAt_const v x)
  have hr := Complex.reCLM.hasFDerivAt.comp x (seedLog_direction_hasFDerivAt hx v)
  have hh := congrArg (fun L : SeedAmbient →L[ℝ] ℝ ↦ L w)
    (hd.fderiv.symm.trans (he.fderiv_eq.trans hr.fderiv))
  simpa [div_eq_mul_inv,mul_comm,mul_left_comm,mul_assoc,mul_add] using hh

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_SeedLogConcreteJets
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open scoped ContDiff RealInnerProductSpace
noncomputable section

lemma seedLogReal_first_at_point (v : SeedAmbient) :
    fderiv ℝ seedLogReal (seedPoint : SeedAmbient) v = 3*v 0 + (3/2)*v 2 := by
  rw [(seedLogReal_hasFDerivAt seedPoint_mem_logDomain).fderiv]
  simp only [ContinuousLinearMap.comp_apply,smul_apply,
    smul_eq_mul,seedPoint_quadratic,seedQuadraticDerivative,add_apply,
    seedPoint_z1,seedPoint_z2]
  norm_num [seedZ1_apply,seedZ2_apply,div_eq_mul_inv,Complex.mul_re,Complex.mul_im]
  simp
  ring

lemma seedLogReal_second_at_point (v w : SeedAmbient) :
    fderiv ℝ (fderiv ℝ seedLogReal) (seedPoint : SeedAmbient) w v =
      -9*v 0*w 0 + 9*v 1*w 1 - (9/4)*v 2*w 2 + (9/4)*v 3*w 3 := by
  rw [seedLogReal_second seedPoint_mem_logDomain]
  simp only [smul_apply,
    smul_eq_mul,seedPoint_quadratic,seedQuadraticDerivative,add_apply,
    seedPoint_z1,seedPoint_z2]
  norm_num [seedZ1_apply,seedZ2_apply,div_eq_mul_inv,Complex.mul_re,Complex.mul_im]
  simp
  ring

lemma seedRealGradient_tangent : ⟪(seedPoint : SeedAmbient),seedRealGradient⟫ = (0:ℝ) := by
  rw [PiLp.inner_apply]
  first | (simp [seedPoint,seedPointVector,seedRealGradient,Fin.sum_univ_succ,Matrix.cons_val_succ]; all_goals first | (norm_num [seedPoint,seedPointVector,seedRealGradient,Fin.sum_univ_succ,Matrix.cons_val_succ]; done) | rfl | decide) | (norm_num [seedPoint,seedPointVector,seedRealGradient,Fin.sum_univ_succ,Matrix.cons_val_succ]; done) | norm_num [seedPoint,seedPointVector,seedRealGradient,Fin.sum_univ_succ,Matrix.cons_val_succ]

lemma seedRealGradient_pair (v : SeedAmbient)
    (hv : ⟪(seedPoint : SeedAmbient),v⟫ = (0:ℝ)) :
    ⟪seedRealGradient,v⟫ = fderiv ℝ seedLogReal (seedPoint : SeedAmbient) v := by
  rw [seedLogReal_first_at_point,PiLp.inner_apply]
  rw [PiLp.inner_apply] at hv
  simp [seedPoint,seedPointVector,Fin.sum_univ_succ,Matrix.cons_val_succ] at hv
  simp [seedRealGradient,Fin.sum_univ_succ,Matrix.cons_val_succ]
  linarith

lemma seedGradient_geometry :
    ⟪seedRealGradient,seedRealGradient⟫ = (29/4:ℝ) ∧
    ⟪seedImagGradient,seedImagGradient⟫ = (45/4:ℝ) ∧
    ⟪seedRealGradient,seedImagGradient⟫ = (0:ℝ) ∧
    ⟪seedRealGradient,seedImagTestVector⟫ = (0:ℝ) ∧
    ⟪seedImagTestVector,seedImagTestVector⟫ = (1:ℝ) := by
  simp only [PiLp.inner_apply]
  first | (simp [seedRealGradient,seedImagGradient,seedImagTestVector, Fin.sum_univ_succ,Matrix.cons_val_succ]; all_goals first | (norm_num [seedRealGradient,seedImagGradient,seedImagTestVector, Fin.sum_univ_succ,Matrix.cons_val_succ]; done) | rfl | decide) | (norm_num [seedRealGradient,seedImagGradient,seedImagTestVector, Fin.sum_univ_succ,Matrix.cons_val_succ]; done) | norm_num [seedRealGradient,seedImagGradient,seedImagTestVector, Fin.sum_univ_succ,Matrix.cons_val_succ]

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_SeedRoundAdmissibility
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Manifold Yau.Geometry
open scoped ContDiff RealInnerProductSpace
noncomputable section

lemma seed_chart_first (f : SeedAmbient → ℝ)
    (hf : DifferentiableAt ℝ f (seedPoint : SeedAmbient)) (v : BaseModel) :
    fderiv ℝ ((fun x : Base ↦ f x) ∘ (extChartAt (𝓡 4) seedPoint).symm) 0 v =
      fderiv ℝ f (seedPoint : SeedAmbient) (centeredSphereIsometry seedPoint v) := by
  let F : BaseModel → SeedAmbient := (Subtype.val : Base → SeedAmbient) ∘
    (extChartAt (𝓡 4) seedPoint).symm
  have hF0 : F 0 = (seedPoint : SeedAmbient) :=
    congrArg (Subtype.val : Base → SeedAmbient) (centeredSphereChart_inverse_zero seedPoint)
  have hd : HasFDerivAt F (centeredSphereIsometry seedPoint).toContinuousLinearMap 0 := by
    rw [show F = stereoInvFunAux (-(seedPoint : SeedAmbient)) ∘ centeredSphereIsometry seedPoint from
      centeredSphereChart_inverse seedPoint]
    have hh : HasFDerivAt (stereoInvFunAux (-(seedPoint : SeedAmbient)))
        (ContinuousLinearMap.id ℝ SeedAmbient) ((centeredSphereIsometry seedPoint).toContinuousLinearMap 0) := by
      simpa using hasFDerivAt_stereoInvFunAux (-(seedPoint : SeedAmbient))
    simpa using hh.comp (0:BaseModel) (centeredSphereIsometry seedPoint).toContinuousLinearMap.hasFDerivAt
  have hh := congrArg (fun L : BaseModel →L[ℝ] ℝ ↦ L v)
    ((hF0.symm ▸ hf).hasFDerivAt.comp 0 hd).fderiv
  change fderiv ℝ (f ∘ F) 0 v = fderiv ℝ f (F 0) (centeredSphereIsometry seedPoint v) at hh
  rw [hF0] at hh
  exact hh

lemma seed_round_hessian (u v : BaseModel) :
    localMetricHessian (roundChartMetric seedPoint) seedRealChart 0 u v =
      fderiv ℝ (fderiv ℝ seedLogReal) (seedPoint : SeedAmbient)
        (centeredSphereIsometry seedPoint u) (centeredSphereIsometry seedPoint v) - 2*⟪u,v⟫ := by
  rw [localMetricHessian_of_connection_zero _ _ _ (roundChartMetric_connection_zero seedPoint)]
  have hf : ContDiffAt ℝ ∞ seedLogReal (seedPoint : SeedAmbient) :=
    Complex.reCLM.contDiff.contDiffAt.comp _ (seedLog_contDiffAt seedPoint_mem_logDomain)
  rw [show seedRealChart = (fun x : Base ↦ seedLogReal x) ∘
    (extChartAt (𝓡 4) seedPoint).symm from rfl,
    sphere_restriction_chart_second_local seedLogReal seedPoint hf,
    seedLogReal_first_at_point]
  norm_num [seedPoint,seedPointVector,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.head_cons,Matrix.tail_cons]
  ring

lemma seed_round_gradient (u : BaseModel)
    (hu : centeredSphereIsometry seedPoint u = seedRealGradient) :
    localMetricGradient (roundChartMetric seedPoint) seedRealChart 0 = u := by
  apply localMetricGradient_eq_of_pair
  · intro v hv
    rw [roundChartMetric_center]
    exact real_inner_self_pos.mpr hv
  · intro v
    rw [roundChartMetric_center]
    change ⟪u,v⟫ = _
    rw [← (centeredSphereIsometry seedPoint).inner_map_map u v,hu]
    exact (seedRealGradient_pair _ (centeredSphereIsometry_orthogonal seedPoint v)).trans
      (seed_chart_first seedLogReal (seedLogReal_hasFDerivAt seedPoint_mem_logDomain).differentiableAt v).symm

theorem seed_round_admissibility :
    let g := roundChartMetric seedPoint
    let p := localMetricGradient g seedRealChart 0
    let H := localMetricHessian g seedRealChart 0
    p ≠ 0 ∧ ∃ t : BaseModel, g 0 p t = 0 ∧ g 0 t t = 1 ∧
      H p p + (g 0 p p + 4)*H t t = 243/16 ∧
      0 < H p p + (g 0 p p + 4)*H t t := by
  obtain ⟨u,hu⟩ := centeredSphereIsometry_exists seedPoint seedRealGradient seedRealGradient_tangent
  obtain ⟨t,ht⟩ := centeredSphereIsometry_exists seedPoint seedImagTestVector seedImagTest_tangent
  dsimp only
  rw [seed_round_gradient u hu]
  have huu : ⟪u,u⟫ = (29/4:ℝ) := by
    rw [← (centeredSphereIsometry seedPoint).inner_map_map u u,hu]
    exact seedGradient_geometry.1
  have hut : ⟪u,t⟫ = (0:ℝ) := by
    rw [← (centeredSphereIsometry seedPoint).inner_map_map u t,hu,ht]
    exact seedGradient_geometry.2.2.2.1
  have htt : ⟪t,t⟫ = (1:ℝ) := by
    rw [← (centeredSphereIsometry seedPoint).inner_map_map t t,ht]
    exact seedGradient_geometry.2.2.2.2
  have hu0 : u ≠ 0 := by intro h; norm_num [h] at huu
  have hHuu : localMetricHessian (roundChartMetric seedPoint) seedRealChart 0 u u = -1017/16 := by
    rw [seed_round_hessian,hu,seedLogReal_second_at_point,huu]
    norm_num [seedRealGradient,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.head_cons,Matrix.tail_cons]
  have hHtt : localMetricHessian (roundChartMetric seedPoint) seedRealChart 0 t t = 7 := by
    rw [seed_round_hessian,ht,seedLogReal_second_at_point,htt]
    norm_num [seedImagTestVector,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.head_cons,Matrix.tail_cons]
  refine ⟨hu0,t,?_,?_,?_,?_⟩
  · rw [roundChartMetric_center]; exact hut
  · rw [roundChartMetric_center]; exact htt
  · rw [roundChartMetric_center,hHuu,hHtt]
    change -1017/16 + (⟪u,u⟫+4)*7 = (243/16:ℝ)
    rw [huu]; norm_num
  · rw [roundChartMetric_center,hHuu,hHtt]
    change (0:ℝ) < -1017/16 + (⟪u,u⟫+4)*7
    rw [huu]; norm_num

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_SeedRoundPatch
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Manifold Yau.Geometry Filter Set Metric
open scoped ContDiff RealInnerProductSpace Topology
noncomputable section

lemma seedChartAmbient_smooth : ContDiff ℝ ∞ seedChartAmbient := by
  rw [show seedChartAmbient = stereoInvFunAux (-(seedPoint : SeedAmbient)) ∘ centeredSphereIsometry seedPoint from
    centeredSphereChart_inverse seedPoint]
  exact contDiff_stereoInvFunAux.comp (centeredSphereIsometry seedPoint).contDiff

lemma seedChartAmbient_zero : seedChartAmbient 0 = (seedPoint : SeedAmbient) :=
  congrArg (Subtype.val : Base → SeedAmbient) (centeredSphereChart_inverse_zero seedPoint)

lemma seedRealChart_smoothAt_zero : ContDiffAt ℝ ∞ seedRealChart 0 := by
  have hf := Complex.reCLM.contDiff.contDiffAt.comp _ (seedLog_contDiffAt seedPoint_mem_logDomain)
  rw [← seedChartAmbient_zero] at hf
  exact hf.comp 0 seedChartAmbient_smooth.contDiffAt

lemma seedImagChart_smoothAt_zero : ContDiffAt ℝ ∞ seedImagChart 0 := by
  have hf := Complex.imCLM.contDiff.contDiffAt.comp _ (seedLog_contDiffAt seedPoint_mem_logDomain)
  rw [← seedChartAmbient_zero] at hf
  exact hf.comp 0 seedChartAmbient_smooth.contDiffAt

lemma seedImagChart_differential_ne_zero : fderiv ℝ seedImagChart 0 ≠ 0 := by
  obtain ⟨t,ht⟩ := centeredSphereIsometry_exists seedPoint seedImagTestVector seedImagTest_tangent
  have h : fderiv ℝ seedImagChart 0 t = 3 := by
    rw [show seedImagChart = (fun x : Base ↦ seedLogImag x) ∘
      (extChartAt (𝓡 4) seedPoint).symm from rfl,
      seed_chart_first seedLogImag (seedLogImag_hasFDerivAt seedPoint_mem_logDomain).differentiableAt,
      ht,seedLog_imag_test]
  intro hz
  simp [hz] at h

lemma seedRoundAdmissible_eventually : ∀ᶠ y in 𝓝 (0 : BaseModel), seedRoundAdmissible y := by
  have hpos (v : BaseModel) (hv : v ≠ 0) : 0 < roundChartMetric seedPoint 0 v v := by
    rw [roundChartMetric_center]; exact real_inner_self_pos.mpr hv
  obtain ⟨hp,t,hpt,htt,_,hs⟩ := seed_round_admissibility
  exact admissibility_eventually (roundChartMetric seedPoint)
    (localMetricHessian (roundChartMetric seedPoint) seedRealChart)
    (localMetricGradient (roundChartMetric seedPoint) seedRealChart) 0
    (roundChartMetric_smooth seedPoint).continuous.continuousAt
    (localMetricHessian_continuousAt _ _ _ (roundChartMetric_smooth seedPoint).contDiffAt
      seedRealChart_smoothAt_zero hpos)
    (localMetricGradient_continuousAt _ _ _ (roundChartMetric_smooth seedPoint).continuous.continuousAt
      seedRealChart_smoothAt_zero hpos)
    (hpos _ hp) t hpt htt hs

theorem seed_round_compact_patch : ∃ r : ℝ, 0 < r ∧ IsCompact (closedBall (0 : BaseModel) r) ∧
    ∀ y ∈ closedBall (0 : BaseModel) r,
      seedChartAmbient y ∈ seedLogDomain ∧ fderiv ℝ seedImagChart y ≠ 0 ∧ seedRoundAdmissible y := by
  have hb : ∀ᶠ y in 𝓝 (0 : BaseModel), seedChartAmbient y ∈ seedLogDomain :=
    seedChartAmbient_smooth.continuous.continuousAt.preimage_mem_nhds
      (seedLogDomain_open.mem_nhds (by rw [seedChartAmbient_zero]; exact seedPoint_mem_logDomain))
  have hd : ∀ᶠ y in 𝓝 (0 : BaseModel), fderiv ℝ seedImagChart y ≠ 0 :=
    (seedImagChart_smoothAt_zero.continuousAt_fderiv (by simp)).eventually_ne
      seedImagChart_differential_ne_zero
  have hall := hb.and (hd.and seedRoundAdmissible_eventually)
  obtain ⟨r,hr,hsub⟩ := Metric.mem_nhds_iff.mp hall
  refine ⟨r/2,by positivity,isCompact_closedBall _ _,?_⟩
  intro y hy
  apply hsub
  exact mem_ball.mpr (lt_of_le_of_lt (mem_closedBall.mp hy) (by linarith))

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Charts_SeedMetricNeighborhood
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Manifold Yau.Geometry Filter Set Metric
open scoped ContDiff RealInnerProductSpace Topology
noncomputable section

lemma seed_jet_admissible_center : JetAdmissible seedRealChart (roundMetricJet 0) 0 := by
  obtain ⟨hp,t,hpt,htt,_,hs⟩ := seed_round_admissibility
  exact ⟨hp,t,hpt,htt,hs⟩

lemma seed_jet_admissible_near_center :
    ∀ᶠ z : MetricJet BaseModel × BaseModel in 𝓝 (roundMetricJet 0,0),
      JetAdmissible seedRealChart z.1 z.2 := by
  apply jetAdmissible_eventually _ _ _ seedRealChart_smoothAt_zero _ seed_jet_admissible_center
  intro v hv
  change 0 < roundChartMetric seedPoint 0 v v
  rw [roundChartMetric_center]
  exact real_inner_self_pos.mpr hv

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Coefficients_CoefficientMetricJets
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open scoped ContDiff
noncomputable section
attribute [local instance] clmTopology clmAdd clmModule
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma coefficientMetricValue_smoothAt (c : CoefficientPoint E)
    (e : (E →L[ℝ] ℝ) ≃L[ℝ] E) (he : e.toContinuousLinearMap = c.1) :
    ContDiffAt ℝ ∞ (coefficientMetricValue : CoefficientPoint E → E →L[ℝ] E →L[ℝ] ℝ) c := by
  have hi : ContDiffAt ℝ ∞ ContinuousLinearMap.inverse c.1 := by
    rw [← he]; exact contDiffAt_map_inverse e
  exact contDiffAt_snd.smul (hi.comp c contDiffAt_fst)

lemma coefficientMetricJet_continuousAt (j : CoefficientFirstJet E)
    (e : (E →L[ℝ] ℝ) ≃L[ℝ] E) (he : e.toContinuousLinearMap = j.1.1) :
    ContinuousAt (coefficientMetricJet : CoefficientFirstJet E → MetricJet E) j := by
  have h := coefficientMetricValue_smoothAt j.1 e he
  exact (h.continuousAt.comp continuousAt_fst).prodMk
    (((h.continuousAt_fderiv (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).comp continuousAt_fst).clm_comp continuousAt_snd)

lemma coefficientMetricJet_actual (c : E → CoefficientPoint E) (x : E)
    (hc : DifferentiableAt ℝ c x) (e : (E →L[ℝ] ℝ) ≃L[ℝ] E)
    (he : e.toContinuousLinearMap = (c x).1) :
    coefficientMetricJet (c x,fderiv ℝ c x) =
      (coefficientMetricValue (c x), fderiv ℝ (coefficientMetricValue ∘ c) x) := by
  apply Prod.ext
  · rfl
  · exact (fderiv_comp x ((coefficientMetricValue_smoothAt (c x) e he).differentiableAt (by simp)) hc).symm

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Coefficients_RoundCoefficientJets
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Manifold Yau.Geometry
open scoped ContDiff RealInnerProductSpace
noncomputable section

lemma roundCoefficient_inverse (y : BaseModel) :
    (positiveMetricEquiv (roundChartMetric seedPoint y) (roundChartMetric_positive y)).symm.toContinuousLinearMap =
      (roundCoefficients y).1 :=
  (ContinuousLinearMap.inverse_equiv (positiveMetricEquiv _ (roundChartMetric_positive y))).symm

lemma roundCoefficients_smooth : ContDiff ℝ ∞ roundCoefficients := by
  apply contDiff_iff_contDiffAt.mpr
  intro y
  have hi : ContDiffAt ℝ ∞ ContinuousLinearMap.inverse (roundChartMetric seedPoint y) := by
    exact contDiffAt_map_inverse (positiveMetricEquiv _ (roundChartMetric_positive y))
  exact (hi.comp y (roundChartMetric_smooth seedPoint).contDiffAt).prodMk contDiffAt_const

lemma roundCoefficients_metric (y : BaseModel) :
    coefficientMetricValue (roundCoefficients y) = roundChartMetric seedPoint y := by
  simp only [coefficientMetricValue,roundCoefficients,one_smul]
  have h1 : ContinuousLinearMap.inverse (roundChartMetric seedPoint y) =
      (positiveMetricEquiv _ (roundChartMetric_positive y)).symm.toContinuousLinearMap :=
    ContinuousLinearMap.inverse_equiv (positiveMetricEquiv _ (roundChartMetric_positive y))
  rw [h1,ContinuousLinearMap.inverse_equiv]
  rfl

lemma roundCoefficientJet_metric (y : BaseModel) :
    coefficientMetricJet (roundCoefficientJet y) = roundMetricJet y := by
  rw [roundCoefficientJet,coefficientMetricJet_actual roundCoefficients y
    (roundCoefficients_smooth.differentiable (by simp) y)
    (positiveMetricEquiv _ (roundChartMetric_positive y)).symm (roundCoefficient_inverse y)]
  have he : coefficientMetricValue ∘ roundCoefficients = roundChartMetric seedPoint :=
    funext roundCoefficients_metric
  rw [he,roundCoefficients_metric]
  rfl

lemma roundCoefficientJet_continuous : Continuous roundCoefficientJet :=
  roundCoefficients_smooth.continuous.prodMk (roundCoefficients_smooth.continuous_fderiv (by simp))

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Coefficients_SeedCoefficientNeighborhood
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Manifold Yau.Geometry Filter Set Metric
open scoped ContDiff RealInnerProductSpace Topology
noncomputable section

lemma seed_coefficient_admissible_near_center :
    ∀ᶠ z : CoefficientFirstJet BaseModel × BaseModel in 𝓝 (roundCoefficientJet 0,0),
      JetAdmissible seedRealChart (coefficientMetricJet z.1) z.2 := by
  have hc := coefficientMetricJet_continuousAt (roundCoefficientJet 0)
    (positiveMetricEquiv _ (roundChartMetric_positive 0)).symm (roundCoefficient_inverse 0)
  have h : ContinuousAt (fun z : CoefficientFirstJet BaseModel × BaseModel ↦
      (coefficientMetricJet z.1,z.2)) (roundCoefficientJet 0,0) := by
    have hcf : ContinuousAt (fun z : CoefficientFirstJet BaseModel × BaseModel ↦ coefficientMetricJet z.1)
        (roundCoefficientJet 0,0) := by
      apply ContinuousAt.comp (f := fun z : CoefficientFirstJet BaseModel × BaseModel ↦ z.1)
        (x := (roundCoefficientJet 0,(0:BaseModel))) (g := coefficientMetricJet (E := BaseModel))
      · exact hc
      · exact continuousAt_fst
    exact hcf.prodMk continuousAt_snd
  have he : ∀ᶠ z : MetricJet BaseModel × BaseModel in
      𝓝 (coefficientMetricJet (roundCoefficientJet 0),0), JetAdmissible seedRealChart z.1 z.2 := by
    rw [roundCoefficientJet_metric]
    exact seed_jet_admissible_near_center
  exact h.tendsto.eventually he

theorem seed_uniform_coefficient_neighborhood : ∃ r δ : ℝ, 0 < r ∧ 0 < δ ∧
    IsCompact (closedBall (0 : BaseModel) r) ∧
    (∀ y ∈ closedBall (0 : BaseModel) r,
      seedChartAmbient y ∈ seedLogDomain ∧ fderiv ℝ seedImagChart y ≠ 0) ∧
    ∀ c : BaseModel → CoefficientPoint BaseModel,
      (∀ y ∈ closedBall (0 : BaseModel) r,
        dist ((c y,fderiv ℝ c y) : CoefficientFirstJet BaseModel) (roundCoefficientJet y) < δ) →
      ∀ y ∈ closedBall (0 : BaseModel) r,
        JetAdmissible seedRealChart (coefficientMetricJet (c y,fderiv ℝ c y)) y := by
  have hev : {z : CoefficientFirstJet BaseModel × BaseModel |
      JetAdmissible seedRealChart (coefficientMetricJet z.1) z.2} ∈ 𝓝 (roundCoefficientJet 0,0) :=
    seed_coefficient_admissible_near_center
  obtain ⟨ε,hε,hεsub⟩ := (Metric.mem_nhds_iff (α := CoefficientFirstJet BaseModel × BaseModel)).mp hev
  have hnear : ∀ᶠ y in 𝓝 (0 : BaseModel), dist (roundCoefficientJet y) (roundCoefficientJet 0) < ε/2 :=
    roundCoefficientJet_continuous.continuousAt.preimage_mem_nhds (ball_mem_nhds _ (by positivity))
  obtain ⟨a,ha,hasub⟩ := Metric.mem_nhds_iff.mp hnear
  obtain ⟨b,hb,_,hbprop⟩ := seed_round_compact_patch
  let r : ℝ := min (a/2) (min (ε/2) b)
  have hr : 0 < r := lt_min (by positivity) (lt_min (by positivity) hb)
  have hra : r < a := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hre : r < ε := lt_of_le_of_lt ((min_le_right _ _).trans (min_le_left _ _)) (by linarith)
  have hrb : r ≤ b := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨r,ε/2,hr,by positivity,isCompact_closedBall _ _,?_,?_⟩
  · intro y hy
    exact (hbprop y (closedBall_subset_closedBall hrb hy)).imp_right And.left
  · intro c hc y hy
    apply hεsub (a := (((c y,fderiv ℝ c y) : CoefficientFirstJet BaseModel),y))
    rw [mem_ball,Prod.dist_eq]
    apply max_lt
    · have hround := hasub (mem_ball.mpr (lt_of_le_of_lt (mem_closedBall.mp hy) hra))
      change dist (roundCoefficientJet y) (roundCoefficientJet 0) < ε/2 at hround
      exact lt_of_le_of_lt (dist_triangle _ (roundCoefficientJet y) _)
        (by dsimp only <;> linarith [hc y hy])
    · exact lt_of_le_of_lt (mem_closedBall.mp hy) hre

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_PositiveContravariant
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

lemma coefficientMetric_positive (c : CoefficientPoint E)
    (hp : ∀ α : E →L[ℝ] ℝ, α ≠ 0 → 0 < α (c.1 α)) (hρ : 0 < c.2) (v : E) (hv : v ≠ 0) :
    0 < coefficientMetricValue c v v := by
  let e := positiveContravariantEquiv c.1 hp
  have hi : ContinuousLinearMap.inverse c.1 = e.symm.toContinuousLinearMap :=
    ContinuousLinearMap.inverse_equiv e
  have he : e.symm v ≠ 0 := by
    intro hz
    have h := congrArg e hz
    exact hv (by simpa using h)
  have hh := hp (e.symm v) he
  change 0 < e.symm v (e (e.symm v)) at hh
  rw [e.apply_symm_apply] at hh
  simpa [coefficientMetricValue,hi] using mul_pos hρ hh

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_SeedCoordinateCube
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Manifold Yau.Geometry Filter Set Metric
open scoped ContDiff RealInnerProductSpace Topology
noncomputable section

lemma seedCoordinateCube_closed (a : ℝ) : IsClosed (seedCoordinateCube a) := by
  simpa [seedCoordinateCube,Set.ofPred_forall,EuclideanSpace.proj] using
    isClosed_iInter (fun i : Fin 4 ↦ isClosed_le (EuclideanSpace.proj i).continuous.abs
      (continuous_const (y := a)))

lemma seedCoordinateCube_norm {a : ℝ} (ha : 0 ≤ a) {y : BaseModel}
    (hy : y ∈ seedCoordinateCube a) : ‖y‖ ≤ 2*a := by
  have hs (i : Fin 4) : (y i)^2 ≤ a^2 := by
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg (y i)) ha).mpr (hy i)
  have hsum := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin 4))) ↦ hs i)
  rw [← EuclideanSpace.real_norm_sq_eq] at hsum
  norm_num at hsum
  nlinarith [norm_nonneg y]

lemma seedCoordinateCube_compact {a : ℝ} (ha : 0 ≤ a) : IsCompact (seedCoordinateCube a) := by
  apply (isCompact_closedBall (0 : BaseModel) (2*a)).of_isClosed_subset (seedCoordinateCube_closed a)
  intro y hy
  rw [mem_closedBall,dist_zero_right]
  exact seedCoordinateCube_norm ha hy

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_SeedEnvelopePatch
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Manifold Yau.Geometry Set Metric
open scoped ContDiff Topology
noncomputable section

theorem seed_envelope_coordinate_patch_oai : ∃ r a δ : ℝ, 0 < r ∧ 0 < a ∧ 0 < δ ∧
    IsCompact (closedBall (0 : BaseModel) r) ∧ IsCompact (seedCoordinateCube a) ∧
    seedCoordinateCube a ⊆ ball (0 : BaseModel) r ∧
    (∀ y ∈ closedBall (0 : BaseModel) r,
      seedChartAmbient y ∈ seedLogDomain ∧ fderiv ℝ seedImagChart y ≠ 0) ∧
    ∀ c : BaseModel → CoefficientPoint BaseModel,
      (∀ y ∈ closedBall (0 : BaseModel) r, DifferentiableAt ℝ c y) →
      (∀ y ∈ closedBall (0 : BaseModel) r, ∀ α : BaseModel →L[ℝ] ℝ,
        α ≠ 0 → 0 < α ((c y).1 α)) →
      (∀ y ∈ closedBall (0 : BaseModel) r, 0 < (c y).2) →
      (∀ y ∈ closedBall (0 : BaseModel) r,
        dist ((c y,fderiv ℝ c y) : CoefficientFirstJet BaseModel) (roundCoefficientJet y) < δ) →
      ∀ y ∈ closedBall (0 : BaseModel) r,
        let g := coefficientMetricValue ∘ c
        let p := localMetricGradient g seedRealChart y
        let H := localMetricHessian g seedRealChart y
        (∀ v : BaseModel, v ≠ 0 → 0 < g y v v) ∧ p ≠ 0 ∧
        ∃ t : BaseModel, g y p t = 0 ∧ g y t t = 1 ∧
          0 < H p p + (g y p p+4)*H t t := by
  obtain ⟨r,δ,hr,hδ,hK,hbranch,hpersist⟩ := seed_uniform_coefficient_neighborhood
  have hcub : seedCoordinateCube (r/4) ⊆ ball (0 : BaseModel) r := by
    intro y hy
    rw [mem_ball,dist_zero_right]
    have hn := seedCoordinateCube_norm (a := r/4) (by positivity) hy
    linarith
  refine ⟨r,r/4,δ,hr,by positivity,hδ,hK,seedCoordinateCube_compact (by positivity),hcub,hbranch,?_⟩
  intro c hc hA hρ hclose y hy
  have ha := hpersist c hclose y hy
  rw [coefficientMetricJet_actual c y (hc y hy)
    (positiveContravariantEquiv (c y).1 (hA y hy)) rfl] at ha
  refine ⟨fun v hv ↦ coefficientMetric_positive (c y) (hA y hy) (hρ y hy) v hv,?_⟩
  exact (jetAdmissible_actual (coefficientMetricValue ∘ c) seedRealChart y).mp ha

end
end Yau.Target

end OAI
end

theorem solution : type_of% @OAI.Yau.Target.seed_envelope_coordinate_patch_oai := @OAI.Yau.Target.seed_envelope_coordinate_patch_oai
