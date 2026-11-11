-- Prove2me | solution 1 for OAI.Yau.Target.intrinsic_noncritical_placed_data
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T00:30:44.881659+00:00
-- url     : https://prove2.me/submissions/711aeb35-5dbf-4f6f-add9-8d84fe031c06

import Mathlib
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Abs
import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.Calculus.TaylorIntegral
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.Finsupp.Weight
import Mathlib.Data.List.FinRange
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.ColumnRowPartitioned
import Mathlib.Geometry.Manifold.Algebra.LieGroup
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.Geometry.Manifold.Riemannian.Basic
import Mathlib.Geometry.Manifold.VectorBundle.Riemannian
import Mathlib.LinearAlgebra.Basis.Prod
import Mathlib.LinearAlgebra.Basis.SMul
import Mathlib.LinearAlgebra.Determinant
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.LinearAlgebra.Matrix.Basis
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.LinearAlgebra.Matrix.SesquilinearForm
import Mathlib.LinearAlgebra.QuadraticForm.Basic
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Measure.Hausdorff
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.Compactness.LocallyCompact
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.UniformSpace.HeineCantor
import Definitions.Def_YauCounterexample
import Definitions.Def_OAIQ237Ny004
import Theorems.Thm_OAI_Yau_Geometry_exists_placed_envelope
import Theorems.Thm_OAI_Yau_Target_seed_envelope_coordinate_patch

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

lemma christoffelTensor_pair (m : E ≃L[ℝ] E →L[ℝ] ℝ)
    (D : E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) (u v w : E) :
    m (christoffelTensor m D u v) w = (D u v w + D v u w - D w u v)/2 := by
  change m (m.symm (christoffelCovector D u v)) w = _
  rw [m.apply_symm_apply, christoffelCovector_apply]

end Yau.Geometry

end

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Charts_MetricConnectionFamilyLemmas
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

omit [CompleteSpace E] in
lemma metricConnection_eq (g : E →L[ℝ] E →L[ℝ] ℝ)
    (hp : ∀ v : E, v ≠ 0 → 0 < g v v) (D : E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) :
    metricConnection g D = christoffelTensor (positiveMetricEquiv g hp) D := by
  have hi : ContinuousLinearMap.inverse g = (positiveMetricEquiv g hp).symm.toContinuousLinearMap :=
    ContinuousLinearMap.inverse_equiv (positiveMetricEquiv g hp)
  simp only [metricConnection, christoffelTensor, hi]

end

open scoped ContDiff
attribute [local instance] clmTopology clmAdd clmModule

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

open scoped ContDiff
attribute [local instance] clmTopology clmAdd clmModule
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

lemma linearCovectorPull_apply (e : F ≃L[ℝ] E) (α : E →L[ℝ] ℝ) (u : F) :
    linearCovectorPull e α u = α (e u) := rfl

lemma linearMetricPull_apply (e : F ≃L[ℝ] E) (g : E →L[ℝ] E →L[ℝ] ℝ) (u v : F) :
    linearMetricPull e g u v = g (e u) (e v) := rfl

lemma linearMetricField_positive (e : F ≃L[ℝ] E)
    (g : E → E →L[ℝ] E →L[ℝ] ℝ) (x : F)
    (hp : ∀ v, v ≠ 0 → 0 < g (e x) v v) :
    ∀ v, v ≠ 0 → 0 < linearMetricField e g x v v := by
  intro v hv
  exact hp (e v) (by intro h; exact hv (e.injective (h.trans e.map_zero.symm)))

lemma linearMetricField_fderiv (e : F ≃L[ℝ] E)
    (g : E → E →L[ℝ] E →L[ℝ] ℝ) (x : F) (hg : DifferentiableAt ℝ g (e x)) :
    fderiv ℝ (linearMetricField e g) x =
      (linearMetricPull e).toContinuousLinearMap ∘L (fderiv ℝ g (e x)) ∘L e.toContinuousLinearMap := by
  exact ((linearMetricPull e).toContinuousLinearMap.hasFDerivAt.comp x
    (hg.hasFDerivAt.comp x e.hasFDerivAt)).fderiv

lemma linearMetricField_fderiv_apply (e : F ≃L[ℝ] E)
    (g : E → E →L[ℝ] E →L[ℝ] ℝ) (x : F) (hg : DifferentiableAt ℝ g (e x)) (u v w : F) :
    fderiv ℝ (linearMetricField e g) x u v w = fderiv ℝ g (e x) (e u) (e v) (e w) := by
  rw [linearMetricField_fderiv e g x hg]; rfl

lemma linearScalar_fderiv (e : F ≃L[ℝ] E) (f : E → ℝ) (x : F)
    (hf : DifferentiableAt ℝ f (e x)) :
    fderiv ℝ (f ∘ e) x = linearCovectorPull e (fderiv ℝ f (e x)) := by
  exact (hf.hasFDerivAt.comp x e.hasFDerivAt).fderiv

variable [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]

lemma localMetricGradient_pair (g : E → E →L[ℝ] E →L[ℝ] ℝ)
    (f : E → ℝ) (x : E) (hp : ∀ v, v ≠ 0 → 0 < g x v v) (v : E) :
    g x (localMetricGradient g f x) v = fderiv ℝ f x v := by
  have hi : ContinuousLinearMap.inverse (g x) =
      (positiveMetricEquiv (g x) hp).symm.toContinuousLinearMap :=
    ContinuousLinearMap.inverse_equiv (positiveMetricEquiv (g x) hp)
  unfold localMetricGradient
  rw [hi]
  exact congrArg (fun α : E →L[ℝ] ℝ ↦ α v)
    ((positiveMetricEquiv (g x) hp).apply_symm_apply (fderiv ℝ f x))

lemma linearMetricField_gradient (e : F ≃L[ℝ] E)
    (g : E → E →L[ℝ] E →L[ℝ] ℝ) (f : E → ℝ) (x : F)
    (hp : ∀ v, v ≠ 0 → 0 < g (e x) v v) (hf : DifferentiableAt ℝ f (e x)) :
    localMetricGradient (linearMetricField e g) (f ∘ e) x =
      e.symm (localMetricGradient g f (e x)) := by
  apply localMetricGradient_eq_of_pair _ _ _ _ (linearMetricField_positive e g x hp)
  intro v
  change g (e x) (e (e.symm (localMetricGradient g f (e x)))) (e v) = _
  rw [e.apply_symm_apply,localMetricGradient_pair g f (e x) hp,
    linearScalar_fderiv e f x hf]
  rfl

lemma metricConnection_pair (g : E →L[ℝ] E →L[ℝ] ℝ)
    (hp : ∀ v, v ≠ 0 → 0 < g v v) (D : E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) (u v w : E) :
    g (metricConnection g D u v) w = (D u v w + D v u w - D w u v)/2 := by
  rw [metricConnection_eq g hp D]
  exact christoffelTensor_pair (positiveMetricEquiv g hp) D u v w

lemma linearMetricField_connection (e : F ≃L[ℝ] E)
    (g : E → E →L[ℝ] E →L[ℝ] ℝ) (x : F)
    (hp : ∀ v, v ≠ 0 → 0 < g (e x) v v) (hg : DifferentiableAt ℝ g (e x)) (u v : F) :
    metricConnection (linearMetricField e g x) (fderiv ℝ (linearMetricField e g) x) u v =
      e.symm (metricConnection (g (e x)) (fderiv ℝ g (e x)) (e u) (e v)) := by
  apply (positiveMetricEquiv _ (linearMetricField_positive e g x hp)).injective
  ext w
  change linearMetricField e g x _ w = linearMetricField e g x _ w
  rw [metricConnection_pair _ (linearMetricField_positive e g x hp)]
  change _ = g (e x) (e (e.symm _)) (e w)
  rw [e.apply_symm_apply,metricConnection_pair _ hp]
  simp only [linearMetricField_fderiv_apply e g x hg]

end Yau.Geometry

end

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_HessianLinearTransport
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
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F]

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
lemma linearScalar_second (e : F ≃L[ℝ] E) (f : E → ℝ) (x : F)
    (hf : ContDiffAt ℝ ∞ f (e x)) (u v : F) :
    fderiv ℝ (fderiv ℝ (f ∘ e)) x u v =
      fderiv ℝ (fderiv ℝ f) (e x) (e u) (e v) := by
  have hnear := ((hf.of_le (show (1 : WithTop ℕ∞) ≤ ∞ by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).eventually (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).filter_mono
    e.continuous.continuousAt.tendsto
  have he : fderiv ℝ (f ∘ e) =ᶠ[𝓝 x]
      (fun y ↦ linearCovectorPull e (fderiv ℝ f (e y))) := by
    filter_upwards [hnear] with y hy
    change ContDiffAt ℝ 1 f (e y) at hy
    exact linearScalar_fderiv e f y (hy.differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top))
  have hd := (hf.fderiv_right (show (∞ : WithTop ℕ∞)+1 ≤ ∞ by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  have ht := (linearCovectorPull e).toContinuousLinearMap.hasFDerivAt.comp x
    (hd.hasFDerivAt.comp x e.hasFDerivAt)
  change HasFDerivAt (fun y ↦ linearCovectorPull e (fderiv ℝ f (e y))) _ x at ht
  rw [he.fderiv_eq]
  rw [ht.fderiv]
  rfl

lemma linearMetricField_hessian (e : F ≃L[ℝ] E)
    (g : E → E →L[ℝ] E →L[ℝ] ℝ) (f : E → ℝ) (x : F)
    (hp : ∀ v, v ≠ 0 → 0 < g (e x) v v) (hg : DifferentiableAt ℝ g (e x))
    (hf : ContDiffAt ℝ ∞ f (e x)) (u v : F) :
    localMetricHessian (linearMetricField e g) (f ∘ e) x u v =
      localMetricHessian g f (e x) (e u) (e v) := by
  change fderiv ℝ (fderiv ℝ (f ∘ e)) x u v -
    fderiv ℝ (f ∘ e) x (metricConnection _ _ u v) = _
  rw [linearScalar_second e f x hf,linearMetricField_connection e g x hp hg,
    linearScalar_fderiv e f x (hf.differentiableAt (by simp)),linearCovectorPull_apply,
    e.apply_symm_apply]
  rfl

theorem linearMetricField_admissible (e : F ≃L[ℝ] E)
    (g : E → E →L[ℝ] E →L[ℝ] ℝ) (f : E → ℝ) (x : F)
    (hp : ∀ v, v ≠ 0 → 0 < g (e x) v v) (hg : DifferentiableAt ℝ g (e x))
    (hf : ContDiffAt ℝ ∞ f (e x))
    (hn : localMetricGradient g f (e x) ≠ 0)
    (ha : ∃ t : E, g (e x) (localMetricGradient g f (e x)) t = 0 ∧
      g (e x) t t = 1 ∧
      0 < localMetricHessian g f (e x) (localMetricGradient g f (e x)) (localMetricGradient g f (e x)) +
        (g (e x) (localMetricGradient g f (e x)) (localMetricGradient g f (e x))+4) *
          localMetricHessian g f (e x) t t) :
    let G := linearMetricField e g
    let P := localMetricGradient G (f ∘ e) x
    let H := localMetricHessian G (f ∘ e) x
    P ≠ 0 ∧ ∃ t : F, G x P t = 0 ∧ G x t t = 1 ∧
      0 < H P P + (G x P P+4)*H t t := by
  dsimp only
  rw [linearMetricField_gradient e g f x hp (hf.differentiableAt (by simp))]
  refine ⟨?_,?_⟩
  · intro h
    exact hn (by simpa using congrArg e h)
  · obtain ⟨t,ht,hu,hs⟩ := ha
    refine ⟨e.symm t,?_,?_,?_⟩
    · simpa only [linearMetricField,linearMetricPull_apply,e.apply_symm_apply] using ht
    · simpa only [linearMetricField,linearMetricPull_apply,e.apply_symm_apply] using hu
    · simpa only [linearMetricField_hessian e g f x hp hg hf,
        linearMetricField,linearMetricPull_apply,e.apply_symm_apply] using hs

end
end Yau.Geometry

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

local instance instFactEqNatFinrankRealSeedAmbientHAddOfNat_r3eee16_1 : Fact (Module.finrank ℝ SeedAmbient = 4+1) := ⟨by simp [SeedAmbient]⟩
lemma seedQuadratic_contDiff : ContDiff ℝ ∞ seedQuadratic :=
  seedZ1.contDiff.mul seedZ2.contDiff

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

local instance instFactEqNatFinrankRealSeedAmbientHAddOfNat_1_r3eee16_1 : Fact (Module.finrank ℝ SeedAmbient = 4+1) := ⟨by simp [SeedAmbient]⟩
lemma seedLogDomain_open : IsOpen seedLogDomain :=
  Complex.isOpen_slitPlane.preimage seedQuadratic_contDiff.continuous

lemma seedLog_contDiffAt {x : SeedAmbient} (hx : x ∈ seedLogDomain) :
    ContDiffAt ℝ ∞ seedLog x :=
  ((Complex.contDiffAt_log hx (n := ∞)).restrict_scalars ℝ).comp x seedQuadratic_contDiff.contDiffAt

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

end
end Yau.Geometry

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

lemma coefficientMetric_symmetric (c : CoefficientPoint E)
    (hp : ∀ α : E →L[ℝ] ℝ, α ≠ 0 → 0 < α (c.1 α))
    (hs : ∀ α β : E →L[ℝ] ℝ, α (c.1 β) = β (c.1 α)) (u v : E) :
    coefficientMetricValue c u v = coefficientMetricValue c v u := by
  let e := positiveContravariantEquiv c.1 hp
  have hi : ContinuousLinearMap.inverse c.1 = e.symm.toContinuousLinearMap :=
    ContinuousLinearMap.inverse_equiv e
  have hh := hs (e.symm u) (e.symm v)
  change e.symm u (e (e.symm v)) = e.symm v (e (e.symm u)) at hh
  rw [e.apply_symm_apply,e.apply_symm_apply] at hh
  simpa [coefficientMetricValue,hi] using congrArg (fun z : ℝ ↦ c.2*z) hh

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_SeedCoordAdmissibility
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Yau.Geometry Yau.Jets Set Metric
open scoped ContDiff
noncomputable section

lemma seedRealChart_smoothAt {y : BaseModel} (hy : seedChartAmbient y ∈ seedLogDomain) :
    ContDiffAt ℝ ∞ seedRealChart y := by
  exact (Complex.reCLM.contDiff.contDiffAt.comp _ (seedLog_contDiffAt hy)).comp y
    seedChartAmbient_smooth.contDiffAt

lemma seedImagChart_smoothAt {y : BaseModel} (hy : seedChartAmbient y ∈ seedLogDomain) :
    ContDiffAt ℝ ∞ seedImagChart y := by
  exact (Complex.imCLM.contDiff.contDiffAt.comp _ (seedLog_contDiffAt hy)).comp y
    seedChartAmbient_smooth.contDiffAt

lemma seedCoordMetric_differentiable (c : BaseModel → CoefficientPoint BaseModel)
    (y : BaseModel) (hc : DifferentiableAt ℝ c y)
    (hA : ∀ α : BaseModel →L[ℝ] ℝ, α ≠ 0 → 0 < α ((c y).1 α)) :
    DifferentiableAt ℝ (coefficientMetricValue ∘ c) y :=
  ((coefficientMetricValue_smoothAt (c y) (positiveContravariantEquiv (c y).1 hA) rfl).differentiableAt
    (by simp)).comp y hc

theorem seed_envelope_Coord_patch : ∃ r a δ : ℝ, 0 < r ∧ 0 < a ∧ 0 < δ ∧
    IsCompact (seedCoordinateCube a) ∧ seedCoordinateCube a ⊆ ball (0 : BaseModel) r ∧
    (∀ y ∈ closedBall (0 : BaseModel) r,
      seedChartAmbient y ∈ seedLogDomain ∧ fderiv ℝ seedImagChart y ≠ 0) ∧
    ∀ c : BaseModel → CoefficientPoint BaseModel,
      (∀ y ∈ closedBall (0 : BaseModel) r, DifferentiableAt ℝ c y) →
      (∀ y ∈ closedBall (0 : BaseModel) r, ∀ α : BaseModel →L[ℝ] ℝ,
        α ≠ 0 → 0 < α ((c y).1 α)) →
      (∀ y ∈ closedBall (0 : BaseModel) r, 0 < (c y).2) →
      (∀ y ∈ closedBall (0 : BaseModel) r,
        dist ((c y,fderiv ℝ c y) : CoefficientFirstJet BaseModel) (roundCoefficientJet y) < δ) →
      ∀ x : _root_.OAI.Yau.Jets.Coord, seedCoordEquiv x ∈ closedBall (0 : BaseModel) r →
        let g := seedCoordMetric c
        let p := metricGradient g seedCoordReal x
        let H := sourceHessian g seedCoordReal x
        (∀ v : _root_.OAI.Yau.Jets.Coord, v ≠ 0 → 0 < g x v v) ∧ p ≠ 0 ∧
        ∃ t : _root_.OAI.Yau.Jets.Coord, g x p t = 0 ∧ g x t t = 1 ∧
          0 < H p p + (g x p p+4)*H t t := by
  obtain ⟨r,a,δ,hr,ha,hδ,_,hK,hsub,hbranch,hpatch⟩ := seed_envelope_coordinate_patch
  refine ⟨r,a,δ,hr,ha,hδ,hK,hsub,hbranch,?_⟩
  intro c hc hA hρ hclose x hx
  obtain ⟨hp,hn,had⟩ := hpatch c hc hA hρ hclose (seedCoordEquiv x) hx
  refine ⟨linearMetricField_positive seedCoordEquiv _ x hp,?_⟩
  exact linearMetricField_admissible seedCoordEquiv (coefficientMetricValue ∘ c) seedRealChart x hp
    (seedCoordMetric_differentiable c _ (hc _ hx) (hA _ hx))
    (seedRealChart_smoothAt (hbranch _ hx).1) hn had

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Charts_SeedCoordMetricRegularity
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Yau.Geometry Yau.Jets
open scoped ContDiff
noncomputable section
attribute [local instance] clmTopology clmAdd clmModule

lemma seedCoordMetric_smooth (c : BaseModel → CoefficientPoint BaseModel)
    (hc : ContDiff ℝ ∞ c)
    (hp : ∀ y (α : BaseModel →L[ℝ] ℝ), α ≠ 0 → 0 < α ((c y).1 α)) :
    ContDiff ℝ ∞ (seedCoordMetric c) := by
  have hm : ContDiff ℝ ∞ (coefficientMetricValue ∘ c) := by
    rw [contDiff_iff_contDiffAt]
    intro y
    exact (coefficientMetricValue_smoothAt (c y) (positiveContravariantEquiv (c y).1 (hp y)) rfl).comp y hc.contDiffAt
  have hh := (contDiff_const (c := seedCoordEquiv.toContinuousLinearMap.precomp ℝ)).clm_comp
    ((hm.comp seedCoordEquiv.contDiff).clm_comp
      (contDiff_const (c := seedCoordEquiv.toContinuousLinearMap)))
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  funext x
  ext u v
  rfl

lemma seedCoordMetric_positive (c : BaseModel → CoefficientPoint BaseModel)
    (hp : ∀ y (α : BaseModel →L[ℝ] ℝ), α ≠ 0 → 0 < α ((c y).1 α))
    (hρ : ∀ y, 0 < (c y).2) (x : _root_.OAI.Yau.Jets.Coord) (v : _root_.OAI.Yau.Jets.Coord) (hv : v ≠ 0) :
    0 < seedCoordMetric c x v v :=
  linearMetricField_positive seedCoordEquiv (coefficientMetricValue ∘ c) x
    (coefficientMetric_positive (c (seedCoordEquiv x)) (hp _) (hρ _)) v hv

lemma seedCoordMetric_symmetric (c : BaseModel → CoefficientPoint BaseModel)
    (hp : ∀ y (α : BaseModel →L[ℝ] ℝ), α ≠ 0 → 0 < α ((c y).1 α))
    (hs : ∀ y (α β : BaseModel →L[ℝ] ℝ), α ((c y).1 β) = β ((c y).1 α))
    (x u v : _root_.OAI.Yau.Jets.Coord) : seedCoordMetric c x u v = seedCoordMetric c x v u :=
  coefficientMetric_symmetric (c (seedCoordEquiv x)) (hp _) (hs _) _ _

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Coefficients_MatrixCoefficientMap
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Matrix Yau.Geometry
open scoped RealInnerProductSpace ContDiff
noncomputable section

lemma baseCovectorCoordinates_apply (α : BaseModel →L[ℝ] ℝ) (v : BaseModel) :
    α v = baseCovectorCoordinates α ⬝ᵥ WithLp.ofLp v := by
  have hv := (EuclideanSpace.basisFun (Fin 4) ℝ).sum_repr v
  conv_lhs => rw [← hv]
  simp [baseCovectorCoordinates,map_sum,map_smul,dotProduct,mul_comm]

lemma baseCovectorCoordinates_injective : Function.Injective baseCovectorCoordinates := by
  intro α β h
  ext v
  rw [baseCovectorCoordinates_apply,baseCovectorCoordinates_apply,h]

lemma baseCovectorCoordinates_ne_zero {α : BaseModel →L[ℝ] ℝ} (hα : α ≠ 0) :
    baseCovectorCoordinates α ≠ 0 := by
  intro h
  exact hα (baseCovectorCoordinates_injective (h.trans (by ext i; rfl)))

lemma matrixContravariant_coordinates (A : Matrix (Fin 4) (Fin 4) ℝ)
    (α : BaseModel →L[ℝ] ℝ) :
    WithLp.ofLp (matrixContravariant A α) = A *ᵥ baseCovectorCoordinates α := by
  ext k
  simp [matrixContravariant,baseCovectorCoordinates,mulVec,dotProduct,
    EuclideanSpace.basisFun_apply,Pi.single_apply,ite_mul,mul_ite,mul_comm]

lemma matrixContravariant_pair (A : Matrix (Fin 4) (Fin 4) ℝ) (α β : BaseModel →L[ℝ] ℝ) :
    α (matrixContravariant A β) = baseCovectorCoordinates α ⬝ᵥ (A *ᵥ baseCovectorCoordinates β) := by
  rw [baseCovectorCoordinates_apply,matrixContravariant_coordinates]

lemma matrixContravariant_positive (A : Matrix (Fin 4) (Fin 4) ℝ) (hA : A.PosDef)
    (α : BaseModel →L[ℝ] ℝ) (hα : α ≠ 0) : 0 < α (matrixContravariant A α) := by
  rw [matrixContravariant_pair]
  simpa only [star_trivial] using hA.dotProduct_mulVec_pos (baseCovectorCoordinates_ne_zero hα)

lemma matrixCovariant_coordinates (B : Matrix (Fin 4) (Fin 4) ℝ) (v : BaseModel) :
    baseCovectorCoordinates (matrixCovariant B v) = B *ᵥ WithLp.ofLp v := by
  ext k
  simp [baseCovectorCoordinates,matrixCovariant,
    EuclideanSpace.inner_single_left,mulVec,dotProduct,mul_comm]

lemma matrixCovariant_apply (B : Matrix (Fin 4) (Fin 4) ℝ) (v w : BaseModel) :
    matrixCovariant B v w = (B *ᵥ WithLp.ofLp v) ⬝ᵥ WithLp.ofLp w := by
  rw [baseCovectorCoordinates_apply,matrixCovariant_coordinates]

lemma matrixContravariant_inverse (A : Matrix (Fin 4) (Fin 4) ℝ) (hA : IsUnit A.det) :
    ContinuousLinearMap.inverse (matrixContravariant A) = matrixCovariant A⁻¹ := by
  apply ContinuousLinearMap.inverse_eq
  · ext v i
    change (matrixContravariant A (matrixCovariant A⁻¹ v)) i = v i
    have h := matrixContravariant_coordinates A (matrixCovariant A⁻¹ v)
    rw [matrixCovariant_coordinates,mulVec_mulVec,mul_nonsing_inv A hA,one_mulVec] at h
    exact congrFun h i
  · ext α v
    have h : baseCovectorCoordinates (matrixCovariant A⁻¹ (matrixContravariant A α)) =
        baseCovectorCoordinates α := by
      rw [matrixCovariant_coordinates,matrixContravariant_coordinates,mulVec_mulVec,
        nonsing_inv_mul A hA,one_mulVec]
    exact congrArg (fun β : BaseModel →L[ℝ] ℝ ↦ β v) (baseCovectorCoordinates_injective h)

lemma matrixCovariant_smul (r : ℝ) (B : Matrix (Fin 4) (Fin 4) ℝ) :
    matrixCovariant (r • B) = r • matrixCovariant B := by
  ext v w
  simp [matrixCovariant_apply,smul_mulVec,smul_dotProduct]

lemma coefficientMetric_matrix (A : Matrix (Fin 4) (Fin 4) ℝ) (hA : A.PosDef) (ρ : ℝ) :
    coefficientMetricValue (matrixContravariant A,ρ) = matrixCovariant (ρ • A⁻¹) := by
  rw [coefficientMetricValue,matrixContravariant_inverse A (isUnit_iff_ne_zero.mpr hA.det_pos.ne'),
    matrixCovariant_smul]

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Coefficients_IntrinsicCoefficientMap
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Manifold Matrix Yau.Geometry
open scoped ContDiff
noncomputable section

lemma intrinsicChartCoefficient_pair (A : IntrinsicTensor) (ρ : Base → ℝ)
    (p : Base) (z : BaseModel) (α β : BaseModel →L[ℝ] ℝ) :
    α ((intrinsicChartCoefficient A ρ p z).1 β) =
      A ((extChartAt (𝓡 4) p).symm z)
        (sphereCoordinateCovector p z (baseCovectorCoordinates α))
        (sphereCoordinateCovector p z (baseCovectorCoordinates β)) := by
  change α (matrixContravariant _ β) = _
  rw [matrixContravariant_pair,intrinsicSphereChartTensor_eq,intrinsicAmbientMatrix_chart_pairing]

variable (A : IntrinsicTensor) (hs : ∀ x v w, A x v w = A x w v)
    (hp : ∀ x v, v ≠ 0 → 0 < A x v v)

include hs hp in
lemma intrinsicSphereChartTensor_posDef (p : Base) {z : BaseModel}
    (hz : z ∈ (extChartAt (𝓡 4) p).target) : (intrinsicSphereChartTensor A p z).PosDef := by
  rw [intrinsicSphereChartTensor_eq]
  change (frameContravariant _ _).PosDef
  rw [sphereChart_contravariant _ (intrinsicAmbientMatrix_posDef A hs hp _) zero_lt_one p hz
    (intrinsicAmbientMatrix_radial A _),one_smul]
  exact (sphereWeightedChartMatrix_posDef _ (intrinsicAmbientMatrix_posDef A hs hp _)
    zero_lt_one p hz).inv

include hs hp in
lemma intrinsicChartCoefficient_positive (ρ : Base → ℝ) (p : Base) {z : BaseModel}
    (hz : z ∈ (extChartAt (𝓡 4) p).target)
    (α : BaseModel →L[ℝ] ℝ) (hα : α ≠ 0) :
    0 < α ((intrinsicChartCoefficient A ρ p z).1 α) :=
  matrixContravariant_positive _ (intrinsicSphereChartTensor_posDef A hs hp p hz) α hα

include hs in
lemma intrinsicChartCoefficient_symmetric (ρ : Base → ℝ) (p : Base) (z : BaseModel)
    (α β : BaseModel →L[ℝ] ℝ) :
    α ((intrinsicChartCoefficient A ρ p z).1 β) = β ((intrinsicChartCoefficient A ρ p z).1 α) := by
  rw [intrinsicChartCoefficient_pair,intrinsicChartCoefficient_pair,hs]

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Coefficients_IntrinsicCoefficientMetric
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Manifold Matrix Yau.Geometry Filter
open scoped ContDiff Topology
noncomputable section

variable (A : IntrinsicTensor) (hs : ∀ x v w, A x v w = A x w v)
    (hp : ∀ x v, v ≠ 0 → 0 < A x v v)
    (ρ : Base → ℝ) (hρ : ∀ x, 0 < ρ x)

include hs hp hρ in
lemma intrinsicChartCoefficient_metric (p : Base) {z : BaseModel}
    (hz : z ∈ (extChartAt (𝓡 4) p).target) :
    coefficientMetricValue (intrinsicChartCoefficient A ρ p z) =
      matrixCovariant (baseChartMetric (intrinsicAmbientMatrix A) ρ p z) := by
  let B := intrinsicSphereChartTensor A p z
  let G := baseChartMetric (intrinsicAmbientMatrix A) ρ p z
  let r := ρ ((extChartAt (𝓡 4) p).symm z)
  have hr : 0 < r := hρ _
  have hB : B.PosDef := intrinsicSphereChartTensor_posDef A hs hp p hz
  have hG : G.PosDef := sphereWeightedChartMatrix_posDef _
    (intrinsicAmbientMatrix_posDef A hs hp _) hr p hz
  have hi : G⁻¹ = r⁻¹ • B := intrinsic_horizontal_inverse A hs hp ρ hρ p hz
  have hb : B = r • G⁻¹ := by rw [hi,smul_smul,mul_inv_cancel₀ hr.ne',one_smul]
  have hbi : B⁻¹ = r⁻¹ • G := by
    apply Matrix.inv_eq_left_inv
    rw [hb,smul_mul_assoc,mul_smul_comm,smul_smul,inv_mul_cancel₀ hr.ne',one_smul,
      mul_nonsing_inv G (isUnit_iff_ne_zero.mpr hG.det_pos.ne')]
  change coefficientMetricValue (matrixContravariant B,r) = matrixCovariant G
  rw [coefficientMetric_matrix B hB r,hbi,smul_smul,mul_inv_cancel₀ hr.ne',one_smul]

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Coefficients_IntrinsicCoefficientSmooth
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Manifold Matrix Yau.Geometry Filter
open scoped ContDiff Topology
noncomputable section
attribute [local instance] clmTopology clmAdd clmModule

variable (A : IntrinsicTensor) (hA : IntrinsicTensorSmooth A)
    (hs : ∀ x v w, A x v w = A x w v)
    (hp : ∀ x v, v ≠ 0 → 0 < A x v v)

include hA hs hp in
lemma intrinsicChartCoefficient_smoothAt (ρ : Base → ℝ)
    (hρ : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ ρ) (p : Base) {z : BaseModel}
    (hz : z ∈ (extChartAt (𝓡 4) p).target) :
    ContDiffAt ℝ ∞ (intrinsicChartCoefficient A ρ p) z := by
  apply ContDiffAt.prodMk _ (smooth_inverse_chart_comp ρ hρ p hz)
  change ContDiffAt ℝ ∞ (fun w ↦ matrixContravariant (intrinsicSphereChartTensor A p w)) z
  unfold matrixContravariant
  apply ContDiffAt.sum
  intro i _
  apply ContDiffAt.sum
  intro j _
  let : IsBoundedSMul ℝ ((BaseModel →L[ℝ] ℝ) →L[ℝ] BaseModel) :=
    IsBoundedSMul.of_norm_smul_le ContinuousLinearMap.opNorm_smul_le
  exact (intrinsicSphereChartTensor_smoothAt A hA hs hp p hz i j).smul contDiffAt_const

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_CompactSmoothExtension
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Yau.Jets Set Filter Manifold
open scoped ContDiff Topology
noncomputable section
attribute [local instance] clmTopology clmAdd clmModule

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
theorem compact_smooth_extension {K U : Set _root_.OAI.Yau.Jets.Coord} (hK : IsCompact K)
    (hU : IsOpen U) (hKU : K ⊆ U) (f : _root_.OAI.Yau.Jets.Coord → F) (hf : ContDiffOn ℝ ∞ f U) :
    ∃ G : _root_.OAI.Yau.Jets.Coord → F, ContDiff ℝ ∞ G ∧ HasCompactSupport G ∧ tsupport G ⊆ U ∧
      ∀ x ∈ K, G =ᶠ[𝓝 x] f := by
  obtain ⟨b,hb,hbc,hbU,hbr,hb1⟩ := compact_smooth_cutoff hK hU hKU
  let G := fun x ↦ b x • f x
  have hG : ContDiff ℝ ∞ G := by
    rw [contDiff_iff_contDiffAt]
    intro x
    by_cases hx : x ∈ tsupport b
    · exact hb.contDiffAt.smul (hf.contDiffAt (hU.mem_nhds (hbU hx)))
    · apply (contDiffAt_const (c := (0:F))).congr_of_eventuallyEq
      filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hx] with z hz
      simp [G,hz]
  have hsupp : tsupport G ⊆ tsupport b := by
    apply closure_mono
    intro x hx hz
    exact hx (by simp [G,hz])
  refine ⟨G,hG,hbc.of_isClosed_subset isClosed_closure hsupp,hsupp.trans hbU,?_⟩
  intro x hx
  filter_upwards [hb1 x hx] with z hz
  simp [G,hz]

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_EnvelopeNestedDomainsLemmas
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Yau.Geometry

open Yau.Jets Set
open scoped Topology

theorem envelope_nested_domains {C P : Set _root_.OAI.Yau.Jets.Coord} (hC : IsCompact C)
    (hP : IsOpen P) (hCP : C ⊆ P) :
    ∃ U Ω : Set _root_.OAI.Yau.Jets.Coord, IsOpen U ∧ IsOpen Ω ∧ C ⊆ U ∧
      IsCompact (closure U) ∧ closure U ⊆ Ω ∧
      IsCompact (closure Ω) ∧ closure Ω ⊆ P := by
  obtain ⟨L,hL,hCL,hLP⟩ := exists_compact_between hC hP hCP
  obtain ⟨M,hM,hLM,hMP⟩ := exists_compact_between hL hP hLP
  have hUL : closure (interior L) ⊆ L := closure_minimal interior_subset hL.isClosed
  have hΩM : closure (interior M) ⊆ M := closure_minimal interior_subset hM.isClosed
  exact ⟨interior L,interior M,isOpen_interior,isOpen_interior,hCL,
    hL.of_isClosed_subset isClosed_closure hUL,hUL.trans hLM,
    hM.of_isClosed_subset isClosed_closure hΩM,hΩM.trans hMP⟩

theorem compact_high_envelope_set (S S0 : _root_.OAI.Yau.Jets.Coord → ℝ) (hS : Continuous S) (hS0 : Continuous S0)
    {C P : Set _root_.OAI.Yau.Jets.Coord} (hC : IsCompact C) (hCP : C ⊆ P) {d : ℝ} (hd : 0 < d)
    (hgap : ∀ x ∈ P, x ∉ C → S x ≤ S0 x-d) :
    IsCompact {x | x ∈ P ∧ S0 x-d/2 ≤ S x} ∧
      {x | x ∈ P ∧ S0 x-d/2 ≤ S x} ⊆ C := by
  have hsub : {x | x ∈ P ∧ S0 x-d/2 ≤ S x} ⊆ C := by
    intro x hx
    by_contra hc
    have hh := hgap x hx.1 hc
    have hl := hx.2
    linarith
  have he : {x | x ∈ P ∧ S0 x-d/2 ≤ S x} = C ∩ {x | S0 x-d/2 ≤ S x} := by
    ext x
    exact ⟨fun hx ↦ ⟨hsub hx,hx.2⟩,fun hx ↦ ⟨hCP hx.1,hx.2⟩⟩
  refine ⟨?_,hsub⟩
  rw [he]
  exact hC.inter_right (isClosed_le (hS0.sub continuous_const) hS)

open Yau.Jets Set Filter
open scoped ContDiff Topology

end Yau.Geometry

end

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_IntrinsicSeedPatch
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Manifold Yau.Geometry Yau.Jets Set Metric
open scoped ContDiff
noncomputable section

lemma intrinsicSeedCoordMetric_eq (A : IntrinsicTensor)
    (hs : ∀ x v w, A x v w = A x w v)
    (hp : ∀ x v, v ≠ 0 → 0 < A x v v) (ρ : Base → ℝ) (hρ : ∀ x, 0 < ρ x) :
    seedCoordMetric (intrinsicChartCoefficient A ρ seedPoint) = intrinsicSeedCoordMetric A ρ := by
  funext x
  change linearMetricPull seedCoordEquiv _ = linearMetricPull seedCoordEquiv _
  rw [Function.comp_apply,intrinsicChartCoefficient_metric A hs hp ρ hρ seedPoint
    (by rw [centeredSphereChart_target]; trivial)]

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_SeedLogExtension
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Yau.Geometry Yau.Jets Filter Set
open scoped ContDiff Topology
noncomputable section

lemma seedCoordBranch_open : IsOpen seedCoordBranch :=
  seedLogDomain_open.preimage (seedChartAmbient_smooth.continuous.comp seedCoordEquiv.continuous)

lemma seedCoordReal_smoothOn : ContDiffOn ℝ ∞ seedCoordReal seedCoordBranch := by
  intro x hx
  exact ((seedRealChart_smoothAt hx).comp x seedCoordEquiv.contDiff.contDiffAt).contDiffWithinAt

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_SeedCoordPatchTopology
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Yau.Geometry Yau.Jets Set Metric
open scoped Topology
noncomputable section

lemma seedCoordPatch_open (r : ℝ) : IsOpen (seedCoordPatch r) :=
  isOpen_ball.preimage seedCoordEquiv.continuous

lemma seedCoordPatch_closure_subset (r : ℝ) :
    closure (seedCoordPatch r) ⊆ seedCoordEquiv ⁻¹' closedBall (0 : BaseModel) r :=
  closure_minimal (preimage_mono ball_subset_closedBall)
    (isClosed_closedBall.preimage seedCoordEquiv.continuous)

lemma seedCoordPatch_compactClosure (r : ℝ) : IsCompact (closure (seedCoordPatch r)) := by
  have hc : IsCompact (seedCoordEquiv ⁻¹' closedBall (0 : BaseModel) r) := by
    have he : seedCoordEquiv ⁻¹' closedBall (0 : BaseModel) r =
        seedCoordEquiv.symm '' closedBall (0 : BaseModel) r := by
      ext x
      constructor
      · intro hx
        exact ⟨seedCoordEquiv x,hx,seedCoordEquiv.symm_apply_apply x⟩
      · rintro ⟨y,hy,rfl⟩
        simpa using hy
    rw [he]
    exact (isCompact_closedBall _ _).image seedCoordEquiv.symm.continuous
  exact hc.of_isClosed_subset isClosed_closure (seedCoordPatch_closure_subset r)

lemma seedCoordCube_image {a : ℝ} {x : _root_.OAI.Yau.Jets.Coord} (hx : x ∈ seedCoordCube a) :
    seedCoordEquiv x ∈ seedCoordinateCube a := by
  intro i
  change |x i| ≤ a
  exact abs_le.mpr ⟨hx.1 i,hx.2 i⟩

lemma seedCoordCube_subset {a r : ℝ} (h : seedCoordinateCube a ⊆ ball (0 : BaseModel) r) :
    seedCoordCube a ⊆ seedCoordPatch r := fun _ hx ↦ h (seedCoordCube_image hx)

lemma seedCoordCube_Icc (a : ℝ) :
    Icc (fun _ : Fin 4 ↦ -a) (fun _ : Fin 4 ↦ -a+2*a) = seedCoordCube a := by
  congr 1
  funext i
  ring

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_LocalEnvelopeDomains
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Yau.Jets Set Filter
open scoped ContDiff Topology
noncomputable section

theorem local_envelope_nested_domains (S S0 : _root_.OAI.Yau.Jets.Coord → ℝ)
    {P B C : Set _root_.OAI.Yau.Jets.Coord} (hP : IsOpen P) (hPc : IsCompact (closure P))
    (hB : IsOpen B) (hPB : closure P ⊆ B)
    (hS : ContDiffOn ℝ ∞ S B) (hS0 : ContDiffOn ℝ ∞ S0 B)
    (hC : IsCompact C) (hCP : C ⊆ P) {d : ℝ} (hd : 0 < d)
    (hgap : ∀ x ∈ P, x ∉ C → S x ≤ S0 x-d) :
    ∃ U Ω : Set _root_.OAI.Yau.Jets.Coord, IsOpen U ∧ IsOpen Ω ∧ C ⊆ U ∧
      IsCompact (closure U) ∧ closure U ⊆ Ω ∧
      IsCompact (closure Ω) ∧ closure Ω ⊆ P ∧
      IsCompact {x | x ∈ P ∧ S0 x-d/2 ≤ S x} ∧
      {x | x ∈ P ∧ S0 x-d/2 ≤ S x} ⊆ U ∧
      (∀ x ∈ P, x ∉ U → S x ≤ S0 x-d) := by
  obtain ⟨R,hR,hRc,hRB,hRe⟩ := compact_smooth_extension hPc hB hPB S hS
  obtain ⟨R0,hR0,hR0c,hR0B,hR0e⟩ := compact_smooth_extension hPc hB hPB S0 hS0
  have hReq (x : _root_.OAI.Yau.Jets.Coord) (hx : x ∈ P) : R x = S x := (hRe x (subset_closure hx)).eq_of_nhds
  have hR0eq (x : _root_.OAI.Yau.Jets.Coord) (hx : x ∈ P) : R0 x = S0 x := (hR0e x (subset_closure hx)).eq_of_nhds
  have hg : ∀ x ∈ P, x ∉ C → R x ≤ R0 x-d := by
    intro x hx hxc
    rw [hReq x hx,hR0eq x hx]
    exact hgap x hx hxc
  obtain ⟨hQ,hQC⟩ := compact_high_envelope_set R R0 hR.continuous hR0.continuous hC hCP hd hg
  have he : {x | x ∈ P ∧ R0 x-d/2 ≤ R x} = {x | x ∈ P ∧ S0 x-d/2 ≤ S x} := by
    ext x
    by_cases hx : x ∈ P
    · simp only [mem_ofPred_eq,hx,true_and,hReq x hx,hR0eq x hx]
    · simp [hx]
  rw [he] at hQ hQC
  obtain ⟨U,Ω,hU,hΩ,hCU,hUc,hUΩ,hΩc,hΩP⟩ := envelope_nested_domains hC hP hCP
  exact ⟨U,Ω,hU,hΩ,hCU,hUc,hUΩ,hΩc,hΩP,hQ,hQC.trans hCU,
    fun x hx hxU ↦ hgap x hx (fun hc ↦ hxU (hCU hc))⟩

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_PlacedEnvelopeDomains
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Yau.Geometry Yau.Jets Set Metric Filter MeasureTheory
open scoped ContDiff Topology
noncomputable section

theorem SeedEnvelopePlaced.domains {g : _root_.OAI.Yau.Jets.Coord → _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ}
    {r a : ℝ} {K : Set _root_.OAI.Yau.Jets.Coord} {T : ℝ}
    (h : SeedEnvelopePlaced g r a K T) : Nonempty (PlacedEnvelopeData g r a K T) := by
  obtain ⟨S,d,C,V,hd,hS,hC,hCP,hinner,hig,hog,hV,hPV,hVB,had,hgain⟩ := h
  have hPB := hPV.trans hVB
  obtain ⟨U,Ω,hU,hΩ,hCU,hUc,hUΩ,hΩc,hΩP,hQ,hQU,hout⟩ :=
    local_envelope_nested_domains S seedCoordReal (seedCoordPatch_open r)
      (seedCoordPatch_compactClosure r) seedCoordBranch_open hPB hS seedCoordReal_smoothOn
      hC hCP hd (fun x _ hx ↦ hog x hx)
  exact ⟨⟨S,d,U,Ω,V,C,hd,hS,hC,hCP,hinner,hig,hog,hV,hPV,hVB,had,hgain,
    hU,hΩ,hCU,hUc,hUΩ,hΩc,hΩP,hQ,hQU⟩⟩

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_SeedNoncriticalPlacement
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Yau.Geometry Yau.Jets Set Metric Filter MeasureTheory
open scoped ContDiff Topology
noncomputable section
attribute [local instance] clmTopology clmAdd clmModule

lemma seedCoordImag_fderiv_ne {x : _root_.OAI.Yau.Jets.Coord}
    (hx : seedChartAmbient (seedCoordEquiv x) ∈ seedLogDomain)
    (hn : fderiv ℝ seedImagChart (seedCoordEquiv x) ≠ 0) :
    fderiv ℝ seedCoordImag x ≠ 0 := by
  rw [seedCoordImag,fderiv_comp x
    ((seedImagChart_smoothAt hx).differentiableAt (by simp))
    seedCoordEquiv.differentiableAt,seedCoordEquiv.fderiv]
  intro h
  apply hn
  ext v
  have he := congrArg (fun L : _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ ↦ L (seedCoordEquiv.symm v)) h
  simpa using he

theorem seed_coefficient_noncritical_placement : ∃ r a δ : ℝ, 0 < r ∧ 0 < a ∧ 0 < δ ∧
    seedCoordCube a ⊆ seedCoordPatch r ∧
    closure (seedCoordPatch r) ⊆ seedCoordBranch ∧
    (∀ x ∈ closure (seedCoordPatch r), fderiv ℝ seedCoordImag x ≠ 0) ∧
    ∀ c : BaseModel → CoefficientPoint BaseModel, ContDiff ℝ ∞ c →
      (∀ y (α : BaseModel →L[ℝ] ℝ), α ≠ 0 → 0 < α ((c y).1 α)) →
      (∀ y (α β : BaseModel →L[ℝ] ℝ), α ((c y).1 β) = β ((c y).1 α)) →
      (∀ y, 0 < (c y).2) →
      (∀ y ∈ closedBall (0 : BaseModel) r,
        dist ((c y,fderiv ℝ c y) : CoefficientFirstJet BaseModel) (roundCoefficientJet y) < δ) →
      ∀ K : Set _root_.OAI.Yau.Jets.Coord, IsCompact K → K ⊆ seedCoordPatch r →
      ∀ T : ℝ, SeedEnvelopePlaced (seedCoordMetric c) r a K T := by
  obtain ⟨r,a,δ,hr,ha,hδ,hK,hsub,hbranch,hseed⟩ := seed_envelope_Coord_patch
  have hDP := seedCoordCube_subset hsub
  have hPB : closure (seedCoordPatch r) ⊆ seedCoordBranch := fun x hx ↦
    (hbranch _ (seedCoordPatch_closure_subset r hx)).1
  refine ⟨r,a,δ,hr,ha,hδ,hDP,hPB,?_,?_⟩
  · intro x hx
    exact seedCoordImag_fderiv_ne (hbranch _ (seedCoordPatch_closure_subset r hx)).1
      (hbranch _ (seedCoordPatch_closure_subset r hx)).2
  intro c hc hp hs hρ hclose K hK hKP T
  have hsa : sourceDirectionalAdmissibleOn (seedCoordMetric c) seedCoordReal
      (closure (seedCoordPatch r)) := by
    intro x hx
    obtain ⟨hpos,hn,v,hpv,hv,hstr⟩ := hseed c
      (fun y _ ↦ hc.differentiable (by simp) y) (fun y _ ↦ hp y)
      (fun y _ ↦ hρ y) hclose x (seedCoordPatch_closure_subset r hx)
    exact ⟨hn,v,hv,hpv,hstr⟩
  have he := exists_placed_envelope (fun _ ↦ -a) (by positivity : 0 < 2*a)
    (seedCoordMetric c) seedCoordReal (seedCoordPatch_open r) (seedCoordPatch_compactClosure r)
    seedCoordBranch_open hPB (by simpa only [seedCoordCube_Icc] using hDP) hK hKP
    (seedCoordMetric_smooth c hc hp).contDiffOn seedCoordReal_smoothOn
    (fun x _ ↦ seedCoordMetric_positive c hp hρ x)
    (fun x _ ↦ seedCoordMetric_symmetric c hp hs x) hsa T
  simpa only [SeedEnvelopePlaced,seedCoordCube_Icc] using he

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_IntrinsicNoncriticalPlacement
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Manifold Yau.Geometry Yau.Jets Set Metric
open scoped ContDiff
noncomputable section
attribute [local instance] clmTopology clmAdd clmModule

theorem intrinsic_noncritical_envelope_placement : ∃ r a δ : ℝ, 0 < r ∧ 0 < a ∧ 0 < δ ∧
    seedCoordCube a ⊆ seedCoordPatch r ∧ closure (seedCoordPatch r) ⊆ seedCoordBranch ∧
    (∀ x ∈ closure (seedCoordPatch r), fderiv ℝ seedCoordImag x ≠ 0) ∧
    ∀ (A : IntrinsicTensor), IntrinsicTensorSmooth A →
      (∀ x v w, A x v w = A x w v) → (∀ x v, v ≠ 0 → 0 < A x v v) →
      ∀ ρ : Base → ℝ, ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ ρ → (∀ x, 0 < ρ x) →
      (∀ y ∈ closedBall (0 : BaseModel) r,
        dist ((intrinsicChartCoefficient A ρ seedPoint y,
          fderiv ℝ (intrinsicChartCoefficient A ρ seedPoint) y) : CoefficientFirstJet BaseModel)
          (roundCoefficientJet y) < δ) →
      ∀ K : Set _root_.OAI.Yau.Jets.Coord, IsCompact K → K ⊆ seedCoordPatch r →
      ∀ T : ℝ, SeedEnvelopePlaced (intrinsicSeedCoordMetric A ρ) r a K T := by
  obtain ⟨r,a,δ,hr,ha,hδ,hDP,hPB,hq,hplace⟩ := seed_coefficient_noncritical_placement
  refine ⟨r,a,δ,hr,ha,hδ,hDP,hPB,hq,?_⟩
  intro A hA hs hp ρ hρ hρp hclose K hK hKP T
  have hc : ContDiff ℝ ∞ (intrinsicChartCoefficient A ρ seedPoint) := by
    rw [contDiff_iff_contDiffAt]
    intro y
    exact intrinsicChartCoefficient_smoothAt A hA hs hp ρ hρ seedPoint
      (by rw [centeredSphereChart_target]; trivial)
  have hh := hplace (intrinsicChartCoefficient A ρ seedPoint) hc
    (fun y ↦ intrinsicChartCoefficient_positive A hs hp ρ seedPoint
      (by rw [centeredSphereChart_target]; trivial))
    (intrinsicChartCoefficient_symmetric A hs ρ seedPoint)
    (fun y ↦ hρp _) hclose K hK hKP T
  simpa only [intrinsicSeedCoordMetric_eq A hs hp ρ hρp] using hh

theorem intrinsic_noncritical_placed_data_oai : ∃ r a δ : ℝ, 0 < r ∧ 0 < a ∧ 0 < δ ∧
    seedCoordCube a ⊆ seedCoordPatch r ∧ closure (seedCoordPatch r) ⊆ seedCoordBranch ∧
    (∀ x ∈ closure (seedCoordPatch r), fderiv ℝ seedCoordImag x ≠ 0) ∧
    ∀ (A : IntrinsicTensor), IntrinsicTensorSmooth A →
      (∀ x v w, A x v w = A x w v) → (∀ x v, v ≠ 0 → 0 < A x v v) →
      ∀ ρ : Base → ℝ, ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ ρ → (∀ x, 0 < ρ x) →
      (∀ y ∈ closedBall (0 : BaseModel) r,
        dist ((intrinsicChartCoefficient A ρ seedPoint y,
          fderiv ℝ (intrinsicChartCoefficient A ρ seedPoint) y) : CoefficientFirstJet BaseModel)
          (roundCoefficientJet y) < δ) →
      ∀ K : Set _root_.OAI.Yau.Jets.Coord, IsCompact K → K ⊆ seedCoordPatch r →
      ∀ T : ℝ, Nonempty (PlacedEnvelopeData (intrinsicSeedCoordMetric A ρ) r a K T) := by
  obtain ⟨r,a,δ,hr,ha,hδ,hDP,hPB,hq,hplace⟩ := intrinsic_noncritical_envelope_placement
  refine ⟨r,a,δ,hr,ha,hδ,hDP,hPB,hq,?_⟩
  intro A hA hs hp ρ hρ hρp hclose K hK hKP T
  exact (hplace A hA hs hp ρ hρ hρp hclose K hK hKP T).domains

end
end Yau.Target

end OAI
end

theorem solution : type_of% @OAI.Yau.Target.intrinsic_noncritical_placed_data_oai := @OAI.Yau.Target.intrinsic_noncritical_placed_data_oai
