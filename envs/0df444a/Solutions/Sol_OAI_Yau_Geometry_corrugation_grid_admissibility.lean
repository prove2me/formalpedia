-- Prove2me | solution 1 for OAI.Yau.Geometry.corrugation_grid_admissibility
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T00:29:48.072367+00:00
-- url     : https://prove2.me/submissions/04d1274a-a423-4164-a3ed-e9a581908757

import Mathlib
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Abs
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.Calculus.TaylorIntegral
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.Finsupp.Weight
import Mathlib.Data.List.FinRange
import Mathlib.Data.Matrix.Basic
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.LinearAlgebra.Basis.SMul
import Mathlib.LinearAlgebra.Determinant
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.LinearAlgebra.QuadraticForm.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
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
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.UniformSpace.HeineCantor
import Definitions.Def_OAIQ237Ny002
import Theorems.Thm_OAI_Yau_Geometry_corrugation_actual_high_admissibility
import Theorems.Thm_OAI_Yau_Geometry_corrugation_actual_low_old_margin
import Theorems.Thm_OAI_Yau_Geometry_corrugation_actual_low_radial
import Theorems.Thm_OAI_Yau_Geometry_corrugation_actual_metric_unit_errors

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

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_EnvelopeContactJet
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Jets
open MvPolynomial
open scoped ContDiff
noncomputable section

lemma coord_expansion (x : Coord) : x = ∑ i, x i • Pi.single i (1:ℝ) := by
  ext j
  simp [Finset.sum_apply, Pi.single_apply, mul_ite]

end
end Yau.Jets

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Charts_ChartedEnvelope
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open scoped ContDiff
open Yau.Jets
noncomputable section
attribute [local instance] clmTopology clmAdd clmModule

lemma metricGradient_pair (g : _root_.OAI.Yau.Jets.Coord → _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ) (S : _root_.OAI.Yau.Jets.Coord → ℝ)
    (y : _root_.OAI.Yau.Jets.Coord) (hp : ∀ v, v ≠ 0 → 0 < g y v v) (v : _root_.OAI.Yau.Jets.Coord) :
    g y (metricGradient g S y) v = fderiv ℝ S y v := by
  have hi : ContinuousLinearMap.inverse (g y) = (positiveMetricEquiv (g y) hp).symm.toContinuousLinearMap :=
    ContinuousLinearMap.inverse_equiv (positiveMetricEquiv (g y) hp)
  change positiveMetricEquiv (g y) hp (ContinuousLinearMap.inverse (g y) (fderiv ℝ S y)) v = _
  rw [hi, ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.apply_symm_apply]

lemma sourceHessian_apply (g : _root_.OAI.Yau.Jets.Coord → _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ) (S : _root_.OAI.Yau.Jets.Coord → ℝ)
    (y u v : _root_.OAI.Yau.Jets.Coord) : sourceHessian g S y u v =
      fderiv ℝ (fderiv ℝ S) y u v - fderiv ℝ S y (metricConnection (g y) (fderiv ℝ g y) u v) := rfl

lemma orthonormal_frame_pair (g : _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ) (e : _root_.OAI.Yau.Jets.Coord ≃L[ℝ] _root_.OAI.Yau.Jets.Coord)
    (he : ∀ i j, g (e (Pi.single i 1)) (e (Pi.single j 1)) = if i = j then 1 else 0)
    (i : Fin 4) (x : _root_.OAI.Yau.Jets.Coord) : g (e (Pi.single i 1)) (e x) = x i := by
  have hx : e x = ∑ j, x j • e (Pi.single j 1) := by
    conv_lhs => rw [coord_expansion x]
    simp
  rw [hx]
  simp [map_sum, he, mul_ite]

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Charts_CorrugationFrozenFrame
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Yau.Jets Set Metric
noncomputable section

lemma frozenFrameCovector_apply (e : _root_.OAI.Yau.Jets.Coord ≃L[ℝ] _root_.OAI.Yau.Jets.Coord) (i : Fin 4) (v : _root_.OAI.Yau.Jets.Coord) :
    frozenFrameCovector e i v = e.symm v i := rfl

lemma frozenFrameCovector_axis (e : _root_.OAI.Yau.Jets.Coord ≃L[ℝ] _root_.OAI.Yau.Jets.Coord) (i j : Fin 4) :
    frozenFrameCovector e i (e (Pi.single j 1)) = if i=j then 1 else 0 := by
  simp [frozenFrameCovector,Pi.single_apply]

lemma frozenFrameCovector_metric (g : _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ)
    (e : _root_.OAI.Yau.Jets.Coord ≃L[ℝ] _root_.OAI.Yau.Jets.Coord)
    (he : ∀ i j, g (e (Pi.single i 1)) (e (Pi.single j 1)) = if i=j then 1 else 0)
    (i : Fin 4) (v : _root_.OAI.Yau.Jets.Coord) :
    frozenFrameCovector e i v = g (e (Pi.single i 1)) v := by
  rw [frozenFrameCovector_apply,← orthonormal_frame_pair g e he i (e.symm v)]
  simp

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Charts_CorrugationFrameBounds
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Yau.Jets
noncomputable section

lemma metric_unit_coordinate_bound (g : _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ)
    {c : ℝ} (hc : 0 < c) (hg : ∀ v : _root_.OAI.Yau.Jets.Coord, c*‖v‖^2 ≤ g v v)
    (v : _root_.OAI.Yau.Jets.Coord) (hv : g v v = 1) : ‖v‖ ≤ 1+c⁻¹ := by
  have h := hg v
  rw [hv] at h
  have hi := mul_inv_cancel₀ hc.ne'
  nlinarith [sq_nonneg (‖v‖-1),norm_nonneg v,inv_pos.mpr hc]

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_CorrugationAffineJets
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open scoped ContDiff
noncomputable section
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

lemma affine_scalar_first (f : F → ℝ) (hf : ContDiff ℝ ∞ f)
    (L : E →L[ℝ] F) (y x v : E) :
    fderiv ℝ (fun z ↦ f (L (z-y))) x v = fderiv ℝ f (L (x-y)) (L v) := by
  have h := (hf.differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) _).hasFDerivAt.comp x
    (L.hasFDerivAt.comp x ((hasFDerivAt_id x).sub_const y))
  simpa [Function.comp_def] using congrArg (fun A : E →L[ℝ] ℝ ↦ A v) h.fderiv

lemma affine_scalar_second (f : F → ℝ) (hf : ContDiff ℝ ∞ f)
    (L : E →L[ℝ] F) (y x u v : E) :
    fderiv ℝ (fderiv ℝ (fun z ↦ f (L (z-y)))) x u v =
      fderiv ℝ (fderiv ℝ f) (L (x-y)) (L u) (L v) := by
  have hcomp : ContDiff ℝ ∞ (fun z ↦ f (L (z-y))) :=
    hf.comp (L.contDiff.comp (contDiff_id.sub contDiff_const))
  have hd := (hcomp.fderiv_right (m := ∞) (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) x
  have he := congrArg (fun A : E →L[ℝ] ℝ ↦ A u)
    (hd.hasFDerivAt.clm_apply (hasFDerivAt_const v x)).fderiv
  simp only [ContinuousLinearMap.comp_zero,zero_add,ContinuousLinearMap.flip_apply] at he
  rw [← he]
  have hfun : (fun z ↦ fderiv ℝ (fun w ↦ f (L (w-y))) z v) =
      (fun z ↦ fderiv ℝ f (L (z-y)) (L v)) :=
    funext (fun z ↦ affine_scalar_first f hf L y z v)
  rw [hfun]
  have hdf := ((hf.fderiv_right (m := ∞) (by simp)).differentiable (by simp) (L (x-y))).hasFDerivAt
  have h := (hdf.comp x (L.hasFDerivAt.comp x ((hasFDerivAt_id x).sub_const y))).clm_apply
    (hasFDerivAt_const (L v) x)
  simpa [Function.comp_def] using congrArg (fun A : E →L[ℝ] ℝ ↦ A u) h.fderiv

lemma scalar_product_second (f k : E → ℝ) (hf : ContDiff ℝ ∞ f)
    (hk : ContDiff ℝ ∞ k) (x u v : E) :
    fderiv ℝ (fderiv ℝ (fun z ↦ f z*k z)) x u v =
      fderiv ℝ (fderiv ℝ f) x u v*k x +
      fderiv ℝ f x v*fderiv ℝ k x u +
      fderiv ℝ f x u*fderiv ℝ k x v +
      f x*fderiv ℝ (fderiv ℝ k) x u v := by
  have hd := (((hf.mul hk).fderiv_right (m := ∞) (by simp)).differentiable (by simp) x)
  have he := congrArg (fun A : E →L[ℝ] ℝ ↦ A u)
    (hd.hasFDerivAt.clm_apply (hasFDerivAt_const v x)).fderiv
  simp only [ContinuousLinearMap.comp_zero,zero_add,ContinuousLinearMap.flip_apply] at he
  rw [← he]
  have hfun : (fun z ↦ fderiv ℝ (fun w ↦ f w*k w) z v) =
      (fun z ↦ fderiv ℝ f z v*k z+f z*fderiv ℝ k z v) := by
    funext z
    change fderiv ℝ (f*k) z v = _
    rw [fderiv_mul (hf.differentiable (by simp) z) (hk.differentiable (by simp) z)]
    simp
    ring
  rw [hfun]
  have df := (((hf.fderiv_right (m := ∞) (by simp)).differentiable (by simp) x).hasFDerivAt.clm_apply
    (hasFDerivAt_const v x))
  have dk := (((hk.fderiv_right (m := ∞) (by simp)).differentiable (by simp) x).hasFDerivAt.clm_apply
    (hasFDerivAt_const v x))
  change fderiv ℝ ((fun z ↦ fderiv ℝ f z v)*k+f*(fun z ↦ fderiv ℝ k z v)) x u = _
  rw [((df.mul (hk.differentiable (by simp) x).hasFDerivAt).add
    ((hf.differentiable (by simp) x).hasFDerivAt.mul dk)).fderiv]
  simp
  ring

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_CorrugationDiskWell
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Real Set MeasureTheory
open scoped ContDiff
noncomputable section

lemma flatPrimitive_hasDerivAt (t : ℝ) : HasDerivAt flatPrimitive (expNegInvGlue t) t := by
  have hc := (expNegInvGlue.contDiff (n := ⊤)).continuous
  exact intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable 0 t)
    (hc.stronglyMeasurableAtFilter _ _) hc.continuousAt

lemma flatPrimitive_smooth : ContDiff ℝ ∞ flatPrimitive := by
  apply contDiff_infty_iff_deriv.mpr
  refine ⟨fun t ↦ (flatPrimitive_hasDerivAt t).differentiableAt,?_⟩
  have he : deriv flatPrimitive = expNegInvGlue := funext (fun t ↦ (flatPrimitive_hasDerivAt t).deriv)
  rw [he]
  exact expNegInvGlue.contDiff

lemma flatPrimitive_zero {t : ℝ} (ht : t ≤ 0) : flatPrimitive t = 0 := by
  unfold flatPrimitive
  calc
    (∫ s in (0:ℝ)..t, expNegInvGlue s) = ∫ s in (0:ℝ)..t, (0:ℝ) := by
      apply intervalIntegral.integral_congr
      intro s hs
      rw [uIcc_of_ge ht] at hs
      exact expNegInvGlue.zero_of_nonpos hs.2
    _ = 0 := by simp

lemma corrugationDiskWell_smooth (a R : ℝ) : ContDiff ℝ ∞ (corrugationDiskWell a R) :=
  contDiff_const.mul (flatPrimitive_smooth.comp
    ((contDiff_const.sub (contDiff_fst.pow 2)).sub (contDiff_snd.pow 2)))

lemma corrugationDiskWell_zero {a R : ℝ} {z : ℝ × ℝ} (hz : R^2 ≤ z.1^2+z.2^2) :
    corrugationDiskWell a R z = 0 := by
  unfold corrugationDiskWell
  rw [flatPrimitive_zero (by linarith),mul_zero]

lemma corrugationDiskWell_compactSupport (a : ℝ) {R : ℝ} (hR : 0 ≤ R) :
    HasCompactSupport (corrugationDiskWell a R) := by
  have hsub : Function.support (corrugationDiskWell a R) ⊆
      (Icc (-R) R) ×ˢ (Icc (-R) R) := by
    intro z hz
    have hn : z.1^2+z.2^2 < R^2 := by
      by_contra h
      exact hz (corrugationDiskWell_zero (le_of_not_gt h))
    constructor <;> constructor <;> nlinarith [sq_nonneg z.1,sq_nonneg z.2]
  exact (isCompact_Icc.prod isCompact_Icc).of_isClosed_subset isClosed_closure
    (closure_minimal hsub (isClosed_Icc.prod isClosed_Icc))

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_CorrugationPeriodicWell
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Real Set Filter
open scoped ContDiff Topology
noncomputable section

lemma corrugation_translate_zero (a : ℝ) (N : ℕ) (z : ℝ × ℝ)
    (hz₁ : |z.1| < (N:ℝ)-1) (hz₂ : |z.2| < (N:ℝ)-1)
    (k : ℤ × ℤ) (hk : k ∉ Finset.Icc (-(N:ℤ),-(N:ℤ)) ((N:ℤ),(N:ℤ))) :
    corrugationDiskWell a (1/4) (z.1-(k.1:ℝ),z.2-(k.2:ℝ)) = 0 := by
  apply corrugationDiskWell_zero
  have hz1 := abs_lt.mp hz₁
  have hz2 := abs_lt.mp hz₂
  simp only [Finset.mem_Icc,Prod.le_def,not_and_or,not_le] at hk
  rcases hk with (hk | hk) | (hk | hk)
  all_goals
    have hk' := (Int.cast_lt (R := ℝ)).mpr hk
    push_cast at hk'
    dsimp only
    nlinarith [sq_nonneg (z.1-(k.1:ℝ)),sq_nonneg (z.2-(k.2:ℝ))]

lemma corrugationPeriodicWell_eq_sum (a : ℝ) (N : ℕ) (z : ℝ × ℝ)
    (hz₁ : |z.1| < (N:ℝ)-1) (hz₂ : |z.2| < (N:ℝ)-1) :
    corrugationPeriodicWell a z =
      ∑ k ∈ Finset.Icc (-(N:ℤ),-(N:ℤ)) ((N:ℤ),(N:ℤ)),
        corrugationDiskWell a (1/4) (z.1-(k.1:ℝ),z.2-(k.2:ℝ)) := by
  apply tsum_eq_sum
  intro k hk
  exact corrugation_translate_zero a N z hz₁ hz₂ k hk

lemma corrugationPeriodicWell_smooth (a : ℝ) : ContDiff ℝ ∞ (corrugationPeriodicWell a) := by
  apply contDiff_iff_contDiffAt.mpr
  intro z
  obtain ⟨N,hN⟩ := exists_nat_gt (max |z.1| |z.2|+1)
  have hz₁ : |z.1| < (N:ℝ)-1 := by have := le_max_left |z.1| |z.2|; linarith
  have hz₂ : |z.2| < (N:ℝ)-1 := by have := le_max_right |z.1| |z.2|; linarith
  have hsum : ContDiff ℝ ∞ (fun w : ℝ × ℝ ↦
      ∑ k ∈ Finset.Icc (-(N:ℤ),-(N:ℤ)) ((N:ℤ),(N:ℤ)),
        corrugationDiskWell a (1/4) (w.1-(k.1:ℝ),w.2-(k.2:ℝ))) := by
    apply ContDiff.sum
    intro k _
    exact (corrugationDiskWell_smooth a (1/4)).comp
      ((contDiff_fst.sub contDiff_const).prodMk (contDiff_snd.sub contDiff_const))
  apply hsum.contDiffAt.congr_of_eventuallyEq
  have h1 : ∀ᶠ w : ℝ × ℝ in 𝓝 z, |w.1| < (N:ℝ)-1 :=
    (continuous_fst.abs.continuousAt).eventually_lt_const hz₁
  have h2 : ∀ᶠ w : ℝ × ℝ in 𝓝 z, |w.2| < (N:ℝ)-1 :=
    (continuous_snd.abs.continuousAt).eventually_lt_const hz₂
  filter_upwards [h1,h2] with w hw1 hw2
  exact corrugationPeriodicWell_eq_sum a N w hw1 hw2

lemma corrugationPeriodicWell_periodic (a : ℝ) (m : ℤ × ℤ) (z : ℝ × ℝ) :
    corrugationPeriodicWell a (z.1+(m.1:ℝ),z.2+(m.2:ℝ)) = corrugationPeriodicWell a z := by
  unfold corrugationPeriodicWell
  have h := (Equiv.addRight m).tsum_eq
    (fun k : ℤ × ℤ ↦ corrugationDiskWell a (1/4) (z.1+(m.1:ℝ)-(k.1:ℝ),z.2+(m.2:ℝ)-(k.2:ℝ)))
  simpa only [Equiv.coe_addRight,Prod.fst_add,Prod.snd_add,Int.cast_add,add_sub_add_right_eq_sub] using h.symm

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_CorrugationPeriodicCell
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Real Set Filter
open scoped ContDiff Topology
noncomputable section

lemma nonzero_integer_shift_square (x : ℝ) (hx : |x| ≤ 1/2) (k : ℤ) (hk : k ≠ 0) :
    (1/4:ℝ) ≤ (x-(k:ℝ))^2 := by
  have hx' := abs_le.mp hx
  rcases lt_or_gt_of_ne hk with hk | hk
  · have hk1 : k ≤ -1 := by omega
    have hkR : (k:ℝ) ≤ -1 := by exact_mod_cast hk1
    nlinarith
  · have hk1 : 1 ≤ k := by omega
    have hkR : 1 ≤ (k:ℝ) := by exact_mod_cast hk1
    nlinarith

lemma corrugationPeriodicWell_cell (a : ℝ) (z : ℝ × ℝ)
    (hz₁ : |z.1| ≤ 1/2) (hz₂ : |z.2| ≤ 1/2) :
    corrugationPeriodicWell a z = corrugationDiskWell a (1/4) z := by
  unfold corrugationPeriodicWell
  rw [tsum_eq_single (0 : ℤ × ℤ)]
  · simp
  · intro k hk
    apply corrugationDiskWell_zero
    have h : k.1 ≠ 0 ∨ k.2 ≠ 0 := by
      by_contra h
      simp only [not_or,not_not] at h
      exact hk (Prod.ext h.1 h.2)
    rcases h with h | h
    · have hs := nonzero_integer_shift_square z.1 hz₁ k.1 h
      dsimp only
      nlinarith [sq_nonneg (z.2-(k.2:ℝ))]
    · have hs := nonzero_integer_shift_square z.2 hz₂ k.2 h
      dsimp only
      nlinarith [sq_nonneg (z.1-(k.1:ℝ))]

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_CorrugationDiskJets
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Real Set
open scoped ContDiff
noncomputable section

lemma corrugationDiskWell_hasFDerivAt (a R : ℝ) (z : ℝ × ℝ) :
    HasFDerivAt (corrugationDiskWell a R)
      ((a*expNegInvGlue (R^2-z.1^2-z.2^2)) • planeRadialCovector z) z := by
  have hd := ((hasFDerivAt_const (R^2) z).sub
    ((ContinuousLinearMap.fst ℝ ℝ ℝ).hasFDerivAt.pow 2)).sub
    ((ContinuousLinearMap.snd ℝ ℝ ℝ).hasFDerivAt.pow 2)
  have h := ((flatPrimitive_hasDerivAt (R^2-z.1^2-z.2^2)).comp_hasFDerivAt z hd).const_mul (-(a/2))
  change HasFDerivAt (corrugationDiskWell a R) _ z at h
  convert! h using 1
  all_goals try with_reducible_and_instances rfl
  ext <;> simp [planeRadialCovector] <;> ring

lemma corrugationDiskWell_fderiv (a R : ℝ) (z v : ℝ × ℝ) :
    fderiv ℝ (corrugationDiskWell a R) z v =
      a*expNegInvGlue (R^2-z.1^2-z.2^2)*(z.1*v.1+z.2*v.2) := by
  rw [(corrugationDiskWell_hasFDerivAt a R z).fderiv]
  rfl

lemma corrugationDiskWell_direction_hasFDerivAt (a R : ℝ) (z v : ℝ × ℝ) :
    HasFDerivAt (fun x ↦ fderiv ℝ (corrugationDiskWell a R) x v)
      ((a*expNegInvGlue (R^2-z.1^2-z.2^2)) • planeRadialCovector v -
        (2*a*((R^2-z.1^2-z.2^2)⁻¹)^2*expNegInvGlue (R^2-z.1^2-z.2^2)*
          (z.1*v.1+z.2*v.2)) • planeRadialCovector z) z := by
  have hd := ((hasFDerivAt_const (R^2) z).sub
    ((ContinuousLinearMap.fst ℝ ℝ ℝ).hasFDerivAt.pow 2)).sub
    ((ContinuousLinearMap.snd ℝ ℝ ℝ).hasFDerivAt.pow 2)
  have h := (((expNegInvGlue_hasDerivAt (R^2-z.1^2-z.2^2)).comp_hasFDerivAt z hd).const_mul a).mul
    (((ContinuousLinearMap.fst ℝ ℝ ℝ).hasFDerivAt.mul_const v.1).add
      ((ContinuousLinearMap.snd ℝ ℝ ℝ).hasFDerivAt.mul_const v.2))
  have he : (fun x ↦ fderiv ℝ (corrugationDiskWell a R) x v) =
      (fun x : ℝ × ℝ ↦ a*expNegInvGlue (R^2-x.1^2-x.2^2)*(x.1*v.1+x.2*v.2)) :=
    funext (fun x ↦ corrugationDiskWell_fderiv a R x v)
  rw [he]
  convert! h using 1
  all_goals try with_reducible_and_instances rfl
  ext <;> simp [planeRadialCovector] <;> ring

lemma corrugationDiskWell_second (a R : ℝ) (z u v : ℝ × ℝ) :
    fderiv ℝ (fderiv ℝ (corrugationDiskWell a R)) z u v =
      a*expNegInvGlue (R^2-z.1^2-z.2^2)*(u.1*v.1+u.2*v.2) -
        2*a*((R^2-z.1^2-z.2^2)⁻¹)^2*expNegInvGlue (R^2-z.1^2-z.2^2)*
          (z.1*u.1+z.2*u.2)*(z.1*v.1+z.2*v.2) := by
  have hd := ((corrugationDiskWell_smooth a R).fderiv_right (m := ∞) (by simp)).differentiable (by simp) z
  have he := congrArg (fun L : (ℝ × ℝ) →L[ℝ] ℝ ↦ L u)
    (hd.hasFDerivAt.clm_apply (hasFDerivAt_const v z)).fderiv
  simp only [ContinuousLinearMap.comp_zero,zero_add,ContinuousLinearMap.flip_apply] at he
  rw [← he,(corrugationDiskWell_direction_hasFDerivAt a R z v).fderiv]
  simp [planeRadialCovector]
  ring

lemma corrugationDiskWell_center_second (a R : ℝ) (u v : ℝ × ℝ) :
    fderiv ℝ (fderiv ℝ (corrugationDiskWell a R)) (0:ℝ × ℝ) u v =
      a*expNegInvGlue (R^2)*(u.1*v.1+u.2*v.2) := by
  simp [corrugationDiskWell_second]

lemma corrugationDiskWell_center_positive {a : ℝ} (ha : 0 ≤ a) (R : ℝ) (v : ℝ × ℝ) :
    0 ≤ fderiv ℝ (fderiv ℝ (corrugationDiskWell a R)) (0:ℝ × ℝ) v v := by
  rw [corrugationDiskWell_center_second]
  exact mul_nonneg (mul_nonneg ha (expNegInvGlue.nonneg _))
    (add_nonneg (mul_self_nonneg _) (mul_self_nonneg _))

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_CorrugationRadialJetsLemmas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Yau.Geometry

open Real

lemma radial_angular_decomposition (z u v : ℝ × ℝ) {r : ℝ}
    (hr : r ≠ 0) (hz : r^2=z.1^2+z.2^2) :
    u.1*v.1+u.2*v.2 =
      radialComponent z u r*radialComponent z v r +
      angularComponent z u r*angularComponent z v r := by
  unfold radialComponent angularComponent
  field_simp
  nlinarith only [congrArg (fun t : ℝ ↦ t*(u.1*v.1+u.2*v.2)) hz]

lemma corrugationDiskWell_radial_first (a R : ℝ) (z v : ℝ × ℝ) {r : ℝ}
    (hr : r ≠ 0) (hz : r^2=z.1^2+z.2^2) :
    fderiv ℝ (corrugationDiskWell a R) z v =
      corrugationSlope a R r*radialComponent z v r := by
  rw [corrugationDiskWell_fderiv]
  have ht : R^2-z.1^2-z.2^2 = R^2-r^2 := by linarith
  rw [ht]
  unfold corrugationSlope radialComponent
  field_simp

lemma corrugationDiskWell_radial_second (a R : ℝ) (z u v : ℝ × ℝ) {r : ℝ}
    (hr : r ≠ 0) (hz : r^2=z.1^2+z.2^2) :
    fderiv ℝ (fderiv ℝ (corrugationDiskWell a R)) z u v =
      deriv (corrugationSlope a R) r*radialComponent z u r*radialComponent z v r +
      (corrugationSlope a R r/r)*angularComponent z u r*angularComponent z v r := by
  rw [corrugationDiskWell_second,corrugationSlope_deriv]
  have ht : R^2-z.1^2-z.2^2 = R^2-r^2 := by linarith
  rw [ht,radial_angular_decomposition z u v hr hz]
  have hu : z.1*u.1+z.2*u.2 = r*radialComponent z u r := by
    unfold radialComponent; field_simp
  have hv : z.1*v.1+z.2*v.2 = r*radialComponent z v r := by
    unfold radialComponent; field_simp
  rw [hu,hv]
  unfold corrugationSlope
  field_simp
  ring

open Real Set
open scoped ContDiff

end Yau.Geometry

end

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_LocalizedCorrugation
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Yau.Jets Set Filter Metric
open scoped ContDiff Topology
noncomputable section

lemma localizedCorrugation_smooth (χ : _root_.OAI.Yau.Jets.Coord → ℝ) (f : (ℝ × ℝ) → ℝ)
    (hχ : ContDiff ℝ ∞ χ) (hf : ContDiff ℝ ∞ f)
    (s J R : ℝ) (a b : _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ) (y : _root_.OAI.Yau.Jets.Coord) :
    ContDiff ℝ ∞ (localizedCorrugation χ f s J R a b y) :=
  (contDiff_const.mul (hχ.comp ((corrugationSlowMap R).contDiff.comp
    (contDiff_id.sub contDiff_const)))).mul
    (hf.comp ((corrugationFastMap J a b).contDiff.comp (contDiff_id.sub contDiff_const)))

lemma localizedCorrugation_support (χ : _root_.OAI.Yau.Jets.Coord → ℝ) (f : (ℝ × ℝ) → ℝ)
    (s J : ℝ) {R : ℝ} (a b : _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ) (y : _root_.OAI.Yau.Jets.Coord) :
    tsupport (localizedCorrugation χ f s J R a b y) ⊆
      (fun x ↦ R⁻¹ • (x-y)) ⁻¹' tsupport χ := by
  apply closure_minimal
  · intro x hx
    apply subset_tsupport
    intro hz
    exact hx (by simp [localizedCorrugation,corrugationSlowMap,hz])
  · exact (isClosed_closure : IsClosed (tsupport χ)).preimage ((continuous_const : Continuous (fun _ : _root_.OAI.Yau.Jets.Coord ↦ R⁻¹)).smul (continuous_id.sub continuous_const))

lemma localizedCorrugation_cube (χ : _root_.OAI.Yau.Jets.Coord → ℝ) (f : (ℝ × ℝ) → ℝ)
    (hχ : tsupport χ ⊆ ball (0:_root_.OAI.Yau.Jets.Coord) (1/2))
    (s J : ℝ) {R : ℝ} (hR : 0 < R) (a b : _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ) (y : _root_.OAI.Yau.Jets.Coord) :
    tsupport (localizedCorrugation χ f s J R a b y) ⊆ ball y (R/2) := by
  intro x hx
  have hz := hχ (localizedCorrugation_support χ f s J a b y hx)
  rw [mem_ball,dist_zero_right,norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hR)] at hz
  rw [mem_ball,dist_eq_norm]
  have hr : R*R⁻¹ = 1 := mul_inv_cancel₀ hR.ne'
  nlinarith [mul_lt_mul_of_pos_left hz hR]

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_CorrugationScaledJetsLemmas
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Yau.Geometry

section

open Yau.Jets
open scoped ContDiff

lemma scalar_const_mul_second (c : ℝ) (f : _root_.OAI.Yau.Jets.Coord → ℝ) (hf : ContDiff ℝ ∞ f)
    (x u v : _root_.OAI.Yau.Jets.Coord) :
    fderiv ℝ (fderiv ℝ (fun z ↦ c*f z)) x u v = c*fderiv ℝ (fderiv ℝ f) x u v := by
  simpa using scalar_product_second (fun _ ↦ c) f contDiff_const hf x u v

lemma localizedCorrugation_first (χ : _root_.OAI.Yau.Jets.Coord → ℝ) (f : (ℝ × ℝ) → ℝ)
    (hχ : ContDiff ℝ ∞ χ) (hf : ContDiff ℝ ∞ f)
    (s J R : ℝ) (a b : _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ) (y x v : _root_.OAI.Yau.Jets.Coord) :
    fderiv ℝ (localizedCorrugation χ f s J R a b y) x v =
      (s/J) * (fderiv ℝ χ (corrugationSlowMap R (x-y)) (corrugationSlowMap R v) *
        f (corrugationFastMap J a b (x-y)) +
        χ (corrugationSlowMap R (x-y)) *
          fderiv ℝ f (corrugationFastMap J a b (x-y)) (corrugationFastMap J a b v)) := by
  let A := corrugationSlowMap R
  let B := corrugationFastMap J a b
  have hA : ContDiff ℝ ∞ (fun z ↦ χ (A (z-y))) :=
    hχ.comp (A.contDiff.comp (contDiff_id.sub contDiff_const))
  have hB : ContDiff ℝ ∞ (fun z ↦ f (B (z-y))) :=
    hf.comp (B.contDiff.comp (contDiff_id.sub contDiff_const))
  have he : localizedCorrugation χ f s J R a b y =
      (fun z ↦ (s/J)*(χ (A (z-y))*f (B (z-y)))) := by
    funext z; dsimp [localizedCorrugation,A,B] <;> ring
  rw [he]
  have hd := ((hA.differentiable (by simp) x).hasFDerivAt.mul
    (hB.differentiable (by simp) x).hasFDerivAt).const_mul (s/J)
  change HasFDerivAt (fun z ↦ (s/J)*(χ (A (z-y))*f (B (z-y)))) _ x at hd
  rw [hd.fderiv]
  simp only [smul_apply,add_apply,smul_eq_mul]
  rw [affine_scalar_first χ hχ,affine_scalar_first f hf]
  dsimp [A,B]
  ring

lemma localizedCorrugation_second (χ : _root_.OAI.Yau.Jets.Coord → ℝ) (f : (ℝ × ℝ) → ℝ)
    (hχ : ContDiff ℝ ∞ χ) (hf : ContDiff ℝ ∞ f)
    (s J R : ℝ) (a b : _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ) (y x u v : _root_.OAI.Yau.Jets.Coord) :
    fderiv ℝ (fderiv ℝ (localizedCorrugation χ f s J R a b y)) x u v =
      (s/J) * (
        fderiv ℝ (fderiv ℝ χ) (corrugationSlowMap R (x-y))
          (corrugationSlowMap R u) (corrugationSlowMap R v) * f (corrugationFastMap J a b (x-y)) +
        fderiv ℝ χ (corrugationSlowMap R (x-y)) (corrugationSlowMap R v) *
          fderiv ℝ f (corrugationFastMap J a b (x-y)) (corrugationFastMap J a b u) +
        fderiv ℝ χ (corrugationSlowMap R (x-y)) (corrugationSlowMap R u) *
          fderiv ℝ f (corrugationFastMap J a b (x-y)) (corrugationFastMap J a b v) +
        χ (corrugationSlowMap R (x-y)) *
          fderiv ℝ (fderiv ℝ f) (corrugationFastMap J a b (x-y))
            (corrugationFastMap J a b u) (corrugationFastMap J a b v)) := by
  let A := corrugationSlowMap R
  let B := corrugationFastMap J a b
  have hA : ContDiff ℝ ∞ (fun z ↦ χ (A (z-y))) :=
    hχ.comp (A.contDiff.comp (contDiff_id.sub contDiff_const))
  have hB : ContDiff ℝ ∞ (fun z ↦ f (B (z-y))) :=
    hf.comp (B.contDiff.comp (contDiff_id.sub contDiff_const))
  have he : localizedCorrugation χ f s J R a b y =
      (fun z ↦ (s/J)*(χ (A (z-y))*f (B (z-y)))) := by
    funext z; dsimp [localizedCorrugation,A,B] <;> ring
  rw [he,scalar_const_mul_second _ _ (hA.mul hB),scalar_product_second _ _ hA hB]
  simp only [affine_scalar_first χ hχ,affine_scalar_first f hf,
    affine_scalar_second χ hχ,affine_scalar_second f hf]
  rfl

end

open Yau.Jets Set Filter
open scoped ContDiff Topology
variable {ι : Type*}

lemma finite_sum_support_subset (I : Finset ι) (w : ι → _root_.OAI.Yau.Jets.Coord → ℝ) (U : Set _root_.OAI.Yau.Jets.Coord)
    (hw : ∀ i ∈ I, tsupport (w i) ⊆ U) :
    tsupport (fun x ↦ ∑ i ∈ I, w i x) ⊆ U := by
  classical
  induction I using Finset.induction_on with
  | empty => simp
  | @insert i I hi ih =>
    simp only [Finset.sum_insert hi]
    exact (tsupport_add _ _).trans (union_subset
      (hw i (Finset.mem_insert_self i I)) (ih (fun j hj ↦ hw j (Finset.mem_insert_of_mem hj))))

lemma finite_disjoint_sum_eventually (I : Finset ι) (w : ι → _root_.OAI.Yau.Jets.Coord → ℝ)
    (hd : ∀ i ∈ I, ∀ j ∈ I, i ≠ j → Disjoint (tsupport (w i)) (tsupport (w j)))
    {i : ι} (hi : i ∈ I) {x : _root_.OAI.Yau.Jets.Coord} (hx : x ∈ tsupport (w i)) :
    (fun z ↦ ∑ j ∈ I, w j z) =ᶠ[𝓝 x] w i := by
  classical
  have hz : ∀ j ∈ I, j ≠ i → w j =ᶠ[𝓝 x] 0 := by
    intro j hj hji
    apply notMem_tsupport_iff_eventuallyEq.mp
    exact fun hjx ↦ Set.disjoint_left.mp (hd i hi j hj hji.symm) hx hjx
  have he : ∀ᶠ z in 𝓝 x, ∀ j ∈ I, j ≠ i → w j z = 0 := by
    apply (eventually_all_finite I.finite_toSet).mpr
    intro j hj
    by_cases hji : j=i
    · simp [hji]
    · filter_upwards [hz j hj hji] with z hz
      exact fun _ ↦ hz
  filter_upwards [he] with z hz
  exact Finset.sum_eq_single i hz (fun h ↦ (h hi).elim)

end Yau.Geometry

end

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Charts_CorrugationMetricError
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Yau.Jets
open scoped ContDiff
noncomputable section

lemma localizedCorrugation_first_scaled (χ : _root_.OAI.Yau.Jets.Coord → ℝ) (f : (ℝ × ℝ) → ℝ)
    (hχ : ContDiff ℝ ∞ χ) (hf : ContDiff ℝ ∞ f)
    (s : ℝ) {J : ℝ} (hJ : J ≠ 0) (R : ℝ)
    (a b : _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ) (y x v : _root_.OAI.Yau.Jets.Coord) :
    fderiv ℝ (localizedCorrugation χ f s J R a b y) x v =
      s*χ (R⁻¹ • (x-y))*fderiv ℝ f (corrugationFastMap J a b (x-y)) (a.prod b v) +
      s/(J*R)*f (corrugationFastMap J a b (x-y))*fderiv ℝ χ (R⁻¹ • (x-y)) v := by
  rw [localizedCorrugation_first χ f hχ hf]
  simp only [corrugationSlowMap,corrugationFastMap,smul_apply,
    ContinuousLinearMap.id_apply,map_smul,smul_eq_mul]
  by_cases hR : R = 0
  · simp [hR]
    field_simp
  · field_simp
    ring

lemma localizedCorrugation_second_scaled (χ : _root_.OAI.Yau.Jets.Coord → ℝ) (f : (ℝ × ℝ) → ℝ)
    (hχ : ContDiff ℝ ∞ χ) (hf : ContDiff ℝ ∞ f)
    (s : ℝ) {J : ℝ} (hJ : J ≠ 0) (R : ℝ)
    (a b : _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ) (y x u v : _root_.OAI.Yau.Jets.Coord) :
    fderiv ℝ (fderiv ℝ (localizedCorrugation χ f s J R a b y)) x u v =
      s*J*χ (R⁻¹ • (x-y))*
        fderiv ℝ (fderiv ℝ f) (corrugationFastMap J a b (x-y)) (a.prod b u) (a.prod b v) +
      s/R*(fderiv ℝ χ (R⁻¹ • (x-y)) v*
        fderiv ℝ f (corrugationFastMap J a b (x-y)) (a.prod b u) +
        fderiv ℝ χ (R⁻¹ • (x-y)) u*
        fderiv ℝ f (corrugationFastMap J a b (x-y)) (a.prod b v)) +
      s/(J*R^2)*f (corrugationFastMap J a b (x-y))*
        fderiv ℝ (fderiv ℝ χ) (R⁻¹ • (x-y)) u v := by
  rw [localizedCorrugation_second χ f hχ hf]
  simp only [corrugationSlowMap,corrugationFastMap,smul_apply,
    ContinuousLinearMap.id_apply,map_smul,smul_eq_mul]
  by_cases hR : R = 0
  · simp [hR]
    field_simp
  · field_simp
    ring

lemma localizedCorrugation_metric_hessian (g : _root_.OAI.Yau.Jets.Coord → _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ)
    (χ : _root_.OAI.Yau.Jets.Coord → ℝ) (f : (ℝ × ℝ) → ℝ)
    (hχ : ContDiff ℝ ∞ χ) (hf : ContDiff ℝ ∞ f)
    (s : ℝ) {J : ℝ} (hJ : J ≠ 0) (R : ℝ)
    (a b : _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ) (y x u v : _root_.OAI.Yau.Jets.Coord) :
    sourceHessian g (localizedCorrugation χ f s J R a b y) x u v =
      s*J*χ (R⁻¹ • (x-y))*
        fderiv ℝ (fderiv ℝ f) (corrugationFastMap J a b (x-y)) (a.prod b u) (a.prod b v) +
      corrugationMetricError g χ f s J R a b y x u v := by
  rw [sourceHessian_apply,localizedCorrugation_second_scaled χ f hχ hf s hJ,
    localizedCorrugation_first_scaled χ f hχ hf s hJ]
  unfold corrugationMetricError
  ring

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_CorrugationPeriodicBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Real Set Metric
noncomputable section

lemma centered_integer_representative (x : ℝ) :
    |x-(⌊x+(1/2:ℝ)⌋:ℤ)| ≤ 1/2 := by
  have h1 := Int.floor_le (x+(1/2:ℝ))
  have h2 := Int.lt_floor_add_one (x+(1/2:ℝ))
  rw [abs_le]
  constructor <;> linarith

lemma corrugationPeriodicWell_representative (a : ℝ) (z : ℝ × ℝ) :
    ∃ w : ℝ × ℝ, |w.1| ≤ 1/2 ∧ |w.2| ≤ 1/2 ∧
      corrugationPeriodicWell a z = corrugationDiskWell a (1/4) w := by
  let m : ℤ × ℤ := (⌊z.1+(1/2:ℝ)⌋,⌊z.2+(1/2:ℝ)⌋)
  let w : ℝ × ℝ := (z.1-(m.1:ℝ),z.2-(m.2:ℝ))
  have h1 : |w.1| ≤ 1/2 := centered_integer_representative z.1
  have h2 : |w.2| ≤ 1/2 := centered_integer_representative z.2
  refine ⟨w,h1,h2,?_⟩
  have he : (w.1+(m.1:ℝ),w.2+(m.2:ℝ))=z := by dsimp [w] <;> simp
  rw [← corrugationPeriodicWell_cell a w h1 h2,← corrugationPeriodicWell_periodic a m w,he]

theorem corrugationPeriodicWell_bounded (a : ℝ) :
    ∃ B : ℝ, 0 < B ∧ ∀ z, |corrugationPeriodicWell a z| ≤ B := by
  obtain ⟨B,hB⟩ := ((corrugationDiskWell_smooth a (1/4)).continuous.norm).bddAbove_range_of_hasCompactSupport
    ((corrugationDiskWell_compactSupport a (show (0:ℝ) ≤ 1/4 by norm_num)).norm)
  refine ⟨max B 0+1,by positivity,?_⟩
  intro z
  obtain ⟨w,_,_,hw⟩ := corrugationPeriodicWell_representative a z
  rw [hw]
  have hb := hB ⟨w,rfl⟩
  have hm := le_max_left B 0
  simpa only [Real.norm_eq_abs] using (hb.trans (by linarith : B ≤ max B 0+1))

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_CorrugationPeriodicJets
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
noncomputable section

lemma corrugationPeriodicWell_shift_jets (a : ℝ) (m : ℤ × ℤ) (z : ℝ × ℝ) :
    fderiv ℝ (corrugationPeriodicWell a) (z.1+(m.1:ℝ),z.2+(m.2:ℝ)) =
      fderiv ℝ (corrugationPeriodicWell a) z ∧
    fderiv ℝ (fderiv ℝ (corrugationPeriodicWell a)) (z.1+(m.1:ℝ),z.2+(m.2:ℝ)) =
      fderiv ℝ (fderiv ℝ (corrugationPeriodicWell a)) z := by
  let k : ℝ × ℝ := ((m.1:ℝ),(m.2:ℝ))
  have he : (fun w : ℝ × ℝ ↦ corrugationPeriodicWell a
      ((ContinuousLinearMap.id ℝ (ℝ × ℝ)) (w-(-k)))) = corrugationPeriodicWell a := by
    funext w
    change corrugationPeriodicWell a (w-(-k)) = _
    rw [sub_neg_eq_add]
    exact corrugationPeriodicWell_periodic a m w
  have hzadd : z+k = (z.1+(m.1:ℝ),z.2+(m.2:ℝ)) := rfl
  constructor
  · apply ContinuousLinearMap.ext
    intro v
    have h := affine_scalar_first (corrugationPeriodicWell a) (corrugationPeriodicWell_smooth a)
      (ContinuousLinearMap.id ℝ (ℝ × ℝ)) (-k) z v
    rw [he] at h
    simpa only [ContinuousLinearMap.id_apply,sub_neg_eq_add,hzadd] using h.symm
  · apply ContinuousLinearMap.ext
    intro u
    apply ContinuousLinearMap.ext
    intro v
    have h := affine_scalar_second (corrugationPeriodicWell a) (corrugationPeriodicWell_smooth a)
      (ContinuousLinearMap.id ℝ (ℝ × ℝ)) (-k) z u v
    rw [he] at h
    simpa only [ContinuousLinearMap.id_apply,sub_neg_eq_add,hzadd] using h.symm

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_CorrugationClosedCell
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Real Set Filter
open scoped Topology
noncomputable section

lemma nonzero_integer_shift_square_wide (x : ℝ) (hx : |x| ≤ 3/4)
    (k : ℤ) (hk : k ≠ 0) : (1/16:ℝ) ≤ (x-(k:ℝ))^2 := by
  have hx' := abs_le.mp hx
  rcases lt_or_gt_of_ne hk with hk | hk
  · have hk1 : k ≤ -1 := by omega
    have hkR : (k:ℝ) ≤ -1 := by exact_mod_cast hk1
    nlinarith
  · have hk1 : 1 ≤ k := by omega
    have hkR : 1 ≤ (k:ℝ) := by exact_mod_cast hk1
    nlinarith

lemma corrugationPeriodicWell_wide_cell (a : ℝ) (z : ℝ × ℝ)
    (hz₁ : |z.1| ≤ 3/4) (hz₂ : |z.2| ≤ 3/4) :
    corrugationPeriodicWell a z = corrugationDiskWell a (1/4) z := by
  unfold corrugationPeriodicWell
  rw [tsum_eq_single (0 : ℤ × ℤ)]
  · simp
  · intro k hk
    apply corrugationDiskWell_zero
    have h : k.1 ≠ 0 ∨ k.2 ≠ 0 := by
      by_contra h
      simp only [not_or,not_not] at h
      exact hk (Prod.ext h.1 h.2)
    rcases h with h | h
    · have hs := nonzero_integer_shift_square_wide z.1 hz₁ k.1 h
      dsimp only
      nlinarith [sq_nonneg (z.2-(k.2:ℝ))]
    · have hs := nonzero_integer_shift_square_wide z.2 hz₂ k.2 h
      dsimp only
      nlinarith [sq_nonneg (z.1-(k.1:ℝ))]

lemma corrugationPeriodicWell_closed_cell_eventually (a : ℝ) (z : ℝ × ℝ)
    (hz₁ : |z.1| ≤ 1/2) (hz₂ : |z.2| ≤ 1/2) :
    corrugationPeriodicWell a =ᶠ[𝓝 z] corrugationDiskWell a (1/4) := by
  have h1 : ∀ᶠ w : ℝ × ℝ in 𝓝 z, |w.1| < 3/4 :=
    continuous_fst.abs.continuousAt.eventually_lt_const (by linarith)
  have h2 : ∀ᶠ w : ℝ × ℝ in 𝓝 z, |w.2| < 3/4 :=
    continuous_snd.abs.continuousAt.eventually_lt_const (by linarith)
  filter_upwards [h1,h2] with w hw1 hw2
  exact corrugationPeriodicWell_wide_cell a w hw1.le hw2.le

lemma corrugationPeriodicWell_closed_cell_jets (a : ℝ) (z : ℝ × ℝ)
    (hz₁ : |z.1| ≤ 1/2) (hz₂ : |z.2| ≤ 1/2) :
    fderiv ℝ (corrugationPeriodicWell a) z = fderiv ℝ (corrugationDiskWell a (1/4)) z ∧
    fderiv ℝ (fderiv ℝ (corrugationPeriodicWell a)) z =
      fderiv ℝ (fderiv ℝ (corrugationDiskWell a (1/4))) z := by
  have h := corrugationPeriodicWell_closed_cell_eventually a z hz₁ hz₂
  exact ⟨h.fderiv_eq,h.fderiv.fderiv_eq⟩

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_CorrugationGlobalJets
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Real
noncomputable section

lemma corrugationCellPoint_bounds (z : ℝ × ℝ) :
    |(corrugationCellPoint z).1| ≤ 1/2 ∧ |(corrugationCellPoint z).2| ≤ 1/2 :=
  ⟨centered_integer_representative z.1,centered_integer_representative z.2⟩

lemma corrugationCellPoint_reconstruct (z : ℝ × ℝ) :
    ((corrugationCellPoint z).1+(corrugationCellIndex z).1,
     (corrugationCellPoint z).2+(corrugationCellIndex z).2) = z := by
  simp [corrugationCellPoint]

lemma corrugationCellRadius_properties (z : ℝ × ℝ) :
    0 ≤ corrugationCellRadius z ∧
    (corrugationCellRadius z)^2 = (corrugationCellPoint z).1^2+(corrugationCellPoint z).2^2 :=
  ⟨Real.sqrt_nonneg _,Real.sq_sqrt (by positivity)⟩

lemma corrugationPeriodicWell_global_jets (a : ℝ) (z : ℝ × ℝ) :
    fderiv ℝ (corrugationPeriodicWell a) z =
      fderiv ℝ (corrugationDiskWell a (1/4)) (corrugationCellPoint z) ∧
    fderiv ℝ (fderiv ℝ (corrugationPeriodicWell a)) z =
      fderiv ℝ (fderiv ℝ (corrugationDiskWell a (1/4))) (corrugationCellPoint z) := by
  have hs := corrugationPeriodicWell_shift_jets a (corrugationCellIndex z) (corrugationCellPoint z)
  rw [corrugationCellPoint_reconstruct] at hs
  have hc := corrugationPeriodicWell_closed_cell_jets a (corrugationCellPoint z)
    (corrugationCellPoint_bounds z).1 (corrugationCellPoint_bounds z).2
  exact ⟨hs.1.trans hc.1,hs.2.trans hc.2⟩

lemma corrugationPeriodicWell_global_radial_jets (a : ℝ) (z u v : ℝ × ℝ)
    (hr : corrugationCellRadius z ≠ 0) :
    fderiv ℝ (corrugationPeriodicWell a) z v =
      corrugationSlope a (1/4) (corrugationCellRadius z)*
        radialComponent (corrugationCellPoint z) v (corrugationCellRadius z) ∧
    fderiv ℝ (fderiv ℝ (corrugationPeriodicWell a)) z u v =
      deriv (corrugationSlope a (1/4)) (corrugationCellRadius z)*
        radialComponent (corrugationCellPoint z) u (corrugationCellRadius z)*
        radialComponent (corrugationCellPoint z) v (corrugationCellRadius z) +
      (corrugationSlope a (1/4) (corrugationCellRadius z)/corrugationCellRadius z)*
        angularComponent (corrugationCellPoint z) u (corrugationCellRadius z)*
        angularComponent (corrugationCellPoint z) v (corrugationCellRadius z) := by
  rw [(corrugationPeriodicWell_global_jets a z).1,(corrugationPeriodicWell_global_jets a z).2]
  exact ⟨corrugationDiskWell_radial_first a (1/4) _ v hr (corrugationCellRadius_properties z).2,
    corrugationDiskWell_radial_second a (1/4) _ u v hr (corrugationCellRadius_properties z).2⟩

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Charts_CorrugationRotatingFrame
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Yau.Jets
noncomputable section

lemma frozen_radial_covector (g : _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ)
    (e : _root_.OAI.Yau.Jets.Coord ≃L[ℝ] _root_.OAI.Yau.Jets.Coord)
    (he : ∀ i j, g (e (Pi.single i 1)) (e (Pi.single j 1)) = if i=j then 1 else 0)
    (z : ℝ × ℝ) (r : ℝ) (v : _root_.OAI.Yau.Jets.Coord) :
    radialComponent z ((frozenFrameCovector e 2).prod (frozenFrameCovector e 3) v) r =
      g (frozenPlaneVector e (z.1/r) (z.2/r)) v := by
  simp only [radialComponent,ContinuousLinearMap.prod_apply,frozenPlaneVector,map_add,map_smul,
    add_apply,smul_apply,smul_eq_mul]
  rw [frozenFrameCovector_metric g e he,frozenFrameCovector_metric g e he]
  ring

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

lemma localMetricGradient_continuousAt (g : E → E →L[ℝ] E →L[ℝ] ℝ)
    (f : E → ℝ) (x : E) (hg : ContinuousAt g x) (hf : ContDiffAt ℝ ∞ f x)
    (hp : ∀ v, v ≠ 0 → 0 < g x v v) : ContinuousAt (localMetricGradient g f) x :=
  (metric_inverse_continuousAt g x hg hp).clm_apply (hf.continuousAt_fderiv (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top))

end

open scoped ContDiff
attribute [local instance] clmTopology clmAdd clmModule

end Yau.Geometry

end

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Charts_MetricCoercivity
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Yau.Jets Set
noncomputable section
attribute [local instance] clmTopology clmAdd clmModule
variable {T : Type*} [TopologicalSpace T] [CompactSpace T]

lemma uniform_metric_coercivity (g : T → _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ)
    (hg : Continuous g) (hp : ∀ t v, v ≠ 0 → 0 < g t v v) :
    ∃ c > 0, ∃ B > 0, ∀ t, ‖g t‖ ≤ B ∧ ∀ v, c*‖v‖^2 ≤ g t v v := by
  have hc : Continuous (fun z : T × _root_.OAI.Yau.Jets.Coord ↦ g z.1 z.2 z.2) :=
    ((hg.comp continuous_fst).clm_apply continuous_snd).clm_apply continuous_snd
  obtain ⟨c,hc0,_,_,hbound⟩ := compact_positive_bounds
    (isCompact_univ.prod (isCompact_sphere (0:_root_.OAI.Yau.Jets.Coord) 1)) _ hc.continuousOn
    (fun z hz ↦ hp z.1 z.2 (by intro he; simpa [he] using hz.2))
  obtain ⟨B,hB,hBb⟩ := (isCompact_univ.image hg).isBounded.exists_pos_norm_le
  refine ⟨c,hc0,B,hB,?_⟩
  intro t
  refine ⟨hBb _ ⟨t,mem_univ _,rfl⟩,?_⟩
  intro v
  by_cases hv : v = 0
  · simp [hv]
  have hn : 0 < ‖v‖ := norm_pos_iff.mpr hv
  have hu : ‖(‖v‖⁻¹:ℝ) • v‖ = 1 := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hn),inv_mul_cancel₀ hn.ne']
  have hh := (hbound (t,(‖v‖⁻¹:ℝ) • v)
    ⟨mem_univ _,by simpa only [Metric.mem_sphere,dist_zero_right] using hu⟩).1
  simp only [map_smul,smul_apply,smul_eq_mul] at hh
  have hmul := mul_le_mul_of_nonneg_left hh (sq_nonneg ‖v‖)
  have he : ‖v‖^2*(‖v‖⁻¹*(‖v‖⁻¹*g t v v)) = g t v v := by field_simp
  rw [he] at hmul
  nlinarith

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Coefficients_CoefficientLocality
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Yau.Jets Filter
open scoped Topology
noncomputable section
attribute [local instance] clmTopology clmAdd clmModule

lemma sourceHessian_eventuallyEq
    {g G : _root_.OAI.Yau.Jets.Coord → _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ} {S A : _root_.OAI.Yau.Jets.Coord → ℝ} {x : _root_.OAI.Yau.Jets.Coord}
    (hg : g =ᶠ[𝓝 x] G) (hS : S =ᶠ[𝓝 x] A) :
    sourceHessian g S =ᶠ[𝓝 x] sourceHessian G A := by
  filter_upwards [hg,hg.fderiv (𝕜 := ℝ),hS.fderiv (𝕜 := ℝ),
    (hS.fderiv (𝕜 := ℝ)).fderiv (𝕜 := ℝ)] with z hz hd hs hss
  simp only [sourceHessian,hz,hd,hs,hss]

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_CompactFreezing
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Yau.Jets Set
open scoped ContDiff
noncomputable section
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

lemma compact_convex_freezing (f : _root_.OAI.Yau.Jets.Coord → F) {D : Set _root_.OAI.Yau.Jets.Coord}
    (hD : IsCompact D) (hconv : Convex ℝ D)
    (hdiff : ∀ x ∈ D, DifferentiableAt ℝ f x)
    (hder : ContinuousOn (fderiv ℝ f) D) :
    ∃ C : ℝ, 0 < C ∧ ∀ x ∈ D, ∀ y ∈ D, ‖f x-f y‖ ≤ C*‖x-y‖ := by
  obtain ⟨C,hC,hbound⟩ := (hD.image_of_continuousOn hder).isBounded.exists_pos_norm_le
  refine ⟨C,hC,?_⟩
  intro x hx y hy
  exact hconv.norm_image_sub_le_of_norm_fderiv_le hdiff
    (fun z hz ↦ hbound _ ⟨z,hz,rfl⟩) hy hx

lemma smooth_compact_freezing (f : _root_.OAI.Yau.Jets.Coord → F) {D U : Set _root_.OAI.Yau.Jets.Coord}
    (hD : IsCompact D) (hconv : Convex ℝ D) (hU : IsOpen U) (hDU : D ⊆ U)
    (hf : ContDiffOn ℝ ∞ f U) :
    ∃ C : ℝ, 0 < C ∧ ∀ x ∈ D, ∀ y ∈ D, ‖f x-f y‖ ≤ C*‖x-y‖ := by
  have hat : ∀ x ∈ D, ContDiffAt ℝ ∞ f x :=
    fun x hx ↦ hf.contDiffAt (hU.mem_nhds (hDU hx))
  apply compact_convex_freezing f hD hconv
  · exact fun x hx ↦ (hat x hx).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  · intro x hx
    exact ((hat x hx).continuousAt_fderiv (by simp)).continuousWithinAt

lemma smooth_compact_covector_freezing (S : _root_.OAI.Yau.Jets.Coord → ℝ) {D U : Set _root_.OAI.Yau.Jets.Coord}
    (hD : IsCompact D) (hconv : Convex ℝ D) (hU : IsOpen U) (hDU : D ⊆ U)
    (hS : ContDiffOn ℝ ∞ S U) :
    ∃ C : ℝ, 0 < C ∧ ∀ x ∈ D, ∀ y ∈ D, ∀ v : _root_.OAI.Yau.Jets.Coord,
      |fderiv ℝ S x v-fderiv ℝ S y v| ≤ C*‖x-y‖*‖v‖ := by
  have hd : ContDiffOn ℝ ∞ (fderiv ℝ S) U :=
    hS.fderiv_of_isOpen hU (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  obtain ⟨C,hC,hb⟩ := smooth_compact_freezing (fderiv ℝ S) hD hconv hU hDU hd
  refine ⟨C,hC,?_⟩
  intro x hx y hy v
  exact ((fderiv ℝ S x-fderiv ℝ S y).le_opNorm v).trans
    (mul_le_mul_of_nonneg_right (hb x hx y hy) (norm_nonneg v))

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_CorrugationCubePartition
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Yau.Jets Set Metric
noncomputable section

lemma corrugationCubeCenter_mem (o : _root_.OAI.Yau.Jets.Coord) {L : ℝ} (hL : 0 < L)
    {n : ℕ} (hn : 0 < n) (k : Fin 4 → Fin n) :
    corrugationCubeCenter o L n k ∈ Set.Icc o (fun i ↦ o i+L) := by
  have hnR : (0:ℝ) < n := by exact_mod_cast hn
  have hR : 0 < L/(n:ℝ) := div_pos hL hnR
  have hRn : (L/(n:ℝ))*(n:ℝ) = L := div_mul_cancel₀ L hnR.ne'
  constructor <;> intro i
  · dsimp [corrugationCubeCenter]
    have hk : (0:ℝ) ≤ (k i:ℝ) := by positivity
    nlinarith
  · dsimp [corrugationCubeCenter]
    have hk : (k i:ℝ)+1 ≤ n := by exact_mod_cast (k i).isLt
    nlinarith

lemma corrugationCube_balls_disjoint (o : _root_.OAI.Yau.Jets.Coord) {L : ℝ} (hL : 0 < L)
    {n : ℕ} (hn : 0 < n) (k j : Fin 4 → Fin n) (hkj : k ≠ j) :
    Disjoint (ball (corrugationCubeCenter o L n k) ((L/(n:ℝ))/2))
      (ball (corrugationCubeCenter o L n j) ((L/(n:ℝ))/2)) := by
  have hnR : (0:ℝ) < n := by exact_mod_cast hn
  have hR : 0 < L/(n:ℝ) := div_pos hL hnR
  obtain ⟨i,hi⟩ : ∃ i, k i ≠ j i := Function.ne_iff.mp hkj
  have hi' : (k i).val ≠ (j i).val := fun h ↦ hi (Fin.ext h)
  have hd : (1:ℝ) ≤ |(k i:ℝ)-(j i:ℝ)| := by
    rcases lt_or_gt_of_ne hi' with h | h
    · have hh : (k i:ℝ)+1 ≤ (j i:ℝ) := by exact_mod_cast h
      rw [abs_of_nonpos (by linarith)]
      linarith
    · have hh : (j i:ℝ)+1 ≤ (k i:ℝ) := by exact_mod_cast h
      rw [abs_of_nonneg (by linarith)]
      linarith
  apply ball_disjoint_ball
  have hcoord := norm_le_pi_norm (corrugationCubeCenter o L n k-corrugationCubeCenter o L n j) i
  have he : ‖(corrugationCubeCenter o L n k-corrugationCubeCenter o L n j) i‖ =
      (L/(n:ℝ))*|(k i:ℝ)-(j i:ℝ)| := by
    change |(o i+_)-(o i+_)| = _
    rw [add_sub_add_left_eq_sub,← mul_sub,abs_mul,abs_of_pos hR]
    congr 2
    ring
  rw [he] at hcoord
  rw [dist_eq_norm]
  nlinarith

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_CorrugationLocalHessian
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Yau.Jets Filter
open scoped ContDiff Topology
noncomputable section

lemma sourceHessian_add_at (g : _root_.OAI.Yau.Jets.Coord → _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ)
    (S w : _root_.OAI.Yau.Jets.Coord → ℝ) {x : _root_.OAI.Yau.Jets.Coord} (hS : ContDiffAt ℝ ∞ S x)
    (hw : ContDiffAt ℝ ∞ w x) (u v : _root_.OAI.Yau.Jets.Coord) :
    sourceHessian g (S+w) x u v = sourceHessian g S x u v+sourceHessian g w x u v := by
  have hSn : ∀ᶠ y in 𝓝 x, ContDiffAt ℝ 1 S y := (hS.of_le (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).eventually (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  have hwn : ∀ᶠ y in 𝓝 x, ContDiffAt ℝ 1 w y := (hw.of_le (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).eventually (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  have he : fderiv ℝ (S+w) =ᶠ[𝓝 x] fderiv ℝ S+fderiv ℝ w := by
    filter_upwards [hSn,hwn] with y hy hz
    exact fderiv_add (hy.differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)) (hz.differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top))
  rw [sourceHessian_apply,sourceHessian_apply,sourceHessian_apply,he.fderiv_eq,he.self_of_nhds]
  rw [fderiv_add ((hS.fderiv_right (m := ∞) (by simp)).differentiableAt (by simp))
    ((hw.fderiv_right (m := ∞) (by simp)).differentiableAt (by simp))]
  simp only [add_apply,Pi.add_apply]
  ring

lemma corrugationPeriodicWell_radius_zero_positive {amp : ℝ} (ha : 0 ≤ amp)
    (z v : ℝ × ℝ) (hr : corrugationCellRadius z = 0) :
    0 ≤ fderiv ℝ (fderiv ℝ (corrugationPeriodicWell amp)) z v v := by
  have hs := (corrugationCellRadius_properties z).2
  rw [hr] at hs
  have h1 : (corrugationCellPoint z).1 = 0 := by nlinarith [sq_nonneg (corrugationCellPoint z).2]
  have h2 : (corrugationCellPoint z).2 = 0 := by nlinarith [sq_nonneg (corrugationCellPoint z).1]
  have hz : corrugationCellPoint z = 0 := Prod.ext h1 h2
  rw [(corrugationPeriodicWell_global_jets amp z).2,hz]
  exact corrugationDiskWell_center_positive ha (1/4) v

lemma corrugated_envelope_global_hessian
    (g : _root_.OAI.Yau.Jets.Coord → _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ) (S χ : _root_.OAI.Yau.Jets.Coord → ℝ)
    {x : _root_.OAI.Yau.Jets.Coord} (hS : ContDiffAt ℝ ∞ S x) (hχ : ContDiff ℝ ∞ χ)
    (amp s : ℝ) {J : ℝ} (hJ : J ≠ 0) (R : ℝ) (a b : _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ)
    (y u v : _root_.OAI.Yau.Jets.Coord) :
    sourceHessian g (S+localizedCorrugation χ (corrugationPeriodicWell amp) s J R a b y) x u v =
      sourceHessian g S x u v + s*J*χ (R⁻¹ • (x-y))*
        fderiv ℝ (fderiv ℝ (corrugationPeriodicWell amp)) (corrugationFastMap J a b (x-y))
          (a.prod b u) (a.prod b v) +
      corrugationMetricError g χ (corrugationPeriodicWell amp) s J R a b y x u v := by
  rw [sourceHessian_add_at g S _ hS
    (localizedCorrugation_smooth χ _ hχ (corrugationPeriodicWell_smooth amp) _ _ _ _ _ _).contDiffAt,
    localizedCorrugation_metric_hessian g χ _ hχ (corrugationPeriodicWell_smooth amp) s hJ]
  ring

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_CorrugationFastLower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Yau.Jets
noncomputable section

lemma corrugation_fast_hessian_lower {amp B : ℝ} (ha : 0 ≤ amp) (hB : 0 ≤ B)
    (z v : ℝ × ℝ)
    (hb : corrugationCellRadius z ≠ 0 →
      |radialComponent (corrugationCellPoint z) v (corrugationCellRadius z)| ≤ B) :
    -(max (-deriv (corrugationSlope amp (1/4)) (corrugationCellRadius z)) 0 * B^2) ≤
      fderiv ℝ (fderiv ℝ (corrugationPeriodicWell amp)) z v v := by
  by_cases hr : corrugationCellRadius z = 0
  · exact (neg_nonpos.mpr (mul_nonneg (le_max_right _ _) (sq_nonneg B))).trans
      (corrugationPeriodicWell_radius_zero_positive ha z v hr)
  · rw [(corrugationPeriodicWell_global_radial_jets amp z v v hr).2]
    let r := corrugationCellRadius z
    let d := max (-deriv (corrugationSlope amp (1/4)) r) 0
    let u := radialComponent (corrugationCellPoint z) v r
    let t := angularComponent (corrugationCellPoint z) v r
    have hr0 : 0 < r := lt_of_le_of_ne (corrugationCellRadius_properties z).1 (Ne.symm hr)
    have hl : 0 ≤ corrugationSlope amp (1/4) r := corrugationSlope_nonneg ha hr0.le
    have hu : u^2 ≤ B^2 := by
      have h := hb hr
      have hsq := sq_le_sq₀ (abs_nonneg u) hB
      exact (sq_abs u).symm.trans_le (hsq.mpr h)
    have hd : 0 ≤ d := le_max_right _ _
    have hdp : -d ≤ deriv (corrugationSlope amp (1/4)) r := by
      have h := le_max_left (-deriv (corrugationSlope amp (1/4)) r) 0
      dsimp [d] <;> linarith
    have hq := mul_le_mul_of_nonneg_right hdp (sq_nonneg u)
    have hs := mul_le_mul_of_nonneg_left hu hd
    have ht := mul_nonneg (div_nonneg hl hr0.le) (sq_nonneg t)
    change -(d*B^2) ≤ deriv (corrugationSlope amp (1/4)) r*u*u+
      (corrugationSlope amp (1/4) r/r)*t*t
    nlinarith only [hq,hs,ht]

lemma weighted_hessian_perturbation_lower {ν H₁ H₂ F₁ F₂ E₁ E₂ B E : ℝ}
    (hν0 : 0 ≤ ν) (hν1 : ν ≤ 1) (hB : 0 ≤ B) (hE : 0 ≤ E)
    (hF₁ : -B ≤ F₁) (hF₂ : -B ≤ F₂) (hE₁ : |E₁| ≤ E) (hE₂ : |E₂| ≤ E) :
    ν*H₁+H₂-2*B-2*E ≤ ν*(H₁+F₁+E₁)+(H₂+F₂+E₂) := by
  have h1 := mul_le_mul_of_nonneg_left hF₁ hν0
  have h2 := mul_le_mul_of_nonneg_left (abs_le.mp hE₁).1 hν0
  have h3 := mul_le_mul_of_nonneg_right hν1 hB
  have h4 := mul_le_mul_of_nonneg_right hν1 hE
  have h5 := (abs_le.mp hE₂).1
  nlinarith

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_CorrugationFirstAxis
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Yau.Jets Set
open scoped ContDiff
noncomputable section

lemma compact_first_derivative_bound (χ : _root_.OAI.Yau.Jets.Coord → ℝ) (hχ : ContDiff ℝ ∞ χ)
    (hc : HasCompactSupport χ) : ∃ C : ℝ, 0 < C ∧ ∀ x, ‖fderiv ℝ χ x‖ ≤ C := by
  have hcD : IsCompact (tsupport (fderiv ℝ χ)) :=
    hc.of_isClosed_subset isClosed_closure (tsupport_fderiv_subset ℝ (f := χ))
  have hcont : Continuous (fun x ↦ ‖fderiv ℝ χ x‖) := (hχ.continuous_fderiv (by simp)).norm
  obtain ⟨B,hB⟩ := (hcD.image hcont).bddAbove
  refine ⟨max B 0+1,by positivity,fun x ↦ ?_⟩
  by_cases hx : x ∈ tsupport (fderiv ℝ χ)
  · exact (hB ⟨x,hx,rfl⟩).trans (by linarith [le_max_left B 0])
  · have hz : fderiv ℝ χ x = 0 := by
      by_contra hn
      exact hx (subset_tsupport _ hn)
    rw [hz]
    simp only [ContinuousLinearMap.opNorm_zero]
    positivity

theorem corrugation_first_axis_bound (χ : _root_.OAI.Yau.Jets.Coord → ℝ) (hχ : ContDiff ℝ ∞ χ)
    (hc : HasCompactSupport χ) (amp : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (s J R : ℝ), 0 ≤ s → 0 < J → 0 < R →
      ∀ (a b : _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ) (y x v : _root_.OAI.Yau.Jets.Coord), a v = 0 → b v = 0 →
      |fderiv ℝ (localizedCorrugation χ (corrugationPeriodicWell amp) s J R a b y) x v| ≤
        s/(J*R)*C*‖v‖ := by
  obtain ⟨B,hB,hf⟩ := corrugationPeriodicWell_bounded amp
  obtain ⟨M,hM,hd⟩ := compact_first_derivative_bound χ hχ hc
  refine ⟨B*M,mul_pos hB hM,?_⟩
  intro s J R hs hJ hR a b y x v ha hb
  rw [localizedCorrugation_first_scaled χ _ hχ (corrugationPeriodicWell_smooth amp) s hJ.ne']
  have hz : a.prod b v = 0 := by ext <;> assumption
  rw [hz,map_zero,mul_zero,zero_add,abs_mul,abs_mul,abs_of_nonneg (div_nonneg hs (mul_pos hJ hR).le)]
  have hder : |fderiv ℝ χ (R⁻¹ • (x-y)) v| ≤ M*‖v‖ :=
    ((fderiv ℝ χ _).le_opNorm v).trans (mul_le_mul_of_nonneg_right (hd _) (norm_nonneg v))
  calc
    _ ≤ (s/(J*R)*B)*(M*‖v‖) := mul_le_mul
      (mul_le_mul_of_nonneg_left (hf _) (by positivity)) hder (abs_nonneg _) (by positivity)
    _ = _ := by ring

lemma corrugated_first_axis_positive (S : _root_.OAI.Yau.Jets.Coord → ℝ) (χ : _root_.OAI.Yau.Jets.Coord → ℝ)
    (hχ : ContDiff ℝ ∞ χ) (amp : ℝ)
    (s J R C A K : ℝ) (_hs : 0 < s) (hA : 0 ≤ A) (_hK : 0 ≤ K)
    (a b : _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ) (y x v : _root_.OAI.Yau.Jets.Coord)
    (hS : DifferentiableAt ℝ S x)
    (haxis : fderiv ℝ S y v = s)
    (hfreeze : |fderiv ℝ S x v-fderiv ℝ S y v| ≤ A*‖x-y‖*‖v‖)
    (hxy : ‖x-y‖ ≤ R) (hv : ‖v‖ ≤ K)
    (herr : |fderiv ℝ (localizedCorrugation χ (corrugationPeriodicWell amp) s J R a b y) x v| ≤
      s/(J*R)*C*‖v‖)
    (hcoef : 0 ≤ s/(J*R)*C)
    (hsmall₁ : A*R*K ≤ s/4) (hsmall₂ : s/(J*R)*C*K ≤ s/4) :
    s/2 ≤ fderiv ℝ (fun z ↦ S z+localizedCorrugation χ (corrugationPeriodicWell amp) s J R a b y z) x v := by
  have hw := (localizedCorrugation_smooth χ _ hχ (corrugationPeriodicWell_smooth amp) s J R a b y).differentiable (by simp)
  change s/2 ≤ fderiv ℝ (S+localizedCorrugation χ (corrugationPeriodicWell amp) s J R a b y) x v
  rw [fderiv_add hS hw.differentiableAt,add_apply]
  have hR : 0 ≤ R := (norm_nonneg (x-y)).trans hxy
  have hfreeze' : |fderiv ℝ S x v-s| ≤ s/4 := by
    rw [haxis] at hfreeze
    apply hfreeze.trans
    calc
      A*‖x-y‖*‖v‖ ≤ A*R*K := mul_le_mul (mul_le_mul_of_nonneg_left hxy hA) hv (norm_nonneg _) (by positivity)
      _ ≤ _ := hsmall₁
  have herr' : |fderiv ℝ (localizedCorrugation χ (corrugationPeriodicWell amp) s J R a b y) x v| ≤ s/4 :=
    herr.trans ((mul_le_mul_of_nonneg_left hv hcoef).trans hsmall₂)
  have h1 := (abs_le.mp hfreeze').1
  have h2 := (abs_le.mp herr').1
  linarith

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_CorrugationFixedAmplitude
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Set
noncomputable section

lemma corrugationFixedAmplitude_spec :
    0 < corrugationFixedAmplitude ∧ corrugationFixedAmplitude ≤ 1 ∧
    (∀ r : ℝ, 0 ≤ r → corrugationSlope corrugationFixedAmplitude (1/4) r *
      max (-deriv (corrugationSlope corrugationFixedAmplitude (1/4)) r) 0 ≤ 1/(64*(1/4:ℝ))) ∧
    ∃ l₀ : ℝ, 0 < l₀ ∧ ∀ r ∈ Icc (1/16:ℝ) (1/8),
      l₀ ≤ corrugationSlope corrugationFixedAmplitude (1/4) r := by
  obtain ⟨C,l₀,ha,ha1,_,hl₀,_,hb,hann,_⟩ := Classical.choose_spec exists_fixed_corrugation_slope
  exact ⟨ha,ha1,fun r hr ↦ (hb r hr).2.2.2,l₀,hl₀,hann⟩

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_CorrugationFrequencyScale
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Filter Real
open scoped Topology
noncomputable section

lemma corrugationScale_formula (L : ℝ) (k : ℕ) :
    corrugationScale L k = L/((k:ℝ)+1)^2 := by
  simp [corrugationScale,corrugationSubdivision]

lemma corrugationFrequency_positive (k : ℕ) : 0 < corrugationFrequency k := by
  unfold corrugationFrequency
  positivity

lemma corrugationSubdivision_positive (k : ℕ) : 0 < corrugationSubdivision k := by
  unfold corrugationSubdivision
  positivity

lemma corrugationScale_positive {L : ℝ} (hL : 0 < L) (k : ℕ) :
    0 < corrugationScale L k := by
  rw [corrugationScale_formula]
  positivity

lemma corrugationFrequency_eighth (k : ℕ) :
    (corrugationFrequency k)^((1:ℝ)/8) = (k:ℝ)+1 := by
  rw [corrugationFrequency,← Real.rpow_natCast,← Real.rpow_mul (by positivity)]
  norm_num

lemma corrugation_scale_rate_identities {L : ℝ} (hL : L ≠ 0) (k : ℕ) :
    (corrugationScale L k)^2*(corrugationFrequency k)^((1:ℝ)/8) = L^2/((k:ℝ)+1)^3 ∧
    (corrugationFrequency k*(corrugationScale L k)^2)⁻¹ = (L^2)⁻¹/((k:ℝ)+1)^4 ∧
    (corrugationFrequency k*corrugationScale L k)⁻¹ = L⁻¹/((k:ℝ)+1)^6 ∧
    corrugationFrequency k*corrugationScale L k = L*((k:ℝ)+1)^6 := by
  rw [corrugationFrequency_eighth,corrugationScale_formula,corrugationFrequency]
  have hk : (k:ℝ)+1 ≠ 0 := by positivity
  constructor
  · field_simp
  constructor
  · field_simp
  constructor
  · field_simp
  · field_simp

lemma corrugation_power_reciprocal_tendsto (C : ℝ) {p : ℕ} (hp : p ≠ 0) :
    Tendsto (fun k : ℕ ↦ C/((k:ℝ)+1)^p) atTop (𝓝 0) := by
  have hk : Tendsto (fun k : ℕ ↦ (k:ℝ)+1) atTop atTop :=
    tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
  have hp' := (tendsto_pow_atTop hp).comp hk
  simpa only [div_eq_mul_inv,mul_zero,Function.comp_def,Pi.inv_apply] using hp'.inv_tendsto_atTop.const_mul C

lemma corrugationScale_tendsto (L : ℝ) :
    Tendsto (corrugationScale L) atTop (𝓝 0) := by
  change Tendsto (fun k ↦ corrugationScale L k) atTop (𝓝 0)
  simp_rw [corrugationScale_formula]
  exact corrugation_power_reciprocal_tendsto L (by norm_num)

lemma corrugation_frequency_scale_tendsto {L : ℝ} (hL : 0 < L) :
    Tendsto (fun k ↦ corrugationFrequency k*corrugationScale L k) atTop atTop := by
  have hk : Tendsto (fun k : ℕ ↦ (k:ℝ)+1) atTop atTop :=
    tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
  simp_rw [(corrugation_scale_rate_identities hL.ne' _).2.2.2]
  exact ((tendsto_pow_atTop (by norm_num : (6:ℕ) ≠ 0)).comp hk).const_mul_atTop hL

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_CorrugationOldData
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Yau.Jets Set
open scoped ContDiff
noncomputable section

lemma corrugationOldSlope_positive (g : _root_.OAI.Yau.Jets.Coord → _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ)
    (S : _root_.OAI.Yau.Jets.Coord → ℝ) (y : _root_.OAI.Yau.Jets.Coord) (hp : ∀ v, v ≠ 0 → 0 < g y v v)
    (hn : metricGradient g S y ≠ 0) : 0 < corrugationOldSlope g S y :=
  Real.sqrt_pos.mpr (hp _ hn)

lemma corrugationOldSlope_continuousOn (g : _root_.OAI.Yau.Jets.Coord → _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ)
    (S : _root_.OAI.Yau.Jets.Coord → ℝ) {U : Set _root_.OAI.Yau.Jets.Coord} (hU : IsOpen U)
    (hg : ContDiffOn ℝ ∞ g U) (hS : ContDiffOn ℝ ∞ S U)
    (hp : ∀ y ∈ U, ∀ v, v ≠ 0 → 0 < g y v v) :
    ContinuousOn (corrugationOldSlope g S) U := by
  intro y hy
  have hg' := hg.contDiffAt (hU.mem_nhds hy)
  have hS' := hS.contDiffAt (hU.mem_nhds hy)
  have hgrad : ContinuousAt (metricGradient g S) y :=
    localMetricGradient_continuousAt g S y hg'.continuousAt hS' (hp y hy)
  exact (Real.continuous_sqrt.continuousAt.comp
    ((hg'.continuousAt.clm_apply hgrad).clm_apply hgrad)).continuousWithinAt

lemma corrugationOldSlope_compact_bounds
    (g : _root_.OAI.Yau.Jets.Coord → _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ) (S : _root_.OAI.Yau.Jets.Coord → ℝ)
    {D U : Set _root_.OAI.Yau.Jets.Coord} (hD : IsCompact D) (hU : IsOpen U) (hDU : D ⊆ U)
    (hg : ContDiffOn ℝ ∞ g U) (hS : ContDiffOn ℝ ∞ S U)
    (hp : ∀ y ∈ U, ∀ v, v ≠ 0 → 0 < g y v v)
    (hn : ∀ y ∈ D, metricGradient g S y ≠ 0) :
    ∃ m : ℝ, 0 < m ∧ ∃ B : ℝ, 0 < B ∧
      ∀ y ∈ D, m ≤ corrugationOldSlope g S y ∧ corrugationOldSlope g S y ≤ B := by
  exact compact_positive_bounds hD _
    ((corrugationOldSlope_continuousOn g S hU hg hS hp).mono hDU)
    (fun y hy ↦ corrugationOldSlope_positive g S y (hp y (hDU hy)) (hn y hy))

lemma compact_metric_comparison (g : _root_.OAI.Yau.Jets.Coord → _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ)
    {D : Set _root_.OAI.Yau.Jets.Coord} (hD : IsCompact D) (hg : ContinuousOn g D)
    (hp : ∀ y ∈ D, ∀ v, v ≠ 0 → 0 < g y v v) :
    ∃ c : ℝ, 0 < c ∧ ∃ M : ℝ, 0 < M ∧
      ∀ y ∈ D, ‖g y‖ ≤ M ∧ ∀ v, c*‖v‖^2 ≤ g y v v := by
  let : CompactSpace D := isCompact_iff_compactSpace.mp hD
  obtain ⟨c,hc,M,hM,hb⟩ := uniform_metric_coercivity (fun y : D ↦ g y)
    hg.domRestrict (fun y v hv ↦ hp y y.property v hv)
  exact ⟨c,hc,M,hM,fun y hy ↦ hb ⟨y,hy⟩⟩

lemma corrugation_frozen_axis_differential
    (g : _root_.OAI.Yau.Jets.Coord → _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ) (S : _root_.OAI.Yau.Jets.Coord → ℝ) (y : _root_.OAI.Yau.Jets.Coord)
    (hp : ∀ v, v ≠ 0 → 0 < g y v v) (hn : metricGradient g S y ≠ 0)
    (e : _root_.OAI.Yau.Jets.Coord ≃L[ℝ] _root_.OAI.Yau.Jets.Coord)
    (he : e (Pi.single 0 1) = (corrugationOldSlope g S y)⁻¹ • metricGradient g S y) :
    fderiv ℝ S y (e (Pi.single 0 1)) = corrugationOldSlope g S y := by
  have hs := corrugationOldSlope_positive g S y hp hn
  have hsq : (corrugationOldSlope g S y)^2 = g y (metricGradient g S y) (metricGradient g S y) :=
    Real.sq_sqrt (hp _ hn).le
  rw [← metricGradient_pair g S y hp,he,map_smul,smul_eq_mul,← hsq]
  field_simp

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_CorrugationNonvanishing
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

theorem corrugation_local_nonvanishing
    (g : _root_.OAI.Yau.Jets.Coord → _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ) (S χ : _root_.OAI.Yau.Jets.Coord → ℝ)
    {D U : Set _root_.OAI.Yau.Jets.Coord} (hD : IsCompact D) (hconv : Convex ℝ D)
    (hU : IsOpen U) (hDU : D ⊆ U)
    (hg : ContDiffOn ℝ ∞ g U) (hS : ContDiffOn ℝ ∞ S U)
    (hp : ∀ y ∈ U, ∀ v, v ≠ 0 → 0 < g y v v)
    (hn : ∀ y ∈ D, metricGradient g S y ≠ 0)
    (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (amp : ℝ) {L : ℝ} (hL : 0 < L) :
    ∀ᶠ k : ℕ in atTop, ∀ y ∈ D, ∀ x ∈ D,
      ‖x-y‖ ≤ corrugationScale L k →
      ∀ e : _root_.OAI.Yau.Jets.Coord ≃L[ℝ] _root_.OAI.Yau.Jets.Coord,
      e (Pi.single 0 1) = (corrugationOldSlope g S y)⁻¹ • metricGradient g S y →
      (∀ i j, g y (e (Pi.single i 1)) (e (Pi.single j 1)) = if i=j then 1 else 0) →
      metricGradient g (S+localizedCorrugation χ (corrugationPeriodicWell amp)
        (corrugationOldSlope g S y) (corrugationFrequency k) (corrugationScale L k)
        (frozenFrameCovector e 2) (frozenFrameCovector e 3) y) x ≠ 0 := by
  obtain ⟨m,hm,B,hB,hslope⟩ := corrugationOldSlope_compact_bounds g S hD hU hDU hg hS hp hn
  obtain ⟨c,hc0,M,hM,hmetric⟩ := compact_metric_comparison g hD (hg.continuousOn.mono hDU)
    (fun y hy ↦ hp y (hDU hy))
  obtain ⟨A,hA,hfreeze⟩ := smooth_compact_covector_freezing S hD hconv hU hDU hS
  obtain ⟨C,hC,hfirst⟩ := corrugation_first_axis_bound χ hχ hc amp
  let K : ℝ := 1+c⁻¹
  have hK : 0 < K := by dsimp [K] <;> positivity
  have ht1 : Tendsto (fun k ↦ A*corrugationScale L k*K) atTop (𝓝 0) := by
    simpa using ((corrugationScale_tendsto L).const_mul A).mul_const K
  have ht2 : Tendsto (fun k ↦ C/(corrugationFrequency k*corrugationScale L k)*K) atTop (𝓝 0) := by
    simpa [div_eq_mul_inv] using
      (((corrugation_frequency_scale_tendsto hL).inv_tendsto_atTop).const_mul C).mul_const K
  have he1 := ht1.eventually_lt_const (show (0:ℝ) < m/4 by positivity)
  have he2 := ht2.eventually_lt_const (show (0:ℝ) < 1/4 by norm_num)
  filter_upwards [he1,he2] with k hk1 hk2
  intro y hy x hx hxy e he0 he
  let v : _root_.OAI.Yau.Jets.Coord := e (Pi.single 0 1)
  let s : ℝ := corrugationOldSlope g S y
  have hs : 0 < s := corrugationOldSlope_positive g S y (hp y (hDU hy)) (hn y hy)
  have hv : ‖v‖ ≤ K := metric_unit_coordinate_bound (g y) hc0 (hmetric y hy).2 v (by simpa [v] using he 0 0)
  have ha : frozenFrameCovector e 2 v = 0 := by dsimp [v]; rw [frozenFrameCovector_axis]; norm_num [Fin.ext_iff]
  have hb : frozenFrameCovector e 3 v = 0 := by dsimp [v]; rw [frozenFrameCovector_axis]; norm_num [Fin.ext_iff]
  have hJ := corrugationFrequency_positive k
  have hR := corrugationScale_positive hL k
  have herr := hfirst s (corrugationFrequency k) (corrugationScale L k) hs.le hJ hR _ _ y x v ha hb
  have hsmall1 : A*corrugationScale L k*K ≤ s/4 := by
    have hm' := (hslope y hy).1
    dsimp [s]
    linarith
  have hsmall2 : s/(corrugationFrequency k*corrugationScale L k)*C*K ≤ s/4 := by
    have hh := mul_le_mul_of_nonneg_left hk2.le hs.le
    calc
      _ = s*(C/(corrugationFrequency k*corrugationScale L k)*K) := by ring
      _ ≤ s*(1/4) := hh
      _ = s/4 := by ring
  have hpos := corrugated_first_axis_positive S χ hχ amp s (corrugationFrequency k)
    (corrugationScale L k) C A K hs hA.le hK.le _ _ y x v
    ((hS.contDiffAt (hU.mem_nhds (hDU hx))).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top))
    (corrugation_frozen_axis_differential g S y (hp y (hDU hy)) (hn y hy) e he0)
    (hfreeze x hx y hy v) hxy hv herr (by positivity) hsmall1 hsmall2
  intro hz
  have hpair := metricGradient_pair g (S+localizedCorrugation χ (corrugationPeriodicWell amp)
    s (corrugationFrequency k) (corrugationScale L k) (frozenFrameCovector e 2) (frozenFrameCovector e 3) y)
    x (hp x (hDU hx)) v
  rw [hz,map_zero,zero_apply] at hpair
  change s/2 ≤ fderiv ℝ (S+localizedCorrugation χ (corrugationPeriodicWell amp)
    s (corrugationFrequency k) (corrugationScale L k) (frozenFrameCovector e 2) (frozenFrameCovector e 3) y) x v at hpos
  rw [← hpair] at hpos
  linarith

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_CorrugationRegimeBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Real Filter
open scoped Topology
noncomputable section

lemma corrugation_fractional_product {χ l : ℝ} (hχ : 0 ≤ χ) (hχ1 : χ ≤ 1)
    (hl : 0 ≤ l) (hl1 : l ≤ 1) :
    χ^((7:ℝ)/8)*l ≤ (χ*l)^((7:ℝ)/8) ∧
    χ*l^((7:ℝ)/8) ≤ (χ*l)^((7:ℝ)/8) := by
  rw [Real.mul_rpow hχ hl]
  exact ⟨mul_le_mul_of_nonneg_left (Real.self_le_rpow_of_le_one hl hl1 (by norm_num)) (Real.rpow_nonneg hχ _),
    mul_le_mul_of_nonneg_right (Real.self_le_rpow_of_le_one hχ hχ1 (by norm_num)) (Real.rpow_nonneg hl _)⟩

lemma corrugation_low_regime_products {χ l J T : ℝ}
    (hχ : 0 ≤ χ) (hχ1 : χ ≤ 1) (hl : 0 ≤ l) (hl1 : l ≤ 1)
    (hJ : 0 < J) (hreg : J*χ*l ≤ T) :
    χ^((7:ℝ)/8)*l ≤ (T/J)^((7:ℝ)/8) ∧
    χ*l^((7:ℝ)/8) ≤ (T/J)^((7:ℝ)/8) ∧ χ*l ≤ T/J := by
  have hp : χ*l ≤ T/J := (le_div_iff₀ hJ).mpr (by nlinarith)
  have hr := Real.rpow_le_rpow (mul_nonneg hχ hl) hp (by norm_num : (0:ℝ) ≤ 7/8)
  exact ⟨(corrugation_fractional_product hχ hχ1 hl hl1).1.trans hr,
    (corrugation_fractional_product hχ hχ1 hl hl1).2.trans hr,hp⟩

lemma corrugationLowErrorRate_bounds {χ l L : ℝ} (hL : 0 < L) (T : ℝ) (k : ℕ)
    (hχ : 0 ≤ χ) (hχ1 : χ ≤ 1) (hl : 0 ≤ l) (hl1 : l ≤ 1)
    (hreg : corrugationFrequency k*χ*l ≤ T) :
    (corrugationScale L k)⁻¹*χ^((7:ℝ)/8)*l +
      (corrugationFrequency k*(corrugationScale L k)^2)⁻¹ + χ*l +
      (corrugationFrequency k*corrugationScale L k)⁻¹ ≤ corrugationLowErrorRate L T k ∧
    (corrugationScale L k)^2*corrugationFrequency k*χ*l^((7:ℝ)/8) ≤
      corrugationLowRadialRate L T k := by
  obtain ⟨h1,h2,h3⟩ := corrugation_low_regime_products hχ hχ1 hl hl1 (corrugationFrequency_positive k) hreg
  constructor
  · unfold corrugationLowErrorRate
    have hh := mul_le_mul_of_nonneg_left h1 (inv_nonneg.mpr (corrugationScale_positive hL k).le)
    nlinarith
  · unfold corrugationLowRadialRate
    have hh := mul_le_mul_of_nonneg_left h2
      (mul_nonneg (sq_nonneg (corrugationScale L k)) (corrugationFrequency_positive k).le)
    nlinarith

lemma corrugation_frequency_fraction {T : ℝ} (hT : 0 ≤ T) (k : ℕ) :
    (T/corrugationFrequency k)^((7:ℝ)/8) = T^((7:ℝ)/8)/((k:ℝ)+1)^7 := by
  rw [Real.div_rpow hT (corrugationFrequency_positive k).le,corrugationFrequency,
    ← Real.rpow_natCast ((k:ℝ)+1) 8,← Real.rpow_mul (by positivity)]
  norm_num

lemma corrugationLowErrorRate_formula {L T : ℝ} (hL : L ≠ 0) (hT : 0 ≤ T) (k : ℕ) :
    corrugationLowErrorRate L T k =
      (L⁻¹*T^((7:ℝ)/8))/((k:ℝ)+1)^5 + (L^2)⁻¹/((k:ℝ)+1)^4 +
      T/((k:ℝ)+1)^8 + L⁻¹/((k:ℝ)+1)^6 := by
  rw [corrugationLowErrorRate,corrugation_frequency_fraction hT,
    (corrugation_scale_rate_identities hL k).2.1,(corrugation_scale_rate_identities hL k).2.2.1,
    corrugationScale_formula,corrugationFrequency]
  have hk : (k:ℝ)+1 ≠ 0 := by positivity
  field_simp

lemma corrugationLowRadialRate_formula {L T : ℝ} (hT : 0 ≤ T) (k : ℕ) :
    corrugationLowRadialRate L T k = (L^2*T^((7:ℝ)/8))/((k:ℝ)+1)^3 := by
  rw [corrugationLowRadialRate,corrugation_frequency_fraction hT,corrugationScale_formula,corrugationFrequency]
  have hk : (k:ℝ)+1 ≠ 0 := by positivity
  field_simp

lemma corrugation_low_rates_tendsto {L T : ℝ} (hL : L ≠ 0) (hT : 0 ≤ T) :
    Tendsto (corrugationLowErrorRate L T) atTop (𝓝 0) ∧
    Tendsto (corrugationLowRadialRate L T) atTop (𝓝 0) := by
  constructor
  · change Tendsto (fun k ↦ corrugationLowErrorRate L T k) atTop (𝓝 0)
    simp_rw [corrugationLowErrorRate_formula hL hT]
    have h1 := corrugation_power_reciprocal_tendsto (L⁻¹*T^((7:ℝ)/8)) (by norm_num : (5:ℕ) ≠ 0)
    have h2 := corrugation_power_reciprocal_tendsto (L^2)⁻¹ (by norm_num : (4:ℕ) ≠ 0)
    have h3 := corrugation_power_reciprocal_tendsto T (by norm_num : (8:ℕ) ≠ 0)
    have h4 := corrugation_power_reciprocal_tendsto L⁻¹ (by norm_num : (6:ℕ) ≠ 0)
    simpa using ((h1.add h2).add h3).add h4
  · change Tendsto (fun k ↦ corrugationLowRadialRate L T k) atTop (𝓝 0)
    simp_rw [corrugationLowRadialRate_formula hT]
    exact corrugation_power_reciprocal_tendsto _ (by norm_num)

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_CorrugationHighRegime
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Real Filter
open scoped Topology
noncomputable section

lemma corrugation_high_regime_lower {χ l J T : ℝ}
    (hχ : 0 ≤ χ) (hχ1 : χ ≤ 1) (hl : 0 ≤ l) (hl1 : l ≤ 1)
    (hJ : 0 < J) (hT : 0 < T) (hreg : T < J*χ*l) :
    0 < χ ∧ 0 < l ∧ T/J ≤ χ ∧ T/J ≤ l := by
  have hp : T/J < χ*l := (div_lt_iff₀ hJ).mpr (by nlinarith)
  have hχl1 := mul_le_mul_of_nonneg_left hl1 hχ
  have hχl2 := mul_le_mul_of_nonneg_right hχ1 hl
  have ht := div_pos hT hJ
  refine ⟨by nlinarith,by nlinarith,?_,?_⟩ <;> nlinarith

lemma corrugation_fractional_factor {x : ℝ} (hx : 0 < x) :
    x^((7:ℝ)/8) = x*x^(-(1:ℝ)/8) := by
  calc
    _ = x^((1:ℝ)+(-(1:ℝ)/8)) := by norm_num
    _ = x^(1:ℝ)*x^(-(1:ℝ)/8) := Real.rpow_add hx _ _
    _ = _ := by rw [Real.rpow_one]

lemma corrugation_high_regime_products {χ l J T : ℝ}
    (hχ : 0 ≤ χ) (hχ1 : χ ≤ 1) (hl : 0 ≤ l) (hl1 : l ≤ 1)
    (hJ : 0 < J) (hT : 0 < T) (hreg : T < J*χ*l) :
    χ^((7:ℝ)/8)*l ≤ (T/J)^(-(1:ℝ)/8)*(χ*l) ∧
    l^((7:ℝ)/8) ≤ (T/J)^(-(1:ℝ)/8)*l := by
  obtain ⟨hc,hlp,hcT,hlT⟩ := corrugation_high_regime_lower hχ hχ1 hl hl1 hJ hT hreg
  have h1 := Real.rpow_le_rpow_of_nonpos (div_pos hT hJ) hcT (by norm_num : -(1:ℝ)/8 ≤ 0)
  have h2 := Real.rpow_le_rpow_of_nonpos (div_pos hT hJ) hlT (by norm_num : -(1:ℝ)/8 ≤ 0)
  constructor
  · rw [corrugation_fractional_factor hc]
    have hh := mul_le_mul_of_nonneg_right h1 (mul_nonneg hχ hl)
    nlinarith
  · rw [corrugation_fractional_factor hlp]
    nlinarith [mul_le_mul_of_nonneg_right h2 hl]

lemma corrugationHighErrorRate_bounds {χ l L T : ℝ} (hL : 0 < L) (hT : 0 < T) (k : ℕ)
    (hχ : 0 ≤ χ) (hχ1 : χ ≤ 1) (hl : 0 ≤ l) (hl1 : l ≤ 1)
    (hreg : T < corrugationFrequency k*χ*l) :
    (corrugationScale L k)⁻¹*χ^((7:ℝ)/8)*l +
      (corrugationFrequency k*(corrugationScale L k)^2)⁻¹ + χ*l +
      (corrugationFrequency k*corrugationScale L k)⁻¹ ≤
        corrugationHighErrorRate L T k*(corrugationFrequency k*χ*l) ∧
    (corrugationScale L k)^2*l^((7:ℝ)/8) ≤ corrugationHighRadialRate L T k*l := by
  have hJ := corrugationFrequency_positive k
  have hR := corrugationScale_positive hL k
  obtain ⟨h1,h2⟩ := corrugation_high_regime_products hχ hχ1 hl hl1 hJ hT hreg
  have htinv : (1:ℝ) ≤ (corrugationFrequency k*χ*l)/T :=
    (one_le_div hT).mpr hreg.le
  constructor
  · unfold corrugationHighErrorRate
    have hb1 := mul_le_mul_of_nonneg_left h1 (inv_nonneg.mpr hR.le)
    have hb2 := mul_le_mul_of_nonneg_left htinv
      (inv_nonneg.mpr (mul_nonneg hJ.le (sq_nonneg (corrugationScale L k))))
    have hb4 := mul_le_mul_of_nonneg_left htinv (inv_nonneg.mpr (mul_nonneg hJ.le hR.le))
    have he1 : (corrugationScale L k)⁻¹*((T/corrugationFrequency k)^(-(1:ℝ)/8)*(χ*l)) =
        ((corrugationFrequency k*corrugationScale L k)⁻¹*(T/corrugationFrequency k)^(-(1:ℝ)/8))*
          (corrugationFrequency k*χ*l) := by field_simp
    have he3 : χ*l = (corrugationFrequency k)⁻¹*(corrugationFrequency k*χ*l) := by field_simp
    rw [← mul_assoc] at hb1
    rw [he1] at hb1
    simp only [div_eq_mul_inv] at hb1 hb2 hb4 he3 ⊢
    nlinarith
  · unfold corrugationHighRadialRate
    have hh := mul_le_mul_of_nonneg_left h2 (sq_nonneg (corrugationScale L k))
    nlinarith

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_CorrugationRadialLoss
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Real
noncomputable section

theorem corrugation_actual_radial_loss : ∃ C : ℝ, 0 < C ∧
    ∀ (amp r χ L T : ℝ), 0 ≤ amp → amp ≤ 1 → 0 ≤ r →
      0 ≤ χ → χ ≤ 1 → 0 < L → 0 < T → ∀ k : ℕ,
      let l := corrugationSlope amp (1/4) r
      let d := max (-(deriv (corrugationSlope amp (1/4)) r)) 0
      (corrugationFrequency k*χ*l ≤ T →
        (corrugationScale L k)^2*corrugationFrequency k*χ*d ≤ C*corrugationLowRadialRate L T k) ∧
      (T < corrugationFrequency k*χ*l →
        (corrugationScale L k)^2*d ≤ C*corrugationHighRadialRate L T k*l) := by
  obtain ⟨C,hC,hbound⟩ := corrugationSlope_fractional_bound
  refine ⟨C,hC,?_⟩
  intro amp r χ L T hamp hamp1 hr hχ hχ1 hL hT k l d
  have hd : d ≤ C*l^((7:ℝ)/8) := hbound amp (1/4) r hamp hamp1 (by norm_num) (by norm_num) hr
  have hl : 0 ≤ l := corrugationSlope_nonneg hamp hr
  have hl1 : l ≤ 1 := corrugationSlope_le_one hamp hamp1 (by norm_num) (by norm_num) hr
  have hJ := corrugationFrequency_positive k
  constructor
  · intro hreg
    have h1 := mul_le_mul_of_nonneg_left hd
      (mul_nonneg (mul_nonneg (sq_nonneg (corrugationScale L k)) hJ.le) hχ)
    have h2 := mul_le_mul_of_nonneg_left
      (corrugationLowErrorRate_bounds hL T k hχ hχ1 hl hl1 hreg).2 hC.le
    nlinarith
  · intro hreg
    have h1 := mul_le_mul_of_nonneg_left hd (sq_nonneg (corrugationScale L k))
    have h2 := mul_le_mul_of_nonneg_left
      (corrugationHighErrorRate_bounds hL hT k hχ hχ1 hl hl1 hreg).2 hC.le
    nlinarith

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_WeightedHessianStability
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Yau.Jets Set
noncomputable section

lemma weightedHessianValue_normalized (g H : _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ)
    (p t : _root_.OAI.Yau.Jets.Coord) (hp : 0 < g p p) :
    weightedHessianValue g H p t =
      (g p p/(g p p+4))*H (metricNormalize g p) (metricNormalize g p)+H t t := by
  have hs := Real.sq_sqrt hp.le
  have hs0 := (Real.sqrt_pos.mpr hp).ne'
  have hd : g p p+4 ≠ 0 := by positivity
  unfold weightedHessianValue metricNormalize
  simp only [map_smul,smul_apply,smul_eq_mul]
  field_simp
  rw [hs]
  ring

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_CorrugationLowAdmissibility
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Yau.Jets Set Filter
open scoped ContDiff Topology
noncomputable section

theorem corrugation_actual_low_admissibility
    (g : _root_.OAI.Yau.Jets.Coord → _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ) (S χ : _root_.OAI.Yau.Jets.Coord → ℝ)
    {D U : Set _root_.OAI.Yau.Jets.Coord} (hD : IsCompact D) (hconv : Convex ℝ D)
    (hU : IsOpen U) (hDU : D ⊆ U)
    (hg : ContDiffOn ℝ ∞ g U) (hS : ContDiffOn ℝ ∞ S U)
    (hp : ∀ y ∈ U, ∀ v, v ≠ 0 → 0 < g y v v)
    (hsym : ∀ y ∈ D, ∀ u v, g y u v = g y v u)
    (hadm : ∀ y ∈ D, metricGradient g S y ≠ 0 ∧
      ∃ q : _root_.OAI.Yau.Jets.Coord, g y q q = 1 ∧ g y (metricGradient g S y) q = 0 ∧
        0 < sourceHessian g S y (metricGradient g S y) (metricGradient g S y) +
          (g y (metricGradient g S y) (metricGradient g S y)+4)*sourceHessian g S y q q)
    (hχ : ContDiff ℝ ∞ χ) (hcpt : HasCompactSupport χ)
    (hχ0 : ∀ x, 0 ≤ χ x) (hχ1 : ∀ x, χ x ≤ 1)
    {Aχ : ℝ} (hAχ : 0 < Aχ)
    (hχA : ∀ z, ‖fderiv ℝ χ z‖ ≤ Aχ*(χ z)^((7:ℝ)/8))
    {amp L : ℝ} (ha : 0 ≤ amp) (ha1 : amp ≤ 1) (hL : 0 < L) :
    ∃ c : ℝ, 0 < c ∧ ∀ T : ℝ, 0 < T → ∀ᶠ k : ℕ in atTop,
      ∀ y ∈ D, ∀ x ∈ D, ‖x-y‖ ≤ corrugationScale L k →
      ∀ e : _root_.OAI.Yau.Jets.Coord ≃L[ℝ] _root_.OAI.Yau.Jets.Coord,
      e (Pi.single 0 1) = (corrugationOldSlope g S y)⁻¹ • metricGradient g S y →
      (∀ i j, g y (e (Pi.single i 1)) (e (Pi.single j 1)) = if i=j then 1 else 0) →
      (∀ u, g y u u = 1 → g y (metricGradient g S y) u = 0 →
        sourceHessian g S y u u ≤ sourceHessian g S y (e (Pi.single 1 1)) (e (Pi.single 1 1))) →
      let z := corrugationFastMap (corrugationFrequency k) (frozenFrameCovector e 2) (frozenFrameCovector e 3) (x-y)
      let p := metricGradient g (S+localizedCorrugation χ (corrugationPeriodicWell amp)
        (corrugationOldSlope g S y) (corrugationFrequency k) (corrugationScale L k)
        (frozenFrameCovector e 2) (frozenFrameCovector e 3) y) x
      let q := metricPerpProjection (g x) (metricNormalize (g x) p) (e (Pi.single 1 1))
      let t := metricNormalize (g x) q
      corrugationFrequency k*χ ((corrugationScale L k)⁻¹ • (x-y))*
        corrugationSlope amp (1/4) (corrugationCellRadius z) ≤ T →
      q ≠ 0 ∧ g x t t = 1 ∧ g x (metricNormalize (g x) p) t = 0 ∧
        c ≤ (g x p p/(g x p p+4))*sourceHessian g (S+localizedCorrugation χ (corrugationPeriodicWell amp)
          (corrugationOldSlope g S y) (corrugationFrequency k) (corrugationScale L k)
          (frozenFrameCovector e 2) (frozenFrameCovector e 3) y) x (metricNormalize (g x) p)
          (metricNormalize (g x) p)+sourceHessian g (S+localizedCorrugation χ (corrugationPeriodicWell amp)
          (corrugationOldSlope g S y) (corrugationFrequency k) (corrugationScale L k)
          (frozenFrameCovector e 2) (frozenFrameCovector e 3) y) x t t := by
  have hn : ∀ y ∈ D, metricGradient g S y ≠ 0 := fun y hy ↦ (hadm y hy).1
  obtain ⟨c,hc,hmargin⟩ := corrugation_actual_low_old_margin g S χ hD hconv hU hDU
    hg hS hp hsym hadm hχ hcpt hχ0 hχ1 ha ha1 hL
  obtain ⟨m,hm,B,hB,hslope⟩ := corrugationOldSlope_compact_bounds g S hD hU hDU hg hS hp hn
  obtain ⟨E,hE,herror⟩ := corrugation_actual_metric_unit_errors g χ hD hU hDU hg hp hχ hcpt
    (fun z ↦ ⟨hχ0 z,hχ1 z⟩) hAχ hχA ha ha1
  obtain ⟨D₀,hD₀,hloss⟩ := corrugation_actual_radial_loss
  have hnv := corrugation_local_nonvanishing g S χ hD hconv hU hDU hg hS hp hn hχ hcpt amp hL
  refine ⟨c/2,half_pos hc,?_⟩
  intro T hT
  obtain ⟨C,hC,hrad⟩ := corrugation_actual_low_radial g S χ hD hconv hU hDU hg hS hp hn
    hχ hcpt hχ0 hχ1 ha ha1 hL T
  have hlim := corrugation_low_rates_tendsto hL.ne' hT.le
  have hsmall : Tendsto (fun k ↦ 2*(B*C^2*D₀*corrugationLowRadialRate L T k)+
      2*(E*B*corrugationLowErrorRate L T k)) atTop (𝓝 0) := by
    simpa using ((hlim.2.const_mul (B*C^2*D₀)).const_mul 2).add ((hlim.1.const_mul (E*B)).const_mul 2)
  filter_upwards [hmargin T,hrad,hnv,hsmall.eventually_lt_const (half_pos hc)] with k hkm hkr hknv hks
  intro y hy x hx hxy e he0 he hmax
  dsimp only
  intro hreg
  let s := corrugationOldSlope g S y
  let J := corrugationFrequency k
  let R := corrugationScale L k
  let a := frozenFrameCovector e 2
  let b := frozenFrameCovector e 3
  let z := corrugationFastMap J a b (x-y)
  let χ₀ := χ (R⁻¹ • (x-y))
  let w := localizedCorrugation χ (corrugationPeriodicWell amp) s J R a b y
  let p := metricGradient g (S+w) x
  let e' := metricNormalize (g x) p
  let q := metricPerpProjection (g x) e' (e (Pi.single 1 1))
  let t := metricNormalize (g x) q
  let ν := g x p p/(g x p p+4)
  let d := max (-deriv (corrugationSlope amp (1/4)) (corrugationCellRadius z)) 0
  let F : _root_.OAI.Yau.Jets.Coord → ℝ := fun v ↦ s*J*χ₀*
    fderiv ℝ (fderiv ℝ (corrugationPeriodicWell amp)) z (a.prod b v) (a.prod b v)
  let Err : _root_.OAI.Yau.Jets.Coord → ℝ := fun v ↦ corrugationMetricError g χ (corrugationPeriodicWell amp) s J R a b y x v v
  let BF := B*C^2*D₀*corrugationLowRadialRate L T k
  let BE := E*B*corrugationLowErrorRate L T k
  have hs : 0 < s := corrugationOldSlope_positive g S y (hp y (hDU hy)) (hn y hy)
  have hsB : s ≤ B := (hslope y hy).2
  have hJ : 0 < J := corrugationFrequency_positive k
  have hR : 0 < R := corrugationScale_positive hL k
  have hχ₀ : 0 ≤ χ₀ := hχ0 _
  have hd : 0 ≤ d := le_max_right _ _
  have hlr : 0 ≤ corrugationLowRadialRate L T k := by
    unfold corrugationLowRadialRate; positivity
  have her : 0 ≤ corrugationLowErrorRate L T k := by
    unfold corrugationLowErrorRate; positivity
  have hBF : 0 ≤ BF := by dsimp [BF] <;> positivity
  have hBE : 0 ≤ BE := by dsimp [BE] <;> positivity
  obtain ⟨hnq,htu,hto,hold⟩ := hkm y hy x hx hxy e he0 he hmax hreg
  have hp0 : 0 < g x p p := hp x (hDU hx) p (hknv y hy x hx hxy e he0 he)
  have heu : g x e' e' = 1 := metricNormalize_unit (g x) p hp0
  have hν0 : 0 ≤ ν := div_nonneg hp0.le (by positivity)
  have hν1 : ν ≤ 1 := (div_le_one (by positivity)).mpr (by linarith)
  have hradial : R^2*J*χ₀*d ≤ D₀*corrugationLowRadialRate L T k :=
    (hloss amp (corrugationCellRadius z) χ₀ L T ha ha1 (corrugationCellRadius_properties z).1
      hχ₀ (hχ1 _) hL hT k).1 hreg
  have hfb (v : _root_.OAI.Yau.Jets.Coord) (hv : corrugationCellRadius z ≠ 0 →
      |radialComponent (corrugationCellPoint z) (a.prod b v) (corrugationCellRadius z)| ≤ C*R) : -BF ≤ F v := by
    have hf := mul_le_mul_of_nonneg_left (corrugation_fast_hessian_lower ha (mul_nonneg hC.le hR.le) z (a.prod b v) hv)
      (mul_nonneg (mul_nonneg hs.le hJ.le) hχ₀)
    have hrb := mul_le_mul_of_nonneg_left hradial (mul_nonneg hs.le (sq_nonneg C))
    have hsb := mul_le_mul_of_nonneg_right hsB
      (mul_nonneg (mul_nonneg (sq_nonneg C) hD₀.le) hlr)
    change -(B*C^2*D₀*corrugationLowRadialRate L T k) ≤ F v
    change s*J*χ₀*(-(d*(C*R)^2)) ≤ F v at hf
    nlinarith only [hf,hrb,hsb]
  have hfe : -BF ≤ F e' := hfb e' (by
    intro hr
    rw [frozen_radial_covector (g y) e he]
    exact (hkr y hy x hx hxy e he0 he hr hreg).1)
  have hft : -BF ≤ F t := hfb t (by
    intro hr
    rw [frozen_radial_covector (g y) e he]
    exact (hkr y hy x hx hxy e he0 he hr hreg).2)
  have heb (v : _root_.OAI.Yau.Jets.Coord) (hv : g x v v = 1) : |Err v| ≤ BE := by
    have hb := (herror s L hs.le hL k y hy x hx e he v v hv hv T hT).1 hreg
    exact hb.trans (by dsimp [BE]; gcongr)
  have hdecomp (v : _root_.OAI.Yau.Jets.Coord) : sourceHessian g (S+w) x v v = sourceHessian g S x v v+F v+Err v :=
    corrugated_envelope_global_hessian g S χ (hS.contDiffAt (hU.mem_nhds (hDU hx))) hχ
      amp s hJ.ne' R a b y v v
  have hbound := weighted_hessian_perturbation_lower
    (H₁ := sourceHessian g S x e' e') (H₂ := sourceHessian g S x t t) hν0 hν1 hBF hBE hfe hft (heb e' heu) (heb t htu)
  have hnew : c/2 ≤ ν*sourceHessian g (S+w) x e' e'+sourceHessian g (S+w) x t t := by
    rw [hdecomp e',hdecomp t]
    change c ≤ ν*sourceHessian g S x e' e'+sourceHessian g S x t t at hold
    change 2*BF+2*BE < c/2 at hks
    linarith
  exact ⟨hnq,htu,hto,hnew⟩

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_NormalizedAdmissibility
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Yau.Jets
noncomputable section

lemma normalized_strict_to_direction (g H : _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ)
    (p t : _root_.OAI.Yau.Jets.Coord) (hp : 0 < g p p)
    (horth : g (metricNormalize g p) t = 0)
    (hstrict : 0 < (g p p/(g p p+4))*H (metricNormalize g p) (metricNormalize g p)+H t t) :
    g p t = 0 ∧ 0 < H p p+(g p p+4)*H t t := by
  have hs0 : Real.sqrt (g p p) ≠ 0 := (Real.sqrt_pos.mpr hp).ne'
  have horth' : (Real.sqrt (g p p))⁻¹*g p t = 0 := by
    simpa only [metricNormalize,map_smul,smul_apply,smul_eq_mul] using horth
  have hpt : g p t = 0 := (mul_eq_zero.mp horth').resolve_left (inv_ne_zero hs0)
  have hval : 0 < weightedHessianValue g H p t := by
    rw [weightedHessianValue_normalized g H p t hp]
    exact hstrict
  have hd : 0 < g p p+4 := by linarith
  have hmul := mul_pos hd hval
  have heq : (g p p+4)*weightedHessianValue g H p t = H p p+(g p p+4)*H t t := by
    unfold weightedHessianValue
    field_simp
  rw [heq] at hmul
  exact ⟨hpt,hmul⟩

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_CorrugationLocalAdmissibility
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Yau.Jets Set Filter
open scoped ContDiff Topology
noncomputable section

theorem corrugation_fixed_local_admissibility
    (g : _root_.OAI.Yau.Jets.Coord → _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ) (S χ : _root_.OAI.Yau.Jets.Coord → ℝ)
    {D U : Set _root_.OAI.Yau.Jets.Coord} (hD : IsCompact D) (hconv : Convex ℝ D)
    (hU : IsOpen U) (hDU : D ⊆ U)
    (hg : ContDiffOn ℝ ∞ g U) (hS : ContDiffOn ℝ ∞ S U)
    (hp : ∀ y ∈ U, ∀ v, v ≠ 0 → 0 < g y v v)
    (hsym : ∀ y ∈ D, ∀ u v, g y u v = g y v u)
    (hadm : ∀ y ∈ D, metricGradient g S y ≠ 0 ∧
      ∃ q : _root_.OAI.Yau.Jets.Coord, g y q q = 1 ∧ g y (metricGradient g S y) q = 0 ∧
        0 < sourceHessian g S y (metricGradient g S y) (metricGradient g S y) +
          (g y (metricGradient g S y) (metricGradient g S y)+4)*sourceHessian g S y q q)
    (hχ : ContDiff ℝ ∞ χ) (hcpt : HasCompactSupport χ)
    (hχ0 : ∀ x, 0 ≤ χ x) (hχ1 : ∀ x, χ x ≤ 1)
    {Aχ : ℝ} (hAχ : 0 < Aχ)
    (hχA : ∀ z, ‖fderiv ℝ χ z‖ ≤ Aχ*(χ z)^((7:ℝ)/8))
    {L : ℝ} (hL : 0 < L) :
    ∀ᶠ k : ℕ in atTop,
      ∀ y ∈ D, ∀ x ∈ D, ‖x-y‖ ≤ corrugationScale L k →
      ∀ e : _root_.OAI.Yau.Jets.Coord ≃L[ℝ] _root_.OAI.Yau.Jets.Coord,
      e (Pi.single 0 1) = (corrugationOldSlope g S y)⁻¹ • metricGradient g S y →
      (∀ i j, g y (e (Pi.single i 1)) (e (Pi.single j 1)) = if i=j then 1 else 0) →
      (∀ u, g y u u = 1 → g y (metricGradient g S y) u = 0 →
        sourceHessian g S y u u ≤ sourceHessian g S y (e (Pi.single 1 1)) (e (Pi.single 1 1))) →
      let w := localizedCorrugation χ (corrugationPeriodicWell corrugationFixedAmplitude)
        (corrugationOldSlope g S y) (corrugationFrequency k) (corrugationScale L k)
        (frozenFrameCovector e 2) (frozenFrameCovector e 3) y
      let p := metricGradient g (S+w) x
      p ≠ 0 ∧ ∃ t : _root_.OAI.Yau.Jets.Coord, g x t t = 1 ∧ g x p t = 0 ∧
        0 < sourceHessian g (S+w) x p p+(g x p p+4)*sourceHessian g (S+w) x t t := by
  obtain ⟨ha,ha1,hprod,_⟩ := corrugationFixedAmplitude_spec
  have hn : ∀ y ∈ D, metricGradient g S y ≠ 0 := fun y hy ↦ (hadm y hy).1
  obtain ⟨c,hc,hlow⟩ := corrugation_actual_low_admissibility g S χ hD hconv hU hDU hg hS hp
    hsym hadm hχ hcpt hχ0 hχ1 hAχ hχA ha.le ha1 hL
  obtain ⟨T,hT,hhigh⟩ := corrugation_actual_high_admissibility g S χ hD hconv hU hDU hg hS hp hn
    hχ hcpt hχ0 hχ1 hAχ hχA ha.le ha1 hL hprod
  have hnv := corrugation_local_nonvanishing g S χ hD hconv hU hDU hg hS hp hn hχ hcpt corrugationFixedAmplitude hL
  filter_upwards [hlow T hT,hhigh,hnv] with k hkl hkh hknv
  intro y hy x hx hxy e he0 he hmax
  dsimp only
  let w := localizedCorrugation χ (corrugationPeriodicWell corrugationFixedAmplitude)
    (corrugationOldSlope g S y) (corrugationFrequency k) (corrugationScale L k)
    (frozenFrameCovector e 2) (frozenFrameCovector e 3) y
  let p := metricGradient g (S+w) x
  have hnP : p ≠ 0 := hknv y hy x hx hxy e he0 he
  have hpP : 0 < g x p p := hp x (hDU hx) p hnP
  refine ⟨hnP,?_⟩
  have finish (t : _root_.OAI.Yau.Jets.Coord) (htu : g x t t = 1) (horth : g x (metricNormalize (g x) p) t = 0)
      (hstr : 0 < (g x p p/(g x p p+4))*sourceHessian g (S+w) x (metricNormalize (g x) p)
        (metricNormalize (g x) p)+sourceHessian g (S+w) x t t) :
      ∃ t : _root_.OAI.Yau.Jets.Coord, g x t t = 1 ∧ g x p t = 0 ∧
        0 < sourceHessian g (S+w) x p p+(g x p p+4)*sourceHessian g (S+w) x t t := by
    obtain ⟨ho,hs⟩ := normalized_strict_to_direction (g x) (sourceHessian g (S+w) x) p t hpP horth hstr
    exact ⟨t,htu,ho,hs⟩
  let z := corrugationFastMap (corrugationFrequency k) (frozenFrameCovector e 2) (frozenFrameCovector e 3) (x-y)
  rcases le_or_gt (corrugationFrequency k*χ ((corrugationScale L k)⁻¹ • (x-y))*
      corrugationSlope corrugationFixedAmplitude (1/4) (corrugationCellRadius z)) T with hreg | hreg
  · obtain ⟨_,hu,ho,hs⟩ := hkl y hy x hx hxy e he0 he hmax hreg
    exact finish _ hu ho (hc.trans_le hs)
  · obtain ⟨_,hu,ho,hs⟩ := hkh y hy x hx hxy e he0 he hreg
    exact finish _ hu ho (zero_lt_one.trans_le hs)

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_CorrugationGridAdmissibility
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Yau.Jets Set Filter Metric
open scoped ContDiff Topology
noncomputable section

theorem corrugation_grid_admissibility_oai (o : _root_.OAI.Yau.Jets.Coord) {L : ℝ} (hL : 0 < L)
    (g : _root_.OAI.Yau.Jets.Coord → _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ) (S χ : _root_.OAI.Yau.Jets.Coord → ℝ)
    {U : Set _root_.OAI.Yau.Jets.Coord} (hU : IsOpen U) (hDU : Icc o (fun i ↦ o i+L) ⊆ U)
    (hg : ContDiffOn ℝ ∞ g U) (hS : ContDiffOn ℝ ∞ S U)
    (hp : ∀ y ∈ U, ∀ v, v ≠ 0 → 0 < g y v v)
    (hsym : ∀ y ∈ Icc o (fun i ↦ o i+L), ∀ u v, g y u v = g y v u)
    (hadm : ∀ y ∈ Icc o (fun i ↦ o i+L), metricGradient g S y ≠ 0 ∧
      ∃ q : _root_.OAI.Yau.Jets.Coord, g y q q = 1 ∧ g y (metricGradient g S y) q = 0 ∧
        0 < sourceHessian g S y (metricGradient g S y) (metricGradient g S y) +
          (g y (metricGradient g S y) (metricGradient g S y)+4)*sourceHessian g S y q q)
    (hχ : ContDiff ℝ ∞ χ) (hχsupp : tsupport χ ⊆ ball (0:_root_.OAI.Yau.Jets.Coord) (1/2))
    (hχ0 : ∀ z, 0 ≤ χ z) (hχ1 : ∀ z, χ z ≤ 1)
    {Aχ : ℝ} (hAχ : 0 < Aχ) (hχA : ∀ z, ‖fderiv ℝ χ z‖ ≤ Aχ*(χ z)^((7:ℝ)/8)) :
    ∀ᶠ k : ℕ in atTop,
      ∀ e : (Fin 4 → Fin (corrugationSubdivision k)) → _root_.OAI.Yau.Jets.Coord ≃L[ℝ] _root_.OAI.Yau.Jets.Coord,
      (∀ i, e i (Pi.single 0 1) =
        (corrugationOldSlope g S (corrugationCubeCenter o L (corrugationSubdivision k) i))⁻¹ •
          metricGradient g S (corrugationCubeCenter o L (corrugationSubdivision k) i)) →
      (∀ i a b, g (corrugationCubeCenter o L (corrugationSubdivision k) i)
        (e i (Pi.single a 1)) (e i (Pi.single b 1)) = if a=b then 1 else 0) →
      (∀ i, let y := corrugationCubeCenter o L (corrugationSubdivision k) i
        ∀ v, g y v v = 1 → g y (metricGradient g S y) v = 0 →
          sourceHessian g S y v v ≤ sourceHessian g S y (e i (Pi.single 1 1)) (e i (Pi.single 1 1))) →
      ∀ x ∈ Icc o (fun i ↦ o i+L),
        let W := corrugationEnvelopePerturbation o L k g S χ corrugationFixedAmplitude e
        let p := metricGradient g (S+W) x
        p ≠ 0 ∧ ∃ t : _root_.OAI.Yau.Jets.Coord, g x t t = 1 ∧ g x p t = 0 ∧
          0 < sourceHessian g (S+W) x p p+(g x p p+4)*sourceHessian g (S+W) x t t := by
  have hc : HasCompactSupport χ :=
    (isCompact_closedBall (0:_root_.OAI.Yau.Jets.Coord) (1/2)).of_isClosed_subset isClosed_closure
      (hχsupp.trans ball_subset_closedBall)
  have hevent := corrugation_fixed_local_admissibility g S χ isCompact_Icc (convex_Icc o (fun i ↦ o i+L))
    hU hDU hg hS hp hsym hadm hχ hc hχ0 hχ1 hAχ hχA hL
  filter_upwards [hevent] with k hk
  intro e he0 he hmax x hx
  dsimp only
  let n := corrugationSubdivision k
  let y := corrugationCubeCenter o L n
  let s := fun i ↦ corrugationOldSlope g S (y i)
  let w := fun i ↦ localizedCorrugation χ (corrugationPeriodicWell corrugationFixedAmplitude) (s i)
    (corrugationFrequency k) (corrugationScale L k) (frozenFrameCovector (e i) 2)
    (frozenFrameCovector (e i) 3) (y i)
  have hR := corrugationScale_positive hL k
  have hd : ∀ i ∈ (Finset.univ : Finset (Fin 4 → Fin n)), ∀ j ∈ Finset.univ,
      i ≠ j → Disjoint (tsupport (w i)) (tsupport (w j)) := by
    intro i _ j _ hij
    exact (corrugationCube_balls_disjoint o hL (corrugationSubdivision_positive k) i j hij).mono
      (localizedCorrugation_cube χ _ hχsupp _ _ hR _ _ _)
      (localizedCorrugation_cube χ _ hχsupp _ _ hR _ _ _)
  have hsum : corrugationEnvelopePerturbation o L k g S χ corrugationFixedAmplitude e =
      (fun z ↦ ∑ i ∈ (Finset.univ : Finset (Fin 4 → Fin n)), w i z) := rfl
  by_cases hactive : ∃ i : Fin 4 → Fin n, x ∈ tsupport (w i)
  · obtain ⟨i,hi⟩ := hactive
    have heq := finite_disjoint_sum_eventually Finset.univ w hd (Finset.mem_univ i) hi
    rw [← hsum] at heq
    have heq' : S+corrugationEnvelopePerturbation o L k g S χ corrugationFixedAmplitude e =ᶠ[𝓝 x] S+w i :=
      Filter.EventuallyEq.add Filter.EventuallyEq.rfl heq
    have hy : y i ∈ Icc o (fun j ↦ o j+L) :=
      corrugationCubeCenter_mem o hL (corrugationSubdivision_positive k) i
    have hxy : ‖x-y i‖ ≤ corrugationScale L k := by
      have hh := localizedCorrugation_cube χ _ hχsupp _ _ hR _ _ _ hi
      rw [mem_ball,dist_eq_norm] at hh
      linarith
    have hnlocal := hk (y i) hy x hx hxy (e i) (he0 i) (he i) (hmax i)
    have hgrad : metricGradient g (S+corrugationEnvelopePerturbation o L k g S χ corrugationFixedAmplitude e) x =
        metricGradient g (S+w i) x := by
      unfold metricGradient
      rw [heq'.fderiv_eq]
    have hhess := (sourceHessian_eventuallyEq (Filter.EventuallyEq.rfl (f := g)) heq').self_of_nhds
    rw [hgrad,hhess]
    exact hnlocal
  · have hzero : corrugationEnvelopePerturbation o L k g S χ corrugationFixedAmplitude e =ᶠ[𝓝 x] 0 := by
      apply notMem_tsupport_iff_eventuallyEq.mp
      rw [hsum]
      intro hmem
      have hsupp := finite_sum_support_subset Finset.univ w {z | ∃ i, z ∈ tsupport (w i)}
        (fun i _ z hz ↦ ⟨i,hz⟩)
      exact hactive (hsupp hmem)
    have heq : S+corrugationEnvelopePerturbation o L k g S χ corrugationFixedAmplitude e =ᶠ[𝓝 x] S := by
      simpa using Filter.EventuallyEq.add (Filter.EventuallyEq.rfl (f := S)) hzero
    have hgrad : metricGradient g (S+corrugationEnvelopePerturbation o L k g S χ corrugationFixedAmplitude e) x =
        metricGradient g S x := by
      unfold metricGradient
      rw [heq.fderiv_eq]
    have hhess := (sourceHessian_eventuallyEq (Filter.EventuallyEq.rfl (f := g)) heq).self_of_nhds
    rw [hgrad,hhess]
    exact hadm x hx

end
end Yau.Geometry

end OAI
end

theorem solution : type_of% @OAI.Yau.Geometry.corrugation_grid_admissibility_oai := @OAI.Yau.Geometry.corrugation_grid_admissibility_oai
