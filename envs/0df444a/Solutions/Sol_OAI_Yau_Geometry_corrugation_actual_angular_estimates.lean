-- Prove2me | solution 1 for OAI.Yau.Geometry.corrugation_actual_angular_estimates
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T00:28:38.629207+00:00
-- url     : https://prove2.me/submissions/e59cf67a-89fd-4c9e-9e89-5dafe33737bf

import Mathlib
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
import Mathlib.Analysis.Calculus.ContDiff.Operations
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
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.Finsupp.Weight
import Mathlib.Data.Matrix.Basic
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.LinearAlgebra.Basis.SMul
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
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
import Mathlib.Topology.Order.Compact
import Definitions.Def_OAIQ237Ny002
import Theorems.Thm_OAI_Yau_Geometry_corrugation_projected_direction_freezing

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

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_CorrugationWellSlope
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Real Set
open scoped ContDiff
noncomputable section

lemma corrugationSlope_center (a R : ℝ) : corrugationSlope a R 0 = 0 := by
  simp [corrugationSlope]

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

lemma corrugationPeriodicWell_cell_eventually (a : ℝ) (z : ℝ × ℝ)
    (hz₁ : |z.1| < 1/2) (hz₂ : |z.2| < 1/2) :
    corrugationPeriodicWell a =ᶠ[𝓝 z] corrugationDiskWell a (1/4) := by
  have h1 : ∀ᶠ w : ℝ × ℝ in 𝓝 z, |w.1| < 1/2 :=
    continuous_fst.abs.continuousAt.eventually_lt_const hz₁
  have h2 : ∀ᶠ w : ℝ × ℝ in 𝓝 z, |w.2| < 1/2 :=
    continuous_snd.abs.continuousAt.eventually_lt_const hz₂
  filter_upwards [h1,h2] with w hw1 hw2
  exact corrugationPeriodicWell_cell a w hw1.le hw2.le

lemma corrugationPeriodicWell_cell_jets (a : ℝ) (z : ℝ × ℝ)
    (hz₁ : |z.1| < 1/2) (hz₂ : |z.2| < 1/2) :
    fderiv ℝ (corrugationPeriodicWell a) z = fderiv ℝ (corrugationDiskWell a (1/4)) z ∧
    fderiv ℝ (fderiv ℝ (corrugationPeriodicWell a)) z =
      fderiv ℝ (fderiv ℝ (corrugationDiskWell a (1/4))) z := by
  have h := corrugationPeriodicWell_cell_eventually a z hz₁ hz₂
  exact ⟨h.fderiv_eq,h.fderiv.fderiv_eq⟩

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

end

open Yau.Jets Set Filter
open scoped ContDiff Topology

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

lemma corrugationPeriodicWell_radial_jets (a : ℝ) (m : ℤ × ℤ) (z : ℝ × ℝ)
    (hz₁ : |z.1| < 1/2) (hz₂ : |z.2| < 1/2) {r : ℝ}
    (hr : r ≠ 0) (hz : r^2=z.1^2+z.2^2) (u v : ℝ × ℝ) :
    fderiv ℝ (corrugationPeriodicWell a) (z.1+(m.1:ℝ),z.2+(m.2:ℝ)) v =
      corrugationSlope a (1/4) r*radialComponent z v r ∧
    fderiv ℝ (fderiv ℝ (corrugationPeriodicWell a)) (z.1+(m.1:ℝ),z.2+(m.2:ℝ)) u v =
      deriv (corrugationSlope a (1/4)) r*radialComponent z u r*radialComponent z v r +
      (corrugationSlope a (1/4) r/r)*angularComponent z u r*angularComponent z v r := by
  have hs := corrugationPeriodicWell_shift_jets a m z
  have hc := corrugationPeriodicWell_cell_jets a z hz₁ hz₂
  rw [hs.1,hs.2,hc.1,hc.2]
  exact ⟨corrugationDiskWell_radial_first a (1/4) z v hr hz,
    corrugationDiskWell_radial_second a (1/4) z u v hr hz⟩

lemma radialComponent_bound (z v : ℝ × ℝ) {r : ℝ} (hr : 0 < r)
    (hz : r^2=z.1^2+z.2^2) : |radialComponent z v r| ≤ 2*‖v‖ := by
  have h1 : |z.1| ≤ r := by nlinarith [sq_abs z.1,sq_nonneg z.2,abs_nonneg z.1]
  have h2 : |z.2| ≤ r := by nlinarith [sq_abs z.2,sq_nonneg z.1,abs_nonneg z.2]
  have hv1 : |v.1| ≤ ‖v‖ := by simpa only [Real.norm_eq_abs] using norm_fst_le v
  have hv2 : |v.2| ≤ ‖v‖ := by simpa only [Real.norm_eq_abs] using norm_snd_le v
  rw [radialComponent,abs_div,abs_of_pos hr]
  apply (div_le_iff₀ hr).mpr
  calc
    _ ≤ |z.1| *|v.1|+|z.2| *|v.2| := by simpa only [abs_mul] using abs_add_le (z.1*v.1) (z.2*v.2)
    _ ≤ r*‖v‖+r*‖v‖ := add_le_add (mul_le_mul h1 hv1 (abs_nonneg _) hr.le)
      (mul_le_mul h2 hv2 (abs_nonneg _) hr.le)
    _ = _ := by ring

lemma corrugationPeriodicWell_derivative_bound {a : ℝ} (ha : 0 ≤ a)
    (m : ℤ × ℤ) (z : ℝ × ℝ) (hz₁ : |z.1| < 1/2) (hz₂ : |z.2| < 1/2)
    {r : ℝ} (hr : 0 < r) (hz : r^2=z.1^2+z.2^2) :
    ‖fderiv ℝ (corrugationPeriodicWell a) (z.1+(m.1:ℝ),z.2+(m.2:ℝ))‖ ≤
      2*corrugationSlope a (1/4) r := by
  have hl := corrugationSlope_nonneg (R := (1/4:ℝ)) ha hr.le
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro v
  rw [Real.norm_eq_abs,(corrugationPeriodicWell_radial_jets a m z hz₁ hz₂ hr.ne' hz v v).1,
    abs_mul,abs_of_nonneg hl]
  exact (mul_le_mul_of_nonneg_left (radialComponent_bound z v hr hz) hl).trans_eq (by ring)

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_CorrugationPeriodicFlatJets
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Real
noncomputable section

lemma corrugationPeriodicWell_center_first (a : ℝ) (m : ℤ × ℤ) :
    fderiv ℝ (corrugationPeriodicWell a) ((m.1:ℝ),(m.2:ℝ)) = 0 := by
  have hs := (corrugationPeriodicWell_shift_jets a m 0).1
  have hc := (corrugationPeriodicWell_cell_jets a 0 (by norm_num) (by norm_num)).1
  simp only [Prod.fst_zero,Prod.snd_zero,zero_add] at hs
  rw [hs,hc]
  apply ContinuousLinearMap.ext
  intro v
  simp [corrugationDiskWell_fderiv]

lemma corrugationPeriodicWell_derivative_bound_nonneg {a : ℝ} (ha : 0 ≤ a)
    (m : ℤ × ℤ) (z : ℝ × ℝ) (hz₁ : |z.1| < 1/2) (hz₂ : |z.2| < 1/2)
    {r : ℝ} (hr : 0 ≤ r) (hz : r^2=z.1^2+z.2^2) :
    ‖fderiv ℝ (corrugationPeriodicWell a) (z.1+(m.1:ℝ),z.2+(m.2:ℝ))‖ ≤
      2*corrugationSlope a (1/4) r := by
  rcases hr.eq_or_lt with hr | hr
  · have hz1 : z.1 = 0 := by nlinarith [sq_nonneg z.2]
    have hz2 : z.2 = 0 := by nlinarith [sq_nonneg z.1]
    rw [← hr,hz1,hz2,zero_add,zero_add,corrugationPeriodicWell_center_first]
    simp [corrugationSlope_center]
  · exact corrugationPeriodicWell_derivative_bound ha m z hz₁ hz₂ hr hz

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

lemma corrugationPeriodicWell_boundary_plateau (a : ℝ) (z : ℝ × ℝ)
    (hz₁ : |z.1| ≤ 1/2) (hz₂ : |z.2| ≤ 1/2)
    (hb : |z.1| = 1/2 ∨ |z.2| = 1/2) :
    corrugationPeriodicWell a =ᶠ[𝓝 z] 0 := by
  have hz : (1/4:ℝ)^2 < z.1^2+z.2^2 := by
    rcases hb with h | h
    · have he := sq_abs z.1
      rw [h] at he
      nlinarith [sq_nonneg z.2]
    · have he := sq_abs z.2
      rw [h] at he
      nlinarith [sq_nonneg z.1]
  have hnear : ∀ᶠ w : ℝ × ℝ in 𝓝 z, (1/4:ℝ)^2 < w.1^2+w.2^2 :=
    ((continuous_fst.pow 2).add (continuous_snd.pow 2)).continuousAt.eventually_const_lt hz
  filter_upwards [corrugationPeriodicWell_closed_cell_eventually a z hz₁ hz₂,hnear] with w hw hr
  exact hw.trans (corrugationDiskWell_zero hr.le)

lemma corrugationPeriodicWell_closed_derivative_bound {a : ℝ} (ha : 0 ≤ a)
    (m : ℤ × ℤ) (z : ℝ × ℝ) (hz₁ : |z.1| ≤ 1/2) (hz₂ : |z.2| ≤ 1/2)
    {r : ℝ} (hr : 0 ≤ r) (hz : r^2=z.1^2+z.2^2) :
    ‖fderiv ℝ (corrugationPeriodicWell a) (z.1+(m.1:ℝ),z.2+(m.2:ℝ))‖ ≤
      2*corrugationSlope a (1/4) r := by
  by_cases h1 : |z.1| < 1/2
  · by_cases h2 : |z.2| < 1/2
    · exact corrugationPeriodicWell_derivative_bound_nonneg ha m z h1 h2 hr hz
    · have hp := corrugationPeriodicWell_boundary_plateau a z hz₁ hz₂
        (Or.inr (le_antisymm hz₂ (le_of_not_gt h2)))
      rw [(corrugationPeriodicWell_shift_jets a m z).1,hp.fderiv_eq]
      simpa using mul_nonneg (show (0:ℝ) ≤ 2 by norm_num) (corrugationSlope_nonneg ha hr)
  · have hp := corrugationPeriodicWell_boundary_plateau a z hz₁ hz₂
      (Or.inl (le_antisymm hz₁ (le_of_not_gt h1)))
    rw [(corrugationPeriodicWell_shift_jets a m z).1,hp.fderiv_eq]
    simpa using mul_nonneg (show (0:ℝ) ≤ 2 by norm_num) (corrugationSlope_nonneg ha hr)

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

lemma corrugationPeriodicWell_global_derivative_bound {a : ℝ} (ha : 0 ≤ a) (z : ℝ × ℝ) :
    ‖fderiv ℝ (corrugationPeriodicWell a) z‖ ≤
      2*corrugationSlope a (1/4) (corrugationCellRadius z) := by
  have h := corrugationPeriodicWell_closed_derivative_bound ha (corrugationCellIndex z)
    (corrugationCellPoint z) (corrugationCellPoint_bounds z).1 (corrugationCellPoint_bounds z).2
    (corrugationCellRadius_properties z).1 (corrugationCellRadius_properties z).2
  rwa [corrugationCellPoint_reconstruct] at h

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
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_CorrugationLeadingVector
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Yau.Jets
noncomputable section

lemma pair_covector_expansion (d : (ℝ × ℝ) →L[ℝ] ℝ) (v : ℝ × ℝ) :
    d v = d (1,0)*v.1+d (0,1)*v.2 := by
  have he : v = v.1 • (1,0)+v.2 • (0,1) := by ext <;> simp
  conv_lhs => rw [he,map_add,map_smul,map_smul]
  simp only [smul_eq_mul]
  ring

lemma corrugationFastVector_pair (g : _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ)
    (e : _root_.OAI.Yau.Jets.Coord ≃L[ℝ] _root_.OAI.Yau.Jets.Coord)
    (he : ∀ i j, g (e (Pi.single i 1)) (e (Pi.single j 1)) = if i=j then 1 else 0)
    (amp : ℝ) (z : ℝ × ℝ) (v : _root_.OAI.Yau.Jets.Coord) :
    g (corrugationFastVector amp e z) v =
      fderiv ℝ (corrugationPeriodicWell amp) z
        ((frozenFrameCovector e 2).prod (frozenFrameCovector e 3) v) := by
  rw [pair_covector_expansion]
  simp only [corrugationFastVector,map_add,map_smul,add_apply,
    smul_apply,smul_eq_mul,ContinuousLinearMap.prod_apply]
  rw [frozenFrameCovector_metric g e he,frozenFrameCovector_metric g e he]

lemma corrugationFastVector_bound (g : _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ)
    {c amp : ℝ} (hc : 0 < c) (hg : ∀ v, c*‖v‖^2 ≤ g v v)
    (ha : 0 ≤ amp) (e : _root_.OAI.Yau.Jets.Coord ≃L[ℝ] _root_.OAI.Yau.Jets.Coord)
    (he : ∀ i j, g (e (Pi.single i 1)) (e (Pi.single j 1)) = if i=j then 1 else 0)
    (z : ℝ × ℝ) :
    ‖corrugationFastVector amp e z‖ ≤
      4*corrugationSlope amp (1/4) (corrugationCellRadius z)*(1+c⁻¹) := by
  have hd := corrugationPeriodicWell_global_derivative_bound ha z
  have h2 := metric_unit_coordinate_bound g hc hg (e (Pi.single 2 1)) (by simpa using he 2 2)
  have h3 := metric_unit_coordinate_bound g hc hg (e (Pi.single 3 1)) (by simpa using he 3 3)
  have hd2 : |fderiv ℝ (corrugationPeriodicWell amp) z (1,0)| ≤
      2*corrugationSlope amp (1/4) (corrugationCellRadius z) := by
    simpa using ((fderiv ℝ (corrugationPeriodicWell amp) z).le_opNorm (1,0)).trans
      (mul_le_mul_of_nonneg_right hd (norm_nonneg (1,0)))
  have hd3 : |fderiv ℝ (corrugationPeriodicWell amp) z (0,1)| ≤
      2*corrugationSlope amp (1/4) (corrugationCellRadius z) := by
    simpa using ((fderiv ℝ (corrugationPeriodicWell amp) z).le_opNorm (0,1)).trans
      (mul_le_mul_of_nonneg_right hd (norm_nonneg (0,1)))
  have hl := corrugationSlope_nonneg (R := (1/4:ℝ)) ha (corrugationCellRadius_properties z).1
  calc
    _ ≤ ‖fderiv ℝ (corrugationPeriodicWell amp) z (1,0) • e (Pi.single 2 1)‖+
        ‖fderiv ℝ (corrugationPeriodicWell amp) z (0,1) • e (Pi.single 3 1)‖ := norm_add_le _ _
    _ ≤ (2*corrugationSlope amp (1/4) (corrugationCellRadius z))*(1+c⁻¹)+
        (2*corrugationSlope amp (1/4) (corrugationCellRadius z))*(1+c⁻¹) := by
      simp only [norm_smul,Real.norm_eq_abs]
      exact add_le_add (mul_le_mul hd2 h2 (norm_nonneg _) (by positivity))
        (mul_le_mul hd3 h3 (norm_nonneg _) (by positivity))
    _ = _ := by ring

lemma corrugationLeadingVector_bound (g : _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ)
    {c amp t : ℝ} (hc : 0 < c) (hg : ∀ v, c*‖v‖^2 ≤ g v v)
    (ha : 0 ≤ amp) (ha1 : amp ≤ 1) (ht : 0 ≤ t) (ht1 : t ≤ 1)
    (e : _root_.OAI.Yau.Jets.Coord ≃L[ℝ] _root_.OAI.Yau.Jets.Coord)
    (he : ∀ i j, g (e (Pi.single i 1)) (e (Pi.single j 1)) = if i=j then 1 else 0)
    (z : ℝ × ℝ) : ‖corrugationLeadingVector amp t e z‖ ≤ 5*(1+c⁻¹) := by
  have h0 := metric_unit_coordinate_bound g hc hg (e (Pi.single 0 1)) (by simpa using he 0 0)
  have hf := corrugationFastVector_bound g hc hg ha e he z
  have hl := corrugationSlope_le_one ha ha1 (by norm_num : (0:ℝ) ≤ 1/4) (by norm_num)
    (corrugationCellRadius_properties z).1
  have hf' : ‖corrugationFastVector amp e z‖ ≤ 4*(1+c⁻¹) := hf.trans (mul_le_mul_of_nonneg_right (by linarith) (by positivity))
  calc
    _ ≤ ‖e (Pi.single 0 1)‖+‖t • corrugationFastVector amp e z‖ := norm_add_le _ _
    _ ≤ (1+c⁻¹)+1*(4*(1+c⁻¹)) := by
      rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg ht]
      exact add_le_add h0 (mul_le_mul ht1 hf' (norm_nonneg _) (by norm_num))
    _ = _ := by ring

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

lemma frozenPlaneVector_pair (g : _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ)
    (e : _root_.OAI.Yau.Jets.Coord ≃L[ℝ] _root_.OAI.Yau.Jets.Coord)
    (he : ∀ i j, g (e (Pi.single i 1)) (e (Pi.single j 1)) = if i=j then 1 else 0)
    (α β γ δ : ℝ) :
    g (frozenPlaneVector e α β) (frozenPlaneVector e γ δ) = α*γ+β*δ := by
  simp [frozenPlaneVector,map_add,map_smul,he,Fin.ext_iff]
  ring

lemma frozenPlaneVector_axis_pair (g : _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ)
    (e : _root_.OAI.Yau.Jets.Coord ≃L[ℝ] _root_.OAI.Yau.Jets.Coord)
    (he : ∀ i j, g (e (Pi.single i 1)) (e (Pi.single j 1)) = if i=j then 1 else 0)
    (α β : ℝ) (i : Fin 4) (hi : i < 2) :
    g (e (Pi.single i 1)) (frozenPlaneVector e α β) = 0 ∧
    g (frozenPlaneVector e α β) (e (Pi.single i 1)) = 0 := by
  have hi2 : i ≠ 2 := by omega
  have hi3 : i ≠ 3 := by omega
  simp [frozenPlaneVector,map_add,map_smul,he,hi2,hi3,Ne.symm hi2,Ne.symm hi3]

lemma frozenPlaneVector_rotating_frame (g : _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ)
    (e : _root_.OAI.Yau.Jets.Coord ≃L[ℝ] _root_.OAI.Yau.Jets.Coord)
    (he : ∀ i j, g (e (Pi.single i 1)) (e (Pi.single j 1)) = if i=j then 1 else 0)
    {α β : ℝ} (hunit : α^2+β^2 = 1) :
    g (frozenPlaneVector e α β) (frozenPlaneVector e α β) = 1 ∧
    g (frozenPlaneVector e (-β) α) (frozenPlaneVector e (-β) α) = 1 ∧
    g (frozenPlaneVector e α β) (frozenPlaneVector e (-β) α) = 0 ∧
    g (frozenPlaneVector e (-β) α) (frozenPlaneVector e α β) = 0 := by
  simp only [frozenPlaneVector_pair g e he]
  constructor
  · nlinarith only [hunit]
  constructor
  · nlinarith only [hunit]
  constructor <;> ring

lemma corrugationFastVector_radial (amp : ℝ) (e : _root_.OAI.Yau.Jets.Coord ≃L[ℝ] _root_.OAI.Yau.Jets.Coord) (z : ℝ × ℝ)
    (hr : corrugationCellRadius z ≠ 0) :
    corrugationFastVector amp e z = corrugationSlope amp (1/4) (corrugationCellRadius z) •
      frozenPlaneVector e ((corrugationCellPoint z).1/corrugationCellRadius z)
        ((corrugationCellPoint z).2/corrugationCellRadius z) := by
  unfold corrugationFastVector
  rw [(corrugationPeriodicWell_global_radial_jets amp z (0,0) (1,0) hr).1,
    (corrugationPeriodicWell_global_radial_jets amp z (0,0) (0,1) hr).1]
  simp [radialComponent,frozenPlaneVector,smul_add,smul_smul]

lemma corrugation_cell_unit_coefficients (z : ℝ × ℝ) (hr : corrugationCellRadius z ≠ 0) :
    ((corrugationCellPoint z).1/corrugationCellRadius z)^2+
      ((corrugationCellPoint z).2/corrugationCellRadius z)^2 = 1 := by
  have hh := (corrugationCellRadius_properties z).2
  field_simp
  nlinarith only [hh]

lemma corrugationLeadingVector_metric_length (g : _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ)
    (e : _root_.OAI.Yau.Jets.Coord ≃L[ℝ] _root_.OAI.Yau.Jets.Coord)
    (he : ∀ i j, g (e (Pi.single i 1)) (e (Pi.single j 1)) = if i=j then 1 else 0)
    (amp t : ℝ) (z : ℝ × ℝ) (hr : corrugationCellRadius z ≠ 0) :
    g (corrugationLeadingVector amp t e z) (corrugationLeadingVector amp t e z) =
      1+(t*corrugationSlope amp (1/4) (corrugationCellRadius z))^2 := by
  let u := frozenPlaneVector e ((corrugationCellPoint z).1/corrugationCellRadius z)
    ((corrugationCellPoint z).2/corrugationCellRadius z)
  have huu : g u u = 1 := (frozenPlaneVector_rotating_frame g e he
    (corrugation_cell_unit_coefficients z hr)).1
  have hu0 := frozenPlaneVector_axis_pair g e he
    ((corrugationCellPoint z).1/corrugationCellRadius z)
    ((corrugationCellPoint z).2/corrugationCellRadius z) 0 (by decide)
  change g (e (Pi.single 0 1)) u = 0 ∧ g u (e (Pi.single 0 1)) = 0 at hu0
  change g (e (Pi.single 0 1)+t • corrugationFastVector amp e z)
    (e (Pi.single 0 1)+t • corrugationFastVector amp e z) = _
  rw [corrugationFastVector_radial amp e z hr]
  change g (e (Pi.single 0 1)+t • (corrugationSlope amp (1/4) (corrugationCellRadius z) • u))
    (e (Pi.single 0 1)+t • (corrugationSlope amp (1/4) (corrugationCellRadius z) • u)) = _
  simp only [map_add,map_smul,add_apply,smul_apply,
    smul_eq_mul,huu,hu0.1,hu0.2,he]
  simp
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

lemma bilinear_pairing_bound (g : _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ) (u v : _root_.OAI.Yau.Jets.Coord) :
    |g u v| ≤ ‖g‖*‖u‖*‖v‖ :=
  ((g u).le_opNorm v).trans (mul_le_mul_of_nonneg_right (g.le_opNorm u) (norm_nonneg v))

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Charts_MetricNormalizationBounds
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Yau.Jets
noncomputable section

lemma bilinear_diagonal_change_bound
    (g h : _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ) (v w : _root_.OAI.Yau.Jets.Coord)
    {M K δ η : ℝ} (hM : 0 ≤ M) (hK : 0 ≤ K)
    (hg : ‖g‖ ≤ M) (hv : ‖v‖ ≤ K) (hw : ‖w‖ ≤ K)
    (hvw : ‖v-w‖ ≤ δ) (hgh : ‖g-h‖ ≤ η) :
    |g v v-h w w| ≤ 2*M*K*δ+η*K^2 := by
  have hδ : 0 ≤ δ := (norm_nonneg _).trans hvw
  have hη : 0 ≤ η := (norm_nonneg (g-h)).trans hgh
  have h1 : |g (v-w) v| ≤ M*δ*K := (bilinear_pairing_bound g _ _).trans (by gcongr)
  have h2 : |g w (v-w)| ≤ M*K*δ := (bilinear_pairing_bound g _ _).trans (by gcongr)
  have h3 : |(g-h) w w| ≤ η*K*K := (bilinear_pairing_bound _ _ _).trans (by gcongr)
  have hid : g v v-h w w = g (v-w) v+g w (v-w)+(g-h) w w := by
    simp only [map_sub,sub_apply]
    ring
  rw [hid]
  calc
    _ ≤ (|g (v-w) v|+|g w (v-w)|)+|(g-h) w w| := (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ (M*δ*K+M*K*δ)+η*K*K := add_le_add (add_le_add h1 h2) h3
    _ = _ := by ring

lemma inverse_sqrt_difference_bound {a b m E : ℝ} (hm : 0 < m)
    (ha : m^2 ≤ a) (hb : m^2 ≤ b) (hab : |a-b| ≤ E) :
    |(Real.sqrt a)⁻¹-(Real.sqrt b)⁻¹| ≤ E/m^3 := by
  have ha0 : 0 < a := (sq_pos_of_pos hm).trans_le ha
  have hb0 : 0 < b := (sq_pos_of_pos hm).trans_le hb
  have hu : 0 < Real.sqrt a := Real.sqrt_pos.mpr ha0
  have hv : 0 < Real.sqrt b := Real.sqrt_pos.mpr hb0
  have hmu : m ≤ Real.sqrt a := (Real.le_sqrt hm.le ha0.le).mpr ha
  have hmv : m ≤ Real.sqrt b := (Real.le_sqrt hm.le hb0.le).mpr hb
  have hden : m^3 ≤ Real.sqrt a*Real.sqrt b*(Real.sqrt a+Real.sqrt b) := by
    calc
      m^3 = m*m*m := by ring
      _ ≤ Real.sqrt a*Real.sqrt b*(Real.sqrt a+Real.sqrt b) :=
        mul_le_mul (mul_le_mul hmu hmv hm.le hu.le) (by linarith) hm.le (mul_nonneg hu.le hv.le)
  have hid : (Real.sqrt a)⁻¹-(Real.sqrt b)⁻¹ =
      (b-a)/(Real.sqrt a*Real.sqrt b*(Real.sqrt a+Real.sqrt b)) := by
    have h1 := Real.sq_sqrt ha0.le
    have h2 := Real.sq_sqrt hb0.le
    field_simp
    nlinarith only [h1,h2]
  rw [hid,abs_div,abs_of_pos (by positivity : 0 < Real.sqrt a*Real.sqrt b*(Real.sqrt a+Real.sqrt b)),abs_sub_comm]
  exact div_le_div₀ ((abs_nonneg _).trans hab) hab (by positivity) hden

lemma metricNormalize_difference_bound
    (g h : _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ) (v w : _root_.OAI.Yau.Jets.Coord)
    {M K m δ η : ℝ} (hM : 0 ≤ M) (hK : 0 ≤ K) (hm : 0 < m)
    (hg : ‖g‖ ≤ M) (hv : ‖v‖ ≤ K) (hw : ‖w‖ ≤ K)
    (hvw : ‖v-w‖ ≤ δ) (hgh : ‖g-h‖ ≤ η)
    (hlenv : m^2 ≤ g v v) (hlenw : m^2 ≤ h w w) :
    ‖metricNormalize g v-metricNormalize h w‖ ≤
      δ/m+K*(2*M*K*δ+η*K^2)/m^3 := by
  have ha0 : 0 < g v v := (sq_pos_of_pos hm).trans_le hlenv
  have ha := Real.sqrt_pos.mpr ha0
  have hma : m ≤ Real.sqrt (g v v) := (Real.le_sqrt hm.le ha0.le).mpr hlenv
  have hinv : (Real.sqrt (g v v))⁻¹ ≤ m⁻¹ := inv_anti₀ hm hma
  have hdiag := bilinear_diagonal_change_bound g h v w hM hK hg hv hw hvw hgh
  have hdiff := inverse_sqrt_difference_bound hm hlenv hlenw hdiag
  have hE : 0 ≤ 2*M*K*δ+η*K^2 := (abs_nonneg _).trans hdiag
  have hid : metricNormalize g v-metricNormalize h w =
      (Real.sqrt (g v v))⁻¹ • (v-w)+
      ((Real.sqrt (g v v))⁻¹-(Real.sqrt (h w w))⁻¹) • w := by
    unfold metricNormalize
    module
  rw [hid]
  calc
    _ ≤ ‖(Real.sqrt (g v v))⁻¹ • (v-w)‖+
        ‖((Real.sqrt (g v v))⁻¹-(Real.sqrt (h w w))⁻¹) • w‖ := norm_add_le _ _
    _ ≤ m⁻¹*δ+((2*M*K*δ+η*K^2)/m^3)*K := by
      simp only [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr ha)]
      exact add_le_add (mul_le_mul hinv hvw (norm_nonneg _) (by positivity))
        (mul_le_mul hdiff hw (norm_nonneg _) (by positivity))
    _ = _ := by ring

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Charts_MetricNormalizationStabilityLemmas
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Yau.Geometry

open Yau.Jets

theorem metric_normalization_uniform_stability {M K : ℝ} (hM : 0 ≤ M) (hK : 0 ≤ K) :
    ∃ ε₀ C : ℝ, 0 < ε₀ ∧ 0 < C ∧
      ∀ (g h : _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ) (v w : _root_.OAI.Yau.Jets.Coord) (ε : ℝ),
      ‖g‖ ≤ M → ‖w‖ ≤ K → 1 ≤ h w w →
      ‖v-w‖ ≤ ε → ‖g-h‖ ≤ ε → ε ≤ ε₀ →
      1/2 ≤ g v v ∧ v ≠ 0 ∧
        ‖metricNormalize g v-metricNormalize h w‖ ≤ C*ε := by
  let H : ℝ := 2*M*(K+1)+(K+1)^2
  have hH : 0 ≤ H := by dsimp [H] <;> positivity
  let ε₀ : ℝ := min 1 (1/(2*(H+1)))
  let C : ℝ := 2+8*(K+1)*H
  have hε₀ : 0 < ε₀ := lt_min zero_lt_one (by positivity)
  have hC : 0 < C := by dsimp [C] <;> positivity
  refine ⟨ε₀,C,hε₀,hC,?_⟩
  intro g h v w ε hg hw hlen hd hm hε
  have hε0 : 0 ≤ ε := (norm_nonneg _).trans hd
  have hε1 : ε ≤ 1 := hε.trans (min_le_left _ _)
  have hε2 : ε ≤ 1/(2*(H+1)) := hε.trans (min_le_right _ _)
  have hsmall : H*ε ≤ 1/2 := by
    have hh := (le_div_iff₀ (by positivity : 0 < 2*(H+1))).mp hε2
    nlinarith
  have hv : ‖v‖ ≤ K+1 := by
    calc
      ‖v‖ ≤ ‖v-w‖+‖w‖ := norm_le_norm_sub_add _ _
      _ ≤ ε+K := add_le_add hd hw
      _ ≤ K+1 := by linarith
  have hw' : ‖w‖ ≤ K+1 := hw.trans (by linarith)
  have hb := bilinear_diagonal_change_bound g h v w hM (by linarith : 0 ≤ K+1) hg hv hw' hd hm
  have hdiag : |g v v-h w w| ≤ H*ε := hb.trans_eq (by dsimp [H] <;> ring)
  have hpos : 1/2 ≤ g v v := by
    have hh := (abs_le.mp hdiag).1
    linarith
  have hn : v ≠ 0 := by
    intro hz
    simp only [hz,map_zero] at hpos
    norm_num at hpos
  refine ⟨hpos,hn,?_⟩
  have hnorm := metricNormalize_difference_bound g h v w hM (by linarith : 0 ≤ K+1)
    (by norm_num : (0:ℝ) < 1/2) hg hv hw' hd hm (by linarith) (by linarith)
  apply hnorm.trans_eq
  dsimp [C,H]
  ring

end Yau.Geometry

end

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

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Coefficients_CorrugationFirstResidual
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

lemma corrugationLeadingVector_pair
    (g : _root_.OAI.Yau.Jets.Coord → _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ) (S : _root_.OAI.Yau.Jets.Coord → ℝ)
    (y : _root_.OAI.Yau.Jets.Coord) (hp : ∀ v, v ≠ 0 → 0 < g y v v)
    (hn : metricGradient g S y ≠ 0) (e : _root_.OAI.Yau.Jets.Coord ≃L[ℝ] _root_.OAI.Yau.Jets.Coord)
    (he0 : e (Pi.single 0 1) = (corrugationOldSlope g S y)⁻¹ • metricGradient g S y)
    (he : ∀ i j, g y (e (Pi.single i 1)) (e (Pi.single j 1)) = if i=j then 1 else 0)
    (amp t : ℝ) (z : ℝ × ℝ) (v : _root_.OAI.Yau.Jets.Coord) :
    g y (corrugationOldSlope g S y • corrugationLeadingVector amp t e z) v =
      fderiv ℝ S y v + corrugationOldSlope g S y*t*
        fderiv ℝ (corrugationPeriodicWell amp) z
          ((frozenFrameCovector e 2).prod (frozenFrameCovector e 3) v) := by
  have hs := corrugationOldSlope_positive g S y hp hn
  simp only [corrugationLeadingVector,map_smul,map_add,smul_apply,
    add_apply,smul_eq_mul]
  rw [he0,map_smul,smul_apply,smul_eq_mul,
    metricGradient_pair g S y hp,corrugationFastVector_pair (g y) e he]
  field_simp

lemma corrugation_cutoff_residual_bound (χ : _root_.OAI.Yau.Jets.Coord → ℝ)
    (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ) (amp : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (s J R : ℝ), 0 ≤ s → 0 < J → 0 < R →
      ∀ (a b : _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ) (y x v : _root_.OAI.Yau.Jets.Coord),
      |fderiv ℝ (localizedCorrugation χ (corrugationPeriodicWell amp) s J R a b y) x v -
        s*χ (R⁻¹ • (x-y))*fderiv ℝ (corrugationPeriodicWell amp)
          (corrugationFastMap J a b (x-y)) (a.prod b v)| ≤ s/(J*R)*C*‖v‖ := by
  obtain ⟨B,hB,hf⟩ := corrugationPeriodicWell_bounded amp
  obtain ⟨M,hM,hd⟩ := compact_first_derivative_bound χ hχ hc
  refine ⟨B*M,mul_pos hB hM,?_⟩
  intro s J R hs hJ hR a b y x v
  rw [localizedCorrugation_first_scaled χ _ hχ (corrugationPeriodicWell_smooth amp) s hJ.ne']
  rw [add_sub_cancel_left,abs_mul,abs_mul,abs_of_nonneg (div_nonneg hs (mul_pos hJ hR).le)]
  have hder : |fderiv ℝ χ (R⁻¹ • (x-y)) v| ≤ M*‖v‖ :=
    ((fderiv ℝ χ _).le_opNorm v).trans (mul_le_mul_of_nonneg_right (hd _) (norm_nonneg v))
  calc
    _ ≤ (s/(J*R)*B)*(M*‖v‖) := mul_le_mul
      (mul_le_mul_of_nonneg_left (hf _) (by positivity)) hder (abs_nonneg _) (by positivity)
    _ = _ := by ring

theorem corrugation_frozen_differential_bound
    (g : _root_.OAI.Yau.Jets.Coord → _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ) (S χ : _root_.OAI.Yau.Jets.Coord → ℝ)
    (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ) (amp : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (J R A : ℝ), 0 < J → 0 < R → 0 ≤ A →
      ∀ (y x : _root_.OAI.Yau.Jets.Coord), (∀ v, v ≠ 0 → 0 < g y v v) →
      metricGradient g S y ≠ 0 → DifferentiableAt ℝ S x → ‖x-y‖ ≤ R →
      (∀ v, |fderiv ℝ S x v-fderiv ℝ S y v| ≤ A*‖x-y‖*‖v‖) →
      ∀ e : _root_.OAI.Yau.Jets.Coord ≃L[ℝ] _root_.OAI.Yau.Jets.Coord,
      e (Pi.single 0 1) = (corrugationOldSlope g S y)⁻¹ • metricGradient g S y →
      (∀ i j, g y (e (Pi.single i 1)) (e (Pi.single j 1)) = if i=j then 1 else 0) →
      ∀ v, |fderiv ℝ (S+localizedCorrugation χ (corrugationPeriodicWell amp)
        (corrugationOldSlope g S y) J R (frozenFrameCovector e 2) (frozenFrameCovector e 3) y) x v -
        g y (corrugationOldSlope g S y • corrugationLeadingVector amp (χ (R⁻¹ • (x-y))) e
          (corrugationFastMap J (frozenFrameCovector e 2) (frozenFrameCovector e 3) (x-y))) v| ≤
        (A*R+corrugationOldSlope g S y/(J*R)*C)*‖v‖ := by
  obtain ⟨C,hC,hres⟩ := corrugation_cutoff_residual_bound χ hχ hc amp
  refine ⟨C,hC,?_⟩
  intro J R A hJ hR hA y x hp hn hS hxy hfreeze e he0 he v
  have hs := corrugationOldSlope_positive g S y hp hn
  have hw := (localizedCorrugation_smooth χ _ hχ (corrugationPeriodicWell_smooth amp)
    (corrugationOldSlope g S y) J R (frozenFrameCovector e 2) (frozenFrameCovector e 3) y).differentiable (by simp)
  rw [fderiv_add hS hw.differentiableAt,add_apply,
    corrugationLeadingVector_pair g S y hp hn e he0 he]
  have hr := hres (corrugationOldSlope g S y) J R hs.le hJ hR
    (frozenFrameCovector e 2) (frozenFrameCovector e 3) y x v
  calc
    _ ≤ |fderiv ℝ S x v-fderiv ℝ S y v|+
        |fderiv ℝ (localizedCorrugation χ (corrugationPeriodicWell amp)
          (corrugationOldSlope g S y) J R (frozenFrameCovector e 2) (frozenFrameCovector e 3) y) x v -
          corrugationOldSlope g S y*χ (R⁻¹ • (x-y))*fderiv ℝ (corrugationPeriodicWell amp)
            (corrugationFastMap J (frozenFrameCovector e 2) (frozenFrameCovector e 3) (x-y))
            ((frozenFrameCovector e 2).prod (frozenFrameCovector e 3) v)| := by
      convert abs_add_le (fderiv ℝ S x v-fderiv ℝ S y v) _ using 1
      all_goals try with_reducible_and_instances rfl
      congr 1
      ring
    _ ≤ A*R*‖v‖+corrugationOldSlope g S y/(J*R)*C*‖v‖ :=
      add_le_add ((hfreeze v).trans (by gcongr)) hr
    _ = _ := by ring

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Coefficients_MetricGradientResidual
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Yau.Jets
noncomputable section

lemma coercive_vector_residual (g : _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ)
    {c E : ℝ} (hc : 0 < c) (hg : ∀ v, c*‖v‖^2 ≤ g v v)
    (w : _root_.OAI.Yau.Jets.Coord) (hres : ∀ v, |g w v| ≤ E*‖v‖) :
    ‖w‖ ≤ E/c := by
  by_cases hw : w = 0
  · have hE : 0 ≤ E := by
      have h := hres (Pi.single 0 1)
      simp only [hw,map_zero,zero_apply,abs_zero] at h
      simpa using h
    simp only [hw,norm_zero]
    exact div_nonneg hE hc.le
  have hn := norm_pos_iff.mpr hw
  have h := (hg w).trans ((le_abs_self _).trans (hres w))
  apply (le_div_iff₀ hc).mpr
  nlinarith

lemma metricGradient_residual_bound
    (g : _root_.OAI.Yau.Jets.Coord → _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ) (S : _root_.OAI.Yau.Jets.Coord → ℝ)
    (x q : _root_.OAI.Yau.Jets.Coord) {c E : ℝ} (hc : 0 < c)
    (hg : ∀ v, c*‖v‖^2 ≤ g x v v)
    (hres : ∀ v, |fderiv ℝ S x v-g x q v| ≤ E*‖v‖) :
    ‖metricGradient g S x-q‖ ≤ E/c := by
  have hp : ∀ v, v ≠ 0 → 0 < g x v v := by
    intro v hv
    exact (mul_pos hc (sq_pos_of_pos (norm_pos_iff.mpr hv))).trans_le (hg v)
  apply coercive_vector_residual (g x) hc hg
  intro v
  simpa only [map_sub,sub_apply,metricGradient_pair g S x hp v] using hres v

lemma metricGradient_frozen_residual_bound
    (g : _root_.OAI.Yau.Jets.Coord → _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ) (S : _root_.OAI.Yau.Jets.Coord → ℝ)
    (x y q : _root_.OAI.Yau.Jets.Coord) {c E A R K : ℝ} (hc : 0 < c)
    (hA : 0 ≤ A) (hR : 0 ≤ R) (hK : 0 ≤ K)
    (hg : ∀ v, c*‖v‖^2 ≤ g x v v)
    (hfreeze : ‖g x-g y‖ ≤ A*R) (hq : ‖q‖ ≤ K)
    (hres : ∀ v, |fderiv ℝ S x v-g y q v| ≤ E*‖v‖) :
    ‖metricGradient g S x-q‖ ≤ (E+A*R*K)/c := by
  apply metricGradient_residual_bound g S x q hc hg
  intro v
  have hm : |g x q v-g y q v| ≤ A*R*K*‖v‖ := by
    calc
      _ = |(g x-g y) q v| := rfl
      _ ≤ ‖g x-g y‖*‖q‖*‖v‖ := bilinear_pairing_bound _ q v
      _ ≤ A*R*K*‖v‖ :=
        mul_le_mul (mul_le_mul_of_nonneg hfreeze hq (norm_nonneg (g x-g y)) hK) le_rfl
          (norm_nonneg v) (mul_nonneg (mul_nonneg hA hR) hK)
  calc
    _ ≤ |fderiv ℝ S x v-g y q v|+|g y q v-g x q v| := abs_sub_le _ _ _
    _ ≤ E*‖v‖+A*R*K*‖v‖ := add_le_add (hres v) (by simpa [abs_sub_comm] using hm)
    _ = _ := by ring

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_CorrugationLeadingLength
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Yau.Jets
noncomputable section

lemma corrugationFastVector_center (amp : ℝ) (e : _root_.OAI.Yau.Jets.Coord ≃L[ℝ] _root_.OAI.Yau.Jets.Coord) (z : ℝ × ℝ)
    (hr : corrugationCellRadius z = 0) : corrugationFastVector amp e z = 0 := by
  have hh := (corrugationCellRadius_properties z).2
  rw [hr] at hh
  have h1 : (corrugationCellPoint z).1 = 0 := by nlinarith [sq_nonneg (corrugationCellPoint z).2]
  have h2 : (corrugationCellPoint z).2 = 0 := by nlinarith [sq_nonneg (corrugationCellPoint z).1]
  simp [corrugationFastVector,(corrugationPeriodicWell_global_jets amp z).1,
    corrugationDiskWell_fderiv,h1,h2]

lemma corrugationLeadingVector_global_length (g : _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ)
    (e : _root_.OAI.Yau.Jets.Coord ≃L[ℝ] _root_.OAI.Yau.Jets.Coord)
    (he : ∀ i j, g (e (Pi.single i 1)) (e (Pi.single j 1)) = if i=j then 1 else 0)
    (amp t : ℝ) (z : ℝ × ℝ) :
    g (corrugationLeadingVector amp t e z) (corrugationLeadingVector amp t e z) =
      1+(t*corrugationSlope amp (1/4) (corrugationCellRadius z))^2 := by
  by_cases hr : corrugationCellRadius z = 0
  · simp [corrugationLeadingVector,corrugationFastVector_center amp e z hr,hr,corrugationSlope,he]
  · exact corrugationLeadingVector_metric_length g e he amp t z hr

lemma corrugationLeadingVector_length_ge_one (g : _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ)
    (e : _root_.OAI.Yau.Jets.Coord ≃L[ℝ] _root_.OAI.Yau.Jets.Coord)
    (he : ∀ i j, g (e (Pi.single i 1)) (e (Pi.single j 1)) = if i=j then 1 else 0)
    (amp t : ℝ) (z : ℝ × ℝ) :
    1 ≤ g (corrugationLeadingVector amp t e z) (corrugationLeadingVector amp t e z) := by
  rw [corrugationLeadingVector_global_length g e he]
  linarith [sq_nonneg (t*corrugationSlope amp (1/4) (corrugationCellRadius z))]

lemma metricNormalize_positive_smul (g : _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ)
    (v : _root_.OAI.Yau.Jets.Coord) {s : ℝ} (hs : 0 < s) :
    metricNormalize g (s • v) = metricNormalize g v := by
  unfold metricNormalize
  simp only [map_smul,smul_apply,smul_eq_mul]
  have hid : s*(s*g v v) = s^2*(g v v) := by ring
  rw [hid,Real.sqrt_mul (sq_nonneg s),Real.sqrt_sq_eq_abs,abs_of_pos hs,
    mul_inv_rev,smul_smul]
  congr 1
  field_simp

lemma inverse_scaled_vector_error (p q : _root_.OAI.Yau.Jets.Coord) {s E : ℝ} (hs : 0 < s)
    (h : ‖p-s • q‖ ≤ s*E) : ‖s⁻¹ • p-q‖ ≤ E := by
  have hid : s⁻¹ • p-q = s⁻¹ • (p-s • q) := by
    rw [smul_sub,smul_smul,inv_mul_cancel₀ hs.ne',one_smul]
  rw [hid,norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hs)]
  calc
    _ ≤ s⁻¹*(s*E) := mul_le_mul_of_nonneg_left h (inv_nonneg.mpr hs.le)
    _ = E := by field_simp

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_CorrugationDirectionEvaluations
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Yau.Jets
noncomputable section

lemma corrugationLeadingVector_angular_orthogonal (g : _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ)
    (e : _root_.OAI.Yau.Jets.Coord ≃L[ℝ] _root_.OAI.Yau.Jets.Coord)
    (he : ∀ i j, g (e (Pi.single i 1)) (e (Pi.single j 1)) = if i=j then 1 else 0)
    (amp t : ℝ) (z : ℝ × ℝ) (hr : corrugationCellRadius z ≠ 0) :
    g (corrugationLeadingVector amp t e z)
      (frozenPlaneVector e (-((corrugationCellPoint z).2/corrugationCellRadius z))
        ((corrugationCellPoint z).1/corrugationCellRadius z)) = 0 := by
  have hrot := frozenPlaneVector_rotating_frame g e he (corrugation_cell_unit_coefficients z hr)
  have haxis := frozenPlaneVector_axis_pair g e he
    (-((corrugationCellPoint z).2/corrugationCellRadius z))
    ((corrugationCellPoint z).1/corrugationCellRadius z) 0 (by decide)
  simp only [corrugationLeadingVector,corrugationFastVector_radial amp e z hr,map_add,map_smul,
    add_apply,smul_apply,smul_eq_mul,haxis.1,hrot.2.2.1]
  ring

lemma corrugation_normalized_leading_radial_bound (g : _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ)
    (e : _root_.OAI.Yau.Jets.Coord ≃L[ℝ] _root_.OAI.Yau.Jets.Coord)
    (he : ∀ i j, g (e (Pi.single i 1)) (e (Pi.single j 1)) = if i=j then 1 else 0)
    {amp t : ℝ} (ha : 0 ≤ amp) (ht : 0 ≤ t) (z : ℝ × ℝ)
    (hr : corrugationCellRadius z ≠ 0) :
    |g (frozenPlaneVector e ((corrugationCellPoint z).1/corrugationCellRadius z)
      ((corrugationCellPoint z).2/corrugationCellRadius z))
      (metricNormalize g (corrugationLeadingVector amp t e z))| ≤
      t*corrugationSlope amp (1/4) (corrugationCellRadius z) := by
  let r := frozenPlaneVector e ((corrugationCellPoint z).1/corrugationCellRadius z)
    ((corrugationCellPoint z).2/corrugationCellRadius z)
  have hrr : g r r = 1 := (frozenPlaneVector_rotating_frame g e he
    (corrugation_cell_unit_coefficients z hr)).1
  have haxis : g r (e (Pi.single 0 1)) = 0 :=
    (frozenPlaneVector_axis_pair g e he _ _ 0 (by decide)).2
  have hpair : g r (corrugationLeadingVector amp t e z) =
      t*corrugationSlope amp (1/4) (corrugationCellRadius z) := by
    rw [corrugationLeadingVector,corrugationFastVector_radial amp e z hr]
    change g r (e (Pi.single 0 1)+t • (corrugationSlope amp (1/4) (corrugationCellRadius z) • r)) = _
    simp [map_add,map_smul,haxis,hrr]
  have hlen := corrugationLeadingVector_length_ge_one g e he amp t z
  have hsqrt : 1 ≤ Real.sqrt (g (corrugationLeadingVector amp t e z) (corrugationLeadingVector amp t e z)) :=
    (Real.le_sqrt (by norm_num) (by linarith)).mpr (by simpa using hlen)
  have hi : (Real.sqrt (g (corrugationLeadingVector amp t e z) (corrugationLeadingVector amp t e z)))⁻¹ ≤ 1 :=
    by simpa using inv_anti₀ zero_lt_one hsqrt
  have hl := corrugationSlope_nonneg (R := (1/4:ℝ)) ha (corrugationCellRadius_properties z).1
  change |g r (metricNormalize g (corrugationLeadingVector amp t e z))| ≤ _
  rw [metricNormalize,map_smul,smul_eq_mul,hpair,abs_of_nonneg (by positivity)]
  nlinarith [mul_nonneg ht hl]

lemma frozen_pairing_error (g : _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ) (r v w : _root_.OAI.Yau.Jets.Coord)
    {M K δ : ℝ} (hM : 0 ≤ M) (hK : 0 ≤ K)
    (hg : ‖g‖ ≤ M) (hr : ‖r‖ ≤ K) (hd : ‖v-w‖ ≤ δ) :
    |g r v-g r w| ≤ M*K*δ := by
  have hδ : 0 ≤ δ := (norm_nonneg _).trans hd
  calc
    _ = |g r (v-w)| := by rw [map_sub]
    _ ≤ ‖g‖*‖r‖*‖v-w‖ := bilinear_pairing_bound _ _ _
    _ ≤ M*K*δ := by gcongr

lemma radial_angular_transfer (g : _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ) (r t v : _root_.OAI.Yau.Jets.Coord)
    {M K δ : ℝ} (hM : 0 ≤ M) (hK : 0 ≤ K)
    (hg : ‖g‖ ≤ M) (hr : ‖r‖ ≤ K) (ht : ‖t‖ ≤ K)
    (hrt : g r t = 0) (htt : g t t = 1) (hd : ‖v-t‖ ≤ δ)
    (hsmall : M*K*δ ≤ 1/2) :
    |g r v| ≤ M*K*δ ∧ 1/2 ≤ g t v := by
  have h1 := frozen_pairing_error g r v t hM hK hg hr hd
  have h2 := frozen_pairing_error g t v t hM hK hg ht hd
  rw [hrt,sub_zero] at h1
  rw [htt] at h2
  refine ⟨h1,?_⟩
  have hh := (abs_le.mp h2).1
  linarith

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
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_CorrugationGradientFreezing
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

theorem corrugation_gradient_freezing
    (g : _root_.OAI.Yau.Jets.Coord → _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ) (S χ : _root_.OAI.Yau.Jets.Coord → ℝ)
    {D U : Set _root_.OAI.Yau.Jets.Coord} (hD : IsCompact D) (hconv : Convex ℝ D)
    (hU : IsOpen U) (hDU : D ⊆ U)
    (hg : ContDiffOn ℝ ∞ g U) (hS : ContDiffOn ℝ ∞ S U)
    (hp : ∀ y ∈ U, ∀ v, v ≠ 0 → 0 < g y v v)
    (hn : ∀ y ∈ D, metricGradient g S y ≠ 0)
    (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (hχ0 : ∀ x, 0 ≤ χ x) (hχ1 : ∀ x, χ x ≤ 1)
    {amp : ℝ} (ha : 0 ≤ amp) (ha1 : amp ≤ 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (J R : ℝ), 0 < J → 0 < R →
      ∀ y ∈ D, ∀ x ∈ D, ‖x-y‖ ≤ R →
      ∀ e : _root_.OAI.Yau.Jets.Coord ≃L[ℝ] _root_.OAI.Yau.Jets.Coord,
      e (Pi.single 0 1) = (corrugationOldSlope g S y)⁻¹ • metricGradient g S y →
      (∀ i j, g y (e (Pi.single i 1)) (e (Pi.single j 1)) = if i=j then 1 else 0) →
      ‖metricGradient g (S+localizedCorrugation χ (corrugationPeriodicWell amp)
        (corrugationOldSlope g S y) J R (frozenFrameCovector e 2) (frozenFrameCovector e 3) y) x -
        corrugationOldSlope g S y • corrugationLeadingVector amp (χ (R⁻¹ • (x-y))) e
          (corrugationFastMap J (frozenFrameCovector e 2) (frozenFrameCovector e 3) (x-y))‖ ≤
        corrugationOldSlope g S y*C*(R+1/(J*R)) := by
  obtain ⟨m,hm,B,hB,hslope⟩ := corrugationOldSlope_compact_bounds g S hD hU hDU hg hS hp hn
  obtain ⟨c,hc0,M,hM,hmetric⟩ := compact_metric_comparison g hD (hg.continuousOn.mono hDU)
    (fun y hy ↦ hp y (hDU hy))
  obtain ⟨A,hA,hdf⟩ := smooth_compact_covector_freezing S hD hconv hU hDU hS
  obtain ⟨G,hG,hgf⟩ := smooth_compact_freezing g hD hconv hU hDU hg
  obtain ⟨C,hC,hres⟩ := corrugation_frozen_differential_bound g S χ hχ hc amp
  let K : ℝ := 5*(1+c⁻¹)
  let Q : ℝ := A/m+G*K+C
  have hK : 0 < K := by dsimp [K] <;> positivity
  have hQ : 0 < Q := by dsimp [Q] <;> positivity
  refine ⟨Q/c,div_pos hQ hc0,?_⟩
  intro J R hJ hR y hy x hx hxy e he0 he
  let s : ℝ := corrugationOldSlope g S y
  let q : _root_.OAI.Yau.Jets.Coord := s • corrugationLeadingVector amp (χ (R⁻¹ • (x-y))) e
    (corrugationFastMap J (frozenFrameCovector e 2) (frozenFrameCovector e 3) (x-y))
  have hs : 0 < s := corrugationOldSlope_positive g S y (hp y (hDU hy)) (hn y hy)
  have hms : m ≤ s := (hslope y hy).1
  have hq : ‖q‖ ≤ s*K := by
    dsimp [q]
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos hs]
    exact mul_le_mul_of_nonneg_left
      (corrugationLeadingVector_bound (g y) hc0 (hmetric y hy).2 ha ha1 (hχ0 _) (hχ1 _) e he _) hs.le
  have hres' := hres J R A hJ hR hA.le y x (hp y (hDU hy)) (hn y hy)
    ((hS.contDiffAt (hU.mem_nhds (hDU hx))).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)) hxy
    (hdf x hx y hy) e he0 he
  have hgrad := metricGradient_frozen_residual_bound g
    (S+localizedCorrugation χ (corrugationPeriodicWell amp) s J R
      (frozenFrameCovector e 2) (frozenFrameCovector e 3) y)
    x y q hc0 hG.le hR.le (mul_nonneg hs.le hK.le) (hmetric x hx).2
    ((hgf x hx y hy).trans (mul_le_mul_of_nonneg_left hxy hG.le)) hq hres'
  have hAs : A ≤ s*(A/m) := by
    have h := mul_le_mul_of_nonneg_right hms (div_nonneg hA.le hm.le)
    have hid : m*(A/m) = A := by field_simp
    rwa [hid] at h
  have hmain : A*R+s/(J*R)*C+G*R*(s*K) ≤ s*Q*(R+1/(J*R)) := by
    have hr0 : 0 ≤ 1/(J*R) := by positivity
    have h1 := mul_le_mul_of_nonneg_right hAs hR.le
    have h2 : 0 ≤ s*C*R := by positivity
    have h3 : 0 ≤ s*(A/m+G*K)*(1/(J*R)) := by positivity
    dsimp [Q]
    simp only [div_eq_mul_inv, one_mul] at *
    nlinarith only [h1,h2,h3]
  calc
    _ ≤ (A*R+s/(J*R)*C+G*R*(s*K))/c := hgrad
    _ ≤ (s*Q*(R+1/(J*R)))/c := div_le_div_of_nonneg_right hmain hc0.le
    _ = s*(Q/c)*(R+1/(J*R)) := by ring

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_CorrugationNormalizedGradient
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

lemma corrugationGradientRate_positive {L : ℝ} (hL : 0 < L) (k : ℕ) :
    0 < corrugationGradientRate L k := by
  have hJ := corrugationFrequency_positive k
  have hR := corrugationScale_positive hL k
  unfold corrugationGradientRate
  positivity

lemma corrugationGradientRate_tendsto {L : ℝ} (hL : 0 < L) :
    Tendsto (corrugationGradientRate L) atTop (𝓝 0) := by
  change Tendsto (fun k ↦ corrugationScale L k+1/(corrugationFrequency k*corrugationScale L k)) atTop (𝓝 0)
  simpa only [one_div,add_zero,Pi.inv_apply] using (corrugationScale_tendsto L).add
    (corrugation_frequency_scale_tendsto hL).inv_tendsto_atTop

theorem corrugation_normalized_gradient_freezing
    (g : _root_.OAI.Yau.Jets.Coord → _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ) (S χ : _root_.OAI.Yau.Jets.Coord → ℝ)
    {D U : Set _root_.OAI.Yau.Jets.Coord} (hD : IsCompact D) (hconv : Convex ℝ D)
    (hU : IsOpen U) (hDU : D ⊆ U)
    (hg : ContDiffOn ℝ ∞ g U) (hS : ContDiffOn ℝ ∞ S U)
    (hp : ∀ y ∈ U, ∀ v, v ≠ 0 → 0 < g y v v)
    (hn : ∀ y ∈ D, metricGradient g S y ≠ 0)
    (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (hχ0 : ∀ x, 0 ≤ χ x) (hχ1 : ∀ x, χ x ≤ 1)
    {amp L : ℝ} (ha : 0 ≤ amp) (ha1 : amp ≤ 1) (hL : 0 < L) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ k : ℕ in atTop,
      ∀ y ∈ D, ∀ x ∈ D, ‖x-y‖ ≤ corrugationScale L k →
      ∀ e : _root_.OAI.Yau.Jets.Coord ≃L[ℝ] _root_.OAI.Yau.Jets.Coord,
      e (Pi.single 0 1) = (corrugationOldSlope g S y)⁻¹ • metricGradient g S y →
      (∀ i j, g y (e (Pi.single i 1)) (e (Pi.single j 1)) = if i=j then 1 else 0) →
      ‖metricNormalize (g x) (metricGradient g (S+localizedCorrugation χ (corrugationPeriodicWell amp)
        (corrugationOldSlope g S y) (corrugationFrequency k) (corrugationScale L k)
        (frozenFrameCovector e 2) (frozenFrameCovector e 3) y) x) -
        metricNormalize (g y) (corrugationLeadingVector amp (χ ((corrugationScale L k)⁻¹ • (x-y))) e
          (corrugationFastMap (corrugationFrequency k) (frozenFrameCovector e 2) (frozenFrameCovector e 3) (x-y)))‖ ≤
        C*corrugationGradientRate L k := by
  obtain ⟨A,hA,hgrad⟩ := corrugation_gradient_freezing g S χ hD hconv hU hDU hg hS hp hn hχ hc hχ0 hχ1 ha ha1
  obtain ⟨c,hc0,M,hM,hmetric⟩ := compact_metric_comparison g hD (hg.continuousOn.mono hDU)
    (fun y hy ↦ hp y (hDU hy))
  obtain ⟨G,hG,hfreeze⟩ := smooth_compact_freezing g hD hconv hU hDU hg
  let K : ℝ := 5*(1+c⁻¹)
  have hK : 0 ≤ K := by dsimp [K] <;> positivity
  obtain ⟨ε₀,B,hε₀,hB,hstab⟩ := metric_normalization_uniform_stability hM.le hK
  let Q : ℝ := A+G+1
  have hQ : 0 < Q := by dsimp [Q] <;> positivity
  refine ⟨B*Q,mul_pos hB hQ,?_⟩
  have ht : Tendsto (fun k ↦ Q*corrugationGradientRate L k) atTop (𝓝 0) :=
    by simpa using (corrugationGradientRate_tendsto hL).const_mul Q
  filter_upwards [ht.eventually_lt_const hε₀] with k hk
  intro y hy x hx hxy e he0 he
  let s := corrugationOldSlope g S y
  let p := metricGradient g (S+localizedCorrugation χ (corrugationPeriodicWell amp) s
    (corrugationFrequency k) (corrugationScale L k) (frozenFrameCovector e 2) (frozenFrameCovector e 3) y) x
  let w := corrugationLeadingVector amp (χ ((corrugationScale L k)⁻¹ • (x-y))) e
    (corrugationFastMap (corrugationFrequency k) (frozenFrameCovector e 2) (frozenFrameCovector e 3) (x-y))
  have hs := corrugationOldSlope_positive g S y (hp y (hDU hy)) (hn y hy)
  have hρ := (corrugationGradientRate_positive hL k).le
  have hJ := corrugationFrequency_positive k
  have hR := corrugationScale_positive hL k
  have hr : corrugationScale L k ≤ corrugationGradientRate L k := by
    dsimp [corrugationGradientRate]
    have hh : 0 ≤ 1/(corrugationFrequency k*corrugationScale L k) := by positivity
    linarith
  have hraw : ‖p-s • w‖ ≤ s*(A*corrugationGradientRate L k) := by
    simpa only [p,w,s,corrugationGradientRate,mul_assoc] using hgrad _ _ hJ hR y hy x hx hxy e he0 he
  have hd : ‖s⁻¹ • p-w‖ ≤ Q*corrugationGradientRate L k := by
    apply (inverse_scaled_vector_error p w hs hraw).trans
    exact mul_le_mul_of_nonneg_right (by dsimp [Q] <;> linarith) hρ
  have hm : ‖g x-g y‖ ≤ Q*corrugationGradientRate L k := by
    calc
      _ ≤ G*‖x-y‖ := hfreeze x hx y hy
      _ ≤ G*corrugationGradientRate L k := mul_le_mul_of_nonneg_left (hxy.trans hr) hG.le
      _ ≤ Q*corrugationGradientRate L k := mul_le_mul_of_nonneg_right (by dsimp [Q] <;> linarith) hρ
  have hw : ‖w‖ ≤ K := corrugationLeadingVector_bound (g y) hc0 (hmetric y hy).2 ha ha1
    (hχ0 _) (hχ1 _) e he _
  have hlen : 1 ≤ g y w w := corrugationLeadingVector_length_ge_one (g y) e he amp _ _
  have hh := (hstab (g x) (g y) (s⁻¹ • p) w (Q*corrugationGradientRate L k)
    (hmetric x hx).1 hw hlen hd hm hk.le).2.2
  rw [metricNormalize_positive_smul (g x) p (inv_pos.mpr hs)] at hh
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  ring

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_CorrugationGradientRates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Filter
open scoped Topology
noncomputable section

lemma corrugationGradientRate_factor {L : ℝ} (hL : L ≠ 0) (k : ℕ) :
    corrugationGradientRate L k = corrugationScale L k*
      (1+(L^2)⁻¹/((k:ℝ)+1)^4) := by
  rw [corrugationGradientRate,corrugationScale_formula,corrugationFrequency]
  have hk : (k:ℝ)+1 ≠ 0 := by positivity
  field_simp

lemma corrugationGradientRate_le_scale {L : ℝ} (hL : 0 < L) :
    ∀ᶠ k : ℕ in atTop, corrugationGradientRate L k ≤ 2*corrugationScale L k := by
  have ht := corrugation_power_reciprocal_tendsto ((L^2)⁻¹) (by norm_num : (4:ℕ) ≠ 0)
  filter_upwards [ht.eventually_lt_const zero_lt_one] with k hk
  rw [corrugationGradientRate_factor hL.ne' k]
  have hR := corrugationScale_positive hL k
  nlinarith

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Spectral_CorrugationAngularProjection
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

theorem corrugation_actual_angular_estimates_oai
    (g : _root_.OAI.Yau.Jets.Coord → _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ) (S χ : _root_.OAI.Yau.Jets.Coord → ℝ)
    {D U : Set _root_.OAI.Yau.Jets.Coord} (hD : IsCompact D) (hconv : Convex ℝ D)
    (hU : IsOpen U) (hDU : D ⊆ U)
    (hg : ContDiffOn ℝ ∞ g U) (hS : ContDiffOn ℝ ∞ S U)
    (hp : ∀ y ∈ U, ∀ v, v ≠ 0 → 0 < g y v v)
    (hn : ∀ y ∈ D, metricGradient g S y ≠ 0)
    (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (hχ0 : ∀ x, 0 ≤ χ x) (hχ1 : ∀ x, χ x ≤ 1)
    {amp L : ℝ} (ha : 0 ≤ amp) (ha1 : amp ≤ 1) (hL : 0 < L) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ k : ℕ in atTop,
      ∀ y ∈ D, ∀ x ∈ D, ‖x-y‖ ≤ corrugationScale L k →
      ∀ e : _root_.OAI.Yau.Jets.Coord ≃L[ℝ] _root_.OAI.Yau.Jets.Coord,
      e (Pi.single 0 1) = (corrugationOldSlope g S y)⁻¹ • metricGradient g S y →
      (∀ i j, g y (e (Pi.single i 1)) (e (Pi.single j 1)) = if i=j then 1 else 0) →
      let z := corrugationFastMap (corrugationFrequency k) (frozenFrameCovector e 2) (frozenFrameCovector e 3) (x-y)
      let r := frozenPlaneVector e ((corrugationCellPoint z).1/corrugationCellRadius z)
        ((corrugationCellPoint z).2/corrugationCellRadius z)
      let t := frozenPlaneVector e (-((corrugationCellPoint z).2/corrugationCellRadius z))
        ((corrugationCellPoint z).1/corrugationCellRadius z)
      let p := metricGradient g (S+localizedCorrugation χ (corrugationPeriodicWell amp)
        (corrugationOldSlope g S y) (corrugationFrequency k) (corrugationScale L k)
        (frozenFrameCovector e 2) (frozenFrameCovector e 3) y) x
      let e' := metricNormalize (g x) p
      let q := metricPerpProjection (g x) e' t
      let t' := metricNormalize (g x) q
      corrugationCellRadius z ≠ 0 →
      q ≠ 0 ∧ g x t' t' = 1 ∧ g x e' t' = 0 ∧
        1/2 ≤ g y t t' ∧ |g y r t'| ≤ C*corrugationScale L k ∧
        |g y r e'| ≤ χ ((corrugationScale L k)⁻¹ • (x-y))*
          corrugationSlope amp (1/4) (corrugationCellRadius z)+C*corrugationScale L k := by
  obtain ⟨A,hA,hdir⟩ := corrugation_normalized_gradient_freezing g S χ hD hconv hU hDU
    hg hS hp hn hχ hc hχ0 hχ1 ha ha1 hL
  obtain ⟨B,hB,hproj⟩ := corrugation_projected_direction_freezing g S χ hD hconv hU hDU
    hg hS hp hn hχ hc hχ0 hχ1 ha ha1 hL
  obtain ⟨c,hc0,M,hM,hmetric⟩ := compact_metric_comparison g hD (hg.continuousOn.mono hDU)
    (fun y hy ↦ hp y (hDU hy))
  let K : ℝ := 1+c⁻¹
  have hK : 0 < K := by dsimp [K] <;> positivity
  let C : ℝ := 2*M*K*(A+B+1)
  have hC : 0 < C := by dsimp [C] <;> positivity
  refine ⟨C,hC,?_⟩
  have ht : Tendsto (fun k ↦ M*K*(B*corrugationGradientRate L k)) atTop (𝓝 0) := by
    simpa using ((corrugationGradientRate_tendsto hL).const_mul B).const_mul (M*K)
  filter_upwards [hdir,hproj,corrugationGradientRate_le_scale hL,
    ht.eventually_lt_const (by norm_num : (0:ℝ) < 1/2)] with k hkdir hkproj hrate hsmall
  intro y hy x hx hxy e he0 he
  dsimp only
  let z := corrugationFastMap (corrugationFrequency k) (frozenFrameCovector e 2) (frozenFrameCovector e 3) (x-y)
  let r := frozenPlaneVector e ((corrugationCellPoint z).1/corrugationCellRadius z)
    ((corrugationCellPoint z).2/corrugationCellRadius z)
  let t := frozenPlaneVector e (-((corrugationCellPoint z).2/corrugationCellRadius z))
    ((corrugationCellPoint z).1/corrugationCellRadius z)
  let p := metricGradient g (S+localizedCorrugation χ (corrugationPeriodicWell amp)
    (corrugationOldSlope g S y) (corrugationFrequency k) (corrugationScale L k)
    (frozenFrameCovector e 2) (frozenFrameCovector e 3) y) x
  let e' := metricNormalize (g x) p
  let q := metricPerpProjection (g x) e' t
  let t' := metricNormalize (g x) q
  let w := corrugationLeadingVector amp (χ ((corrugationScale L k)⁻¹ • (x-y))) e z
  intro hr
  have hrot := frozenPlaneVector_rotating_frame (g y) e he (corrugation_cell_unit_coefficients z hr)
  have hrr : g y r r = 1 := hrot.1
  have htt : g y t t = 1 := hrot.2.1
  have hrt : g y r t = 0 := hrot.2.2.1
  have hrB : ‖r‖ ≤ K := metric_unit_coordinate_bound (g y) hc0 (hmetric y hy).2 r hrr
  have htB : ‖t‖ ≤ K := metric_unit_coordinate_bound (g y) hc0 (hmetric y hy).2 t htt
  have hwt : g y w t = 0 := corrugationLeadingVector_angular_orthogonal (g y) e he amp _ z hr
  obtain ⟨hnq,hu,ho,hb⟩ := hkproj y hy x hx hxy e he0 he t htt hwt
  have hb' : ‖t'-t‖ ≤ B*corrugationGradientRate L k := hb
  have hrad := radial_angular_transfer (g y) r t t' hM.le hK.le (hmetric y hy).1 hrB htB hrt htt hb' hsmall.le
  have hd : ‖e'-metricNormalize (g y) w‖ ≤ A*corrugationGradientRate L k := hkdir y hy x hx hxy e he0 he
  have hpair := frozen_pairing_error (g y) r e' (metricNormalize (g y) w) hM.le hK.le
    (hmetric y hy).1 hrB hd
  have hlead : |g y r (metricNormalize (g y) w)| ≤
      χ ((corrugationScale L k)⁻¹ • (x-y))*corrugationSlope amp (1/4) (corrugationCellRadius z) :=
    corrugation_normalized_leading_radial_bound (g y) e he ha (hχ0 _) z hr
  have hR := (corrugationScale_positive hL k).le
  have hAc : M*K*(A*corrugationGradientRate L k) ≤ C*corrugationScale L k := by
    calc
      _ ≤ M*K*(A*(2*corrugationScale L k)) := by gcongr
      _ ≤ C*corrugationScale L k := by dsimp [C] <;> nlinarith [mul_nonneg (mul_nonneg (mul_nonneg hM.le hK.le) hR) (by linarith : 0 ≤ B+1)]
  have hBc : M*K*(B*corrugationGradientRate L k) ≤ C*corrugationScale L k := by
    calc
      _ ≤ M*K*(B*(2*corrugationScale L k)) := by gcongr
      _ ≤ C*corrugationScale L k := by dsimp [C] <;> nlinarith [mul_nonneg (mul_nonneg (mul_nonneg hM.le hK.le) hR) (by linarith : 0 ≤ A+1)]
  refine ⟨hnq,hu,ho,hrad.2,hrad.1.trans hBc,?_⟩
  calc
    _ ≤ |g y r e'-g y r (metricNormalize (g y) w)|+|g y r (metricNormalize (g y) w)| := by
      convert abs_add_le (g y r e'-g y r (metricNormalize (g y) w)) (g y r (metricNormalize (g y) w)) using 1
      all_goals try with_reducible_and_instances rfl
      congr 1
      ring
    _ ≤ M*K*(A*corrugationGradientRate L k)+
        χ ((corrugationScale L k)⁻¹ • (x-y))*corrugationSlope amp (1/4) (corrugationCellRadius z) := add_le_add hpair hlead
    _ ≤ _ := by linarith

end
end Yau.Geometry

end OAI
end

theorem solution : type_of% @OAI.Yau.Geometry.corrugation_actual_angular_estimates_oai := @OAI.Yau.Geometry.corrugation_actual_angular_estimates_oai
