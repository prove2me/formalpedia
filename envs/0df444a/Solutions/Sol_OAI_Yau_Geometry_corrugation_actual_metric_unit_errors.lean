-- Prove2me | solution 1 for OAI.Yau.Geometry.corrugation_actual_metric_unit_errors
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T00:25:05.893204+00:00
-- url     : https://prove2.me/submissions/df891057-aca7-44c2-b4a5-a45d7698c7b7

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

lemma frozenFrameCovector_norm_bound (g : _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ)
    {c M : ℝ} (hc : 0 < c) (hM : 0 ≤ M)
    (hlower : ∀ v : _root_.OAI.Yau.Jets.Coord, c*‖v‖^2 ≤ g v v) (hupper : ‖g‖ ≤ M)
    (e : _root_.OAI.Yau.Jets.Coord ≃L[ℝ] _root_.OAI.Yau.Jets.Coord)
    (he : ∀ i j, g (e (Pi.single i 1)) (e (Pi.single j 1)) = if i=j then 1 else 0)
    (i : Fin 4) : ‖frozenFrameCovector e i‖ ≤ M*(1+c⁻¹) := by
  have heq : frozenFrameCovector e i = g (e (Pi.single i 1)) := by
    ext v
    exact frozenFrameCovector_metric g e he i v
  rw [heq]
  have hu : g (e (Pi.single i 1)) (e (Pi.single i 1)) = 1 := by simpa using he i i
  calc
    _ ≤ ‖g‖*‖e (Pi.single i 1)‖ := g.le_opNorm _
    _ ≤ M*(1+c⁻¹) := mul_le_mul hupper
      (metric_unit_coordinate_bound g hc hlower _ hu) (norm_nonneg _) hM

lemma frozenFrame_pair_norm_bound (g : _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ)
    {c M : ℝ} (hc : 0 < c) (hM : 0 ≤ M)
    (hlower : ∀ v : _root_.OAI.Yau.Jets.Coord, c*‖v‖^2 ≤ g v v) (hupper : ‖g‖ ≤ M)
    (e : _root_.OAI.Yau.Jets.Coord ≃L[ℝ] _root_.OAI.Yau.Jets.Coord)
    (he : ∀ i j, g (e (Pi.single i 1)) (e (Pi.single j 1)) = if i=j then 1 else 0) :
    ‖(frozenFrameCovector e 2).prod (frozenFrameCovector e 3)‖ ≤ M*(1+c⁻¹) := by
  have h2 := frozenFrameCovector_norm_bound g hc hM hlower hupper e he 2
  have h3 := frozenFrameCovector_norm_bound g hc hM hlower hupper e he 3
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro v
  change ‖(frozenFrameCovector e 2 v,frozenFrameCovector e 3 v)‖ ≤ _
  rw [Prod.norm_def]
  apply max_le
  · exact ((frozenFrameCovector e 2).le_opNorm v).trans (mul_le_mul_of_nonneg_right h2 (norm_nonneg v))
  · exact ((frozenFrameCovector e 3).le_opNorm v).trans (mul_le_mul_of_nonneg_right h3 (norm_nonneg v))

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

lemma corrugationPeriodicWell_global_derivative_bound {a : ℝ} (ha : 0 ≤ a) (z : ℝ × ℝ) :
    ‖fderiv ℝ (corrugationPeriodicWell a) z‖ ≤
      2*corrugationSlope a (1/4) (corrugationCellRadius z) := by
  have h := corrugationPeriodicWell_closed_derivative_bound ha (corrugationCellIndex z)
    (corrugationCellPoint z) (corrugationCellPoint_bounds z).1 (corrugationCellPoint_bounds z).2
    (corrugationCellRadius_properties z).1 (corrugationCellRadius_properties z).2
  rwa [corrugationCellPoint_reconstruct] at h

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_CorrugationErrorBound
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Yau.Jets
noncomputable section

lemma corrugationMetricError_bound
    (g : _root_.OAI.Yau.Jets.Coord → _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ)
    (χ : _root_.OAI.Yau.Jets.Coord → ℝ) (f : (ℝ × ℝ) → ℝ)
    {s J R C₀ C₁ C₂ L G : ℝ}
    (hs : 0 ≤ s) (hJ : 0 < J) (hR : 0 < R)
    (hC₀ : 0 ≤ C₀) (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂) (hL : 0 ≤ L) (hG : 0 ≤ G)
    (a b : _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ) (y x u v : _root_.OAI.Yau.Jets.Coord)
    (hc : 0 ≤ χ (R⁻¹ • (x-y)))
    (hf : |f (corrugationFastMap J a b (x-y))| ≤ C₀)
    (hχu : |fderiv ℝ χ (R⁻¹ • (x-y)) u| ≤ C₁)
    (hχv : |fderiv ℝ χ (R⁻¹ • (x-y)) v| ≤ C₁)
    (hχuv : |fderiv ℝ (fderiv ℝ χ) (R⁻¹ • (x-y)) u v| ≤ C₂)
    (hfu : |fderiv ℝ f (corrugationFastMap J a b (x-y)) (a.prod b u)| ≤ L)
    (hfv : |fderiv ℝ f (corrugationFastMap J a b (x-y)) (a.prod b v)| ≤ L)
    (hfΓ : |fderiv ℝ f (corrugationFastMap J a b (x-y))
      (a.prod b (metricConnection (g x) (fderiv ℝ g x) u v))| ≤ L*G)
    (hχΓ : |fderiv ℝ χ (R⁻¹ • (x-y))
      (metricConnection (g x) (fderiv ℝ g x) u v)| ≤ C₁*G) :
    |corrugationMetricError g χ f s J R a b y x u v| ≤
      s*(2*C₁*L/R + C₀*C₂/(J*R^2) + χ (R⁻¹ • (x-y))*L*G + C₀*C₁*G/(J*R)) := by
  let X := R⁻¹ • (x-y)
  let Z := corrugationFastMap J a b (x-y)
  let Γ := metricConnection (g x) (fderiv ℝ g x) u v
  have hcross : |fderiv ℝ χ X v*fderiv ℝ f Z (a.prod b u) +
      fderiv ℝ χ X u*fderiv ℝ f Z (a.prod b v)| ≤ 2*C₁*L := by
    calc
      _ ≤ |fderiv ℝ χ X v*fderiv ℝ f Z (a.prod b u)| +
          |fderiv ℝ χ X u*fderiv ℝ f Z (a.prod b v)| := abs_add_le _ _
      _ ≤ C₁*L+C₁*L := by
        simp only [abs_mul]
        exact add_le_add (mul_le_mul hχv hfu (abs_nonneg _) hC₁)
          (mul_le_mul hχu hfv (abs_nonneg _) hC₁)
      _ = _ := by ring
  have h1 : |s/R*(fderiv ℝ χ X v*fderiv ℝ f Z (a.prod b u) +
      fderiv ℝ χ X u*fderiv ℝ f Z (a.prod b v))| ≤ (s/R)*(2*C₁*L) := by
    rw [abs_mul,abs_of_nonneg (div_nonneg hs hR.le)]
    exact mul_le_mul_of_nonneg_left hcross (div_nonneg hs hR.le)
  have h2 : |s/(J*R^2)*f Z*fderiv ℝ (fderiv ℝ χ) X u v| ≤ s/(J*R^2)*C₀*C₂ := by
    simp only [abs_mul,abs_of_nonneg (div_nonneg hs (mul_nonneg hJ.le (sq_nonneg R))) ]
    exact mul_le_mul_of_nonneg (mul_le_mul_of_nonneg_left hf (by positivity)) hχuv
      (mul_nonneg (div_nonneg hs (mul_nonneg hJ.le (sq_nonneg R))) (abs_nonneg _)) hC₂
  have h3 : |s*χ X*fderiv ℝ f Z (a.prod b Γ)| ≤ s*χ X*(L*G) := by
    rw [abs_mul,abs_of_nonneg (mul_nonneg hs hc)]
    exact mul_le_mul_of_nonneg (le_refl _) hfΓ (mul_nonneg hs hc) (mul_nonneg hL hG)
  have h4 : |s/(J*R)*f Z*fderiv ℝ χ X Γ| ≤ s/(J*R)*C₀*(C₁*G) := by
    simp only [abs_mul,abs_of_nonneg (div_nonneg hs (mul_nonneg hJ.le hR.le))]
    exact mul_le_mul (mul_le_mul_of_nonneg_left hf (by positivity)) hχΓ (abs_nonneg _) (by positivity)
  have hsub (a b : ℝ) : |a-b| ≤ |a|+|b| := by
    simpa only [sub_eq_add_neg,abs_neg] using abs_add_le a (-b)
  unfold corrugationMetricError
  calc
    _ ≤ (|s/R*(fderiv ℝ χ X v*fderiv ℝ f Z (a.prod b u) +
        fderiv ℝ χ X u*fderiv ℝ f Z (a.prod b v))| +
        |s/(J*R^2)*f Z*fderiv ℝ (fderiv ℝ χ) X u v|) +
        |s*χ X*fderiv ℝ f Z (a.prod b Γ)| + |s/(J*R)*f Z*fderiv ℝ χ X Γ| := by
      exact (hsub _ _).trans (add_le_add
        ((hsub _ _).trans (add_le_add (abs_add_le _ _) le_rfl)) le_rfl)
    _ ≤ s/R*(2*C₁*L)+s/(J*R^2)*C₀*C₂+s*χ X*(L*G)+s/(J*R)*C₀*(C₁*G) :=
      add_le_add (add_le_add (add_le_add h1 h2) h3) h4
    _ = _ := by dsimp [X] <;> ring

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_CorrugationNormBounds
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

lemma clm_apply_bound {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (A : E →L[ℝ] F) {C : ℝ} (hA : ‖A‖ ≤ C) (v : E) : ‖A v‖ ≤ C*‖v‖ :=
  (A.le_opNorm v).trans (mul_le_mul_of_nonneg_right hA (norm_nonneg v))

lemma clm_unit_bound {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (A : E →L[ℝ] F) {C : ℝ} (hA : ‖A‖ ≤ C) (v : E) (hv : ‖v‖ ≤ 1) : ‖A v‖ ≤ C := by
  exact (clm_apply_bound A hA v).trans (by nlinarith [norm_nonneg A])

lemma bilinear_unit_bound {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (A : E →L[ℝ] E →L[ℝ] F) {C : ℝ} (hA : ‖A‖ ≤ C)
    (u v : E) (hu : ‖u‖ ≤ 1) (hv : ‖v‖ ≤ 1) : ‖A u v‖ ≤ C :=
  clm_unit_bound (A u) (clm_unit_bound A hA u hu) v hv

lemma compact_second_derivative_bound (χ : _root_.OAI.Yau.Jets.Coord → ℝ) (hχ : ContDiff ℝ ∞ χ)
    (hc : HasCompactSupport χ) : ∃ C : ℝ, 0 < C ∧ ∀ x, ‖fderiv ℝ (fderiv ℝ χ) x‖ ≤ C := by
  have hsub : tsupport (fderiv ℝ (fderiv ℝ χ)) ⊆ tsupport χ :=
    (tsupport_fderiv_subset ℝ (f := fderiv ℝ χ)).trans (tsupport_fderiv_subset ℝ (f := χ))
  have hcDD : IsCompact (tsupport (fderiv ℝ (fderiv ℝ χ))) :=
    hc.of_isClosed_subset isClosed_closure hsub
  have hcont : Continuous (fun x ↦ ‖fderiv ℝ (fderiv ℝ χ) x‖) :=
    ((hχ.fderiv_right (m := ∞) (by simp)).continuous_fderiv (by simp)).norm
  obtain ⟨B,hB⟩ := (hcDD.image hcont).bddAbove
  refine ⟨max B 0+1,by positivity,fun x ↦ ?_⟩
  by_cases hx : x ∈ tsupport (fderiv ℝ (fderiv ℝ χ))
  · exact (hB ⟨x,hx,rfl⟩).trans (by linarith [le_max_left B 0])
  · have hz : fderiv ℝ (fderiv ℝ χ) x = 0 := by
      by_contra hn
      exact hx (subset_tsupport _ hn)
    rw [hz]
    simp only [ContinuousLinearMap.opNorm_zero]
    positivity

lemma corrugationMetricError_operator_bound
    (g : _root_.OAI.Yau.Jets.Coord → _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ)
    (χ : _root_.OAI.Yau.Jets.Coord → ℝ) (f : (ℝ × ℝ) → ℝ)
    {s J R C₀ C₁ C₂ L K G : ℝ}
    (hs : 0 ≤ s) (hJ : 0 < J) (hR : 0 < R)
    (hC₀ : 0 ≤ C₀) (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂)
    (hL : 0 ≤ L) (hK : 0 ≤ K) (hG : 0 ≤ G)
    (a b : _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ) (y x u v : _root_.OAI.Yau.Jets.Coord) (hu : ‖u‖ ≤ 1) (hv : ‖v‖ ≤ 1)
    (hc : 0 ≤ χ (R⁻¹ • (x-y)))
    (hf : |f (corrugationFastMap J a b (x-y))| ≤ C₀)
    (hχD : ‖fderiv ℝ χ (R⁻¹ • (x-y))‖ ≤ C₁)
    (hχDD : ‖fderiv ℝ (fderiv ℝ χ) (R⁻¹ • (x-y))‖ ≤ C₂)
    (hfD : ‖fderiv ℝ f (corrugationFastMap J a b (x-y))‖ ≤ L)
    (hQ : ‖a.prod b‖ ≤ K)
    (hΓ : ‖metricConnection (g x) (fderiv ℝ g x)‖ ≤ G) :
    |corrugationMetricError g χ f s J R a b y x u v| ≤
      s*(2*C₁*(L*K)/R + C₀*C₂/(J*R^2) +
        χ (R⁻¹ • (x-y))*(L*K)*G + C₀*C₁*G/(J*R)) := by
  have hD (w : _root_.OAI.Yau.Jets.Coord) : |fderiv ℝ f (corrugationFastMap J a b (x-y)) (a.prod b w)| ≤
      (L*K)*‖w‖ := by
    calc
      _ ≤ L*‖a.prod b w‖ := clm_apply_bound _ hfD _
      _ ≤ L*(K*‖w‖) := mul_le_mul_of_nonneg_left (clm_apply_bound _ hQ _) hL
      _ = _ := by ring
  have hconn := bilinear_unit_bound _ hΓ u v hu hv
  apply corrugationMetricError_bound g χ f hs hJ hR hC₀ hC₁ hC₂ (mul_nonneg hL hK) hG a b y x u v hc hf
  · exact clm_unit_bound _ hχD u hu
  · exact clm_unit_bound _ hχD v hv
  · exact bilinear_unit_bound _ hχDD u v hu hv
  · exact (hD u).trans (by nlinarith [mul_nonneg hL hK])
  · exact (hD v).trans (by nlinarith [mul_nonneg hL hK])
  · exact (hD _).trans (mul_le_mul_of_nonneg_left hconn (mul_nonneg hL hK))
  · exact (clm_apply_bound _ hχD _).trans (mul_le_mul_of_nonneg_left hconn hC₁)

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_CorrugationGlobalError
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Yau.Jets Real
open scoped ContDiff
noncomputable section

theorem corrugation_global_source_error_bound (χ : _root_.OAI.Yau.Jets.Coord → ℝ)
    (hχ : ContDiff ℝ ∞ χ) (hcpt : HasCompactSupport χ)
    (hχrange : ∀ z, 0 ≤ χ z ∧ χ z ≤ 1) {D : ℝ} (hD : 0 < D)
    (hχD : ∀ z, ‖fderiv ℝ χ z‖ ≤ D*(χ z)^((7:ℝ)/8))
    {amp K G : ℝ} (hamp : 0 ≤ amp) (hK : 0 ≤ K) (hG : 0 ≤ G) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (g : _root_.OAI.Yau.Jets.Coord → _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ) (s J R : ℝ),
      0 ≤ s → 0 < J → 0 < R →
      ∀ (a b : _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ) (y x u v : _root_.OAI.Yau.Jets.Coord),
      ‖u‖ ≤ 1 → ‖v‖ ≤ 1 → ‖a.prod b‖ ≤ K →
      ‖metricConnection (g x) (fderiv ℝ g x)‖ ≤ G →
      |corrugationMetricError g χ (corrugationPeriodicWell amp) s J R a b y x u v| ≤
        C*s*(R⁻¹*(χ (R⁻¹ • (x-y)))^((7:ℝ)/8)*corrugationSlope amp (1/4) (corrugationCellRadius (corrugationFastMap J a b (x-y))) +
          (J*R^2)⁻¹ + χ (R⁻¹ • (x-y))*corrugationSlope amp (1/4) (corrugationCellRadius (corrugationFastMap J a b (x-y))) + (J*R)⁻¹) := by
  obtain ⟨B,hB,hf⟩ := corrugationPeriodicWell_bounded amp
  obtain ⟨M,hM,hχDD⟩ := compact_second_derivative_bound χ hχ hcpt
  let C := 4*D*K+B*M+2*K*G+B*D*G+1
  have hC : 0 < C := by dsimp [C] <;> positivity
  have h1 : 4*D*K ≤ C := by dsimp [C] <;> nlinarith [mul_nonneg hB.le hM.le,mul_nonneg hK hG,mul_nonneg (mul_nonneg hB.le hD.le) hG]
  have h2 : B*M ≤ C := by dsimp [C] <;> nlinarith [mul_nonneg hD.le hK,mul_nonneg hK hG,mul_nonneg (mul_nonneg hB.le hD.le) hG]
  have h3 : 2*K*G ≤ C := by dsimp [C] <;> nlinarith [mul_nonneg hD.le hK,mul_nonneg hB.le hM.le,mul_nonneg (mul_nonneg hB.le hD.le) hG]
  have h4 : B*D*G ≤ C := by dsimp [C] <;> nlinarith [mul_nonneg hD.le hK,mul_nonneg hB.le hM.le,mul_nonneg hK hG]
  refine ⟨C,hC,?_⟩
  intro g s J R hs hJ hR a b y x u v hu hv hQ hΓ
  let q := (χ (R⁻¹ • (x-y)))^((7:ℝ)/8)
  let l := corrugationSlope amp (1/4) (corrugationCellRadius (corrugationFastMap J a b (x-y)))
  have hq : 0 ≤ q := Real.rpow_nonneg (hχrange _).1 _
  have hq1 : q ≤ 1 := Real.rpow_le_one (hχrange _).1 (hχrange _).2 (by norm_num)
  have hl : 0 ≤ l := corrugationSlope_nonneg hamp (corrugationCellRadius_properties _).1
  have hfD : ‖fderiv ℝ (corrugationPeriodicWell amp) (corrugationFastMap J a b (x-y))‖ ≤ 2*l := by
    exact corrugationPeriodicWell_global_derivative_bound hamp _
  have hb := corrugationMetricError_operator_bound g χ (corrugationPeriodicWell amp)
    hs hJ hR hB.le (mul_nonneg hD.le hq) hM.le (show 0 ≤ 2*l by positivity) hK hG
    a b y x u v hu hv (hχrange _).1 (hf _) (hχD _) (hχDD _) hfD hQ hΓ
  have hn1 : 0 ≤ R⁻¹*q*l := by positivity
  have hn2 : 0 ≤ (J*R^2)⁻¹ := by positivity
  have hn3 : 0 ≤ χ (R⁻¹ • (x-y))*l := mul_nonneg (hχrange _).1 hl
  have hn4 : 0 ≤ (J*R)⁻¹ := by positivity
  have hd4 : B*D*G*q ≤ C :=
    (mul_le_mul_of_nonneg_left hq1 (by positivity)).trans (by simpa using h4)
  calc
    _ ≤ s*(2*(D*q)*(2*l*K)/R+B*M/(J*R^2)+χ (R⁻¹ • (x-y))*(2*l*K)*G+B*(D*q)*G/(J*R)) := hb
    _ = s*((4*D*K)*(R⁻¹*q*l)+(B*M)*(J*R^2)⁻¹+
        (2*K*G)*(χ (R⁻¹ • (x-y))*l)+(B*D*G*q)*(J*R)⁻¹) := by ring
    _ ≤ s*(C*(R⁻¹*q*l)+C*(J*R^2)⁻¹+C*(χ (R⁻¹ • (x-y))*l)+C*(J*R)⁻¹) := by
      exact mul_le_mul_of_nonneg_left (add_le_add (add_le_add
        (add_le_add (mul_le_mul_of_nonneg_right h1 hn1) (mul_le_mul_of_nonneg_right h2 hn2))
        (mul_le_mul_of_nonneg_right h3 hn3)) (mul_le_mul_of_nonneg_right hd4 hn4)) hs
    _ = _ := by dsimp [q,l] <;> ring

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
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_CorrugationRegimeErrors
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Yau.Jets Real
open scoped ContDiff
noncomputable section

theorem corrugation_actual_regime_errors (χ : _root_.OAI.Yau.Jets.Coord → ℝ)
    (hχ : ContDiff ℝ ∞ χ) (hcpt : HasCompactSupport χ)
    (hχrange : ∀ z, 0 ≤ χ z ∧ χ z ≤ 1) {D : ℝ} (hD : 0 < D)
    (hχD : ∀ z, ‖fderiv ℝ χ z‖ ≤ D*(χ z)^((7:ℝ)/8))
    {amp K G : ℝ} (hamp : 0 ≤ amp) (hamp1 : amp ≤ 1) (hK : 0 ≤ K) (hG : 0 ≤ G) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (g : _root_.OAI.Yau.Jets.Coord → _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ) (s L : ℝ),
      0 ≤ s → 0 < L → ∀ k : ℕ,
      ∀ (a b : _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ) (y x u v : _root_.OAI.Yau.Jets.Coord),
      ‖u‖ ≤ 1 → ‖v‖ ≤ 1 → ‖a.prod b‖ ≤ K →
      ‖metricConnection (g x) (fderiv ℝ g x)‖ ≤ G →
      let χ₀ := χ ((corrugationScale L k)⁻¹ • (x-y))
      let l := corrugationSlope amp (1/4)
        (corrugationCellRadius (corrugationFastMap (corrugationFrequency k) a b (x-y)))
      ∀ T : ℝ, 0 < T →
      (corrugationFrequency k*χ₀*l ≤ T →
        |corrugationMetricError g χ (corrugationPeriodicWell amp) s (corrugationFrequency k)
          (corrugationScale L k) a b y x u v| ≤ C*s*corrugationLowErrorRate L T k) ∧
      (T < corrugationFrequency k*χ₀*l →
        |corrugationMetricError g χ (corrugationPeriodicWell amp) s (corrugationFrequency k)
          (corrugationScale L k) a b y x u v| ≤
            C*s*corrugationHighErrorRate L T k*(corrugationFrequency k*χ₀*l)) := by
  obtain ⟨C,hC,hbound⟩ := corrugation_global_source_error_bound χ hχ hcpt hχrange hD hχD hamp hK hG
  refine ⟨C,hC,?_⟩
  intro g s L hs hL k a b y x u v hu hv hQ hΓ χ₀ l T hT
  have hχ0 : 0 ≤ χ₀ := (hχrange _).1
  have hχ1 : χ₀ ≤ 1 := (hχrange _).2
  have hl : 0 ≤ l := corrugationSlope_nonneg hamp (corrugationCellRadius_properties _).1
  have hl1 : l ≤ 1 := corrugationSlope_le_one hamp hamp1 (by norm_num) (by norm_num)
    (corrugationCellRadius_properties _).1
  have hb := hbound g s (corrugationFrequency k) (corrugationScale L k) hs
    (corrugationFrequency_positive k) (corrugationScale_positive hL k) a b y x u v hu hv hQ hΓ
  constructor
  · intro hreg
    exact hb.trans (mul_le_mul_of_nonneg_left
      (corrugationLowErrorRate_bounds hL T k hχ0 hχ1 hl hl1 hreg).1 (mul_nonneg hC.le hs))
  · intro hreg
    have h := hb.trans (mul_le_mul_of_nonneg_left
      (corrugationHighErrorRate_bounds hL hT k hχ0 hχ1 hl hl1 hreg).1 (mul_nonneg hC.le hs))
    exact h.trans_eq (by ring)

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Charts_CorrugationMetricErrorRescale
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

lemma corrugationMetricError_smul_both
    (g : _root_.OAI.Yau.Jets.Coord → _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ) (χ : _root_.OAI.Yau.Jets.Coord → ℝ) (f : (ℝ × ℝ) → ℝ)
    (s J R : ℝ) (a b : _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ) (y x u v : _root_.OAI.Yau.Jets.Coord) (r : ℝ) :
    corrugationMetricError g χ f s J R a b y x (r • u) (r • v) =
      r^2*corrugationMetricError g χ f s J R a b y x u v := by
  simp only [corrugationMetricError,map_smul,smul_apply,smul_eq_mul]
  ring

lemma corrugationMetricError_bound_rescale
    (g : _root_.OAI.Yau.Jets.Coord → _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ) (χ : _root_.OAI.Yau.Jets.Coord → ℝ) (f : (ℝ × ℝ) → ℝ)
    (s J R : ℝ) (a b : _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ) (y x : _root_.OAI.Yau.Jets.Coord)
    {K B : ℝ} (hK : 0 < K)
    (hb : ∀ u v : _root_.OAI.Yau.Jets.Coord, ‖u‖ ≤ 1 → ‖v‖ ≤ 1 →
      |corrugationMetricError g χ f s J R a b y x u v| ≤ B)
    (u v : _root_.OAI.Yau.Jets.Coord) (hu : ‖u‖ ≤ K) (hv : ‖v‖ ≤ K) :
    |corrugationMetricError g χ f s J R a b y x u v| ≤ K^2*B := by
  have hnorm (w : _root_.OAI.Yau.Jets.Coord) (hw : ‖w‖ ≤ K) : ‖K⁻¹ • w‖ ≤ 1 := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hK)]
    exact (mul_le_mul_of_nonneg_left hw (inv_nonneg.mpr hK.le)).trans_eq (inv_mul_cancel₀ hK.ne')
  have h := hb (K⁻¹ • u) (K⁻¹ • v) (hnorm u hu) (hnorm v hv)
  have hid : corrugationMetricError g χ f s J R a b y x u v =
      K^2*corrugationMetricError g χ f s J R a b y x (K⁻¹ • u) (K⁻¹ • v) := by
    rw [corrugationMetricError_smul_both]
    field_simp
  rw [hid,abs_mul,abs_of_nonneg (sq_nonneg K)]
  exact mul_le_mul_of_nonneg_left h (sq_nonneg K)

theorem corrugation_actual_bounded_regime_errors (χ : _root_.OAI.Yau.Jets.Coord → ℝ)
    (hχ : ContDiff ℝ ∞ χ) (hcpt : HasCompactSupport χ)
    (hχrange : ∀ z, 0 ≤ χ z ∧ χ z ≤ 1) {D : ℝ} (hD : 0 < D)
    (hχD : ∀ z, ‖fderiv ℝ χ z‖ ≤ D*(χ z)^((7:ℝ)/8))
    {amp K G V : ℝ} (hamp : 0 ≤ amp) (hamp1 : amp ≤ 1)
    (hK : 0 ≤ K) (hG : 0 ≤ G) (hV : 0 < V) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (g : _root_.OAI.Yau.Jets.Coord → _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ) (s L : ℝ),
      0 ≤ s → 0 < L → ∀ k : ℕ,
      ∀ (a b : _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ) (y x u v : _root_.OAI.Yau.Jets.Coord),
      ‖u‖ ≤ V → ‖v‖ ≤ V → ‖a.prod b‖ ≤ K →
      ‖metricConnection (g x) (fderiv ℝ g x)‖ ≤ G →
      let χ₀ := χ ((corrugationScale L k)⁻¹ • (x-y))
      let l := corrugationSlope amp (1/4)
        (corrugationCellRadius (corrugationFastMap (corrugationFrequency k) a b (x-y)))
      ∀ T : ℝ, 0 < T →
      (corrugationFrequency k*χ₀*l ≤ T →
        |corrugationMetricError g χ (corrugationPeriodicWell amp) s (corrugationFrequency k)
          (corrugationScale L k) a b y x u v| ≤ C*s*corrugationLowErrorRate L T k) ∧
      (T < corrugationFrequency k*χ₀*l →
        |corrugationMetricError g χ (corrugationPeriodicWell amp) s (corrugationFrequency k)
          (corrugationScale L k) a b y x u v| ≤
            C*s*corrugationHighErrorRate L T k*(corrugationFrequency k*χ₀*l)) := by
  obtain ⟨C,hC,hbound⟩ := corrugation_actual_regime_errors χ hχ hcpt hχrange hD hχD hamp hamp1 hK hG
  refine ⟨V^2*C,mul_pos (sq_pos_of_pos hV) hC,?_⟩
  intro g s L hs hL k a b y x u v hu hv hab hΓ χ₀ l T hT
  constructor
  · intro hreg
    have hb := corrugationMetricError_bound_rescale g χ (corrugationPeriodicWell amp) s
      (corrugationFrequency k) (corrugationScale L k) a b y x hV
      (fun u v hu hv ↦ (hbound g s L hs hL k a b y x u v hu hv hab hΓ T hT).1 hreg) u v hu hv
    exact hb.trans_eq (by ring)
  · intro hreg
    have hb := corrugationMetricError_bound_rescale g χ (corrugationPeriodicWell amp) s
      (corrugationFrequency k) (corrugationScale L k) a b y x hV
      (fun u v hu hv ↦ (hbound g s L hs hL k a b y x u v hu hv hab hΓ T hT).2 hreg) u v hu hv
    exact hb.trans_eq (by ring)

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

lemma compact_metric_comparison (g : _root_.OAI.Yau.Jets.Coord → _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ)
    {D : Set _root_.OAI.Yau.Jets.Coord} (hD : IsCompact D) (hg : ContinuousOn g D)
    (hp : ∀ y ∈ D, ∀ v, v ≠ 0 → 0 < g y v v) :
    ∃ c : ℝ, 0 < c ∧ ∃ M : ℝ, 0 < M ∧
      ∀ y ∈ D, ‖g y‖ ≤ M ∧ ∀ v, c*‖v‖^2 ≤ g y v v := by
  let : CompactSpace D := isCompact_iff_compactSpace.mp hD
  obtain ⟨c,hc,M,hM,hb⟩ := uniform_metric_coercivity (fun y : D ↦ g y)
    hg.domRestrict (fun y v hv ↦ hp y y.property v hv)
  exact ⟨c,hc,M,hM,fun y hy ↦ hb ⟨y,hy⟩⟩

lemma compact_connection_bound (g : _root_.OAI.Yau.Jets.Coord → _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ)
    {D U : Set _root_.OAI.Yau.Jets.Coord} (hD : IsCompact D) (hU : IsOpen U) (hDU : D ⊆ U)
    (hg : ContDiffOn ℝ ∞ g U)
    (hp : ∀ y ∈ U, ∀ v, v ≠ 0 → 0 < g y v v) :
    ∃ G : ℝ, 0 < G ∧ ∀ y ∈ D, ‖metricConnection (g y) (fderiv ℝ g y)‖ ≤ G := by
  have hc : ContinuousOn (fun y ↦ metricConnection (g y) (fderiv ℝ g y)) D := by
    intro y hy
    have hg' := hg.contDiffAt (hU.mem_nhds (hDU hy))
    exact (metric_connection_continuousAt g (fderiv ℝ g) y hg'.continuousAt
      (hg'.continuousAt_fderiv (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)) (hp y (hDU hy))).continuousWithinAt
  obtain ⟨G,hG,hb⟩ := (hD.image_of_continuousOn hc).isBounded.exists_pos_norm_le
  exact ⟨G,hG,fun y hy ↦ hb _ ⟨y,hy,rfl⟩⟩

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_CorrugationUnitRegimeErrors
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

theorem corrugation_actual_metric_unit_errors_oai
    (g : _root_.OAI.Yau.Jets.Coord → _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ) (χ : _root_.OAI.Yau.Jets.Coord → ℝ)
    {D U : Set _root_.OAI.Yau.Jets.Coord} (hD : IsCompact D) (hU : IsOpen U) (hDU : D ⊆ U)
    (hg : ContDiffOn ℝ ∞ g U) (hp : ∀ y ∈ U, ∀ v, v ≠ 0 → 0 < g y v v)
    (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (hχrange : ∀ z, 0 ≤ χ z ∧ χ z ≤ 1) {A : ℝ} (hA : 0 < A)
    (hχA : ∀ z, ‖fderiv ℝ χ z‖ ≤ A*(χ z)^((7:ℝ)/8))
    {amp : ℝ} (ha : 0 ≤ amp) (ha1 : amp ≤ 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (s L : ℝ), 0 ≤ s → 0 < L → ∀ k : ℕ,
      ∀ y ∈ D, ∀ x ∈ D, ∀ e : _root_.OAI.Yau.Jets.Coord ≃L[ℝ] _root_.OAI.Yau.Jets.Coord,
      (∀ i j, g y (e (Pi.single i 1)) (e (Pi.single j 1)) = if i=j then 1 else 0) →
      ∀ u v : _root_.OAI.Yau.Jets.Coord, g x u u = 1 → g x v v = 1 →
      let a := frozenFrameCovector e 2
      let b := frozenFrameCovector e 3
      let χ₀ := χ ((corrugationScale L k)⁻¹ • (x-y))
      let l := corrugationSlope amp (1/4)
        (corrugationCellRadius (corrugationFastMap (corrugationFrequency k) a b (x-y)))
      ∀ T : ℝ, 0 < T →
      (corrugationFrequency k*χ₀*l ≤ T →
        |corrugationMetricError g χ (corrugationPeriodicWell amp) s (corrugationFrequency k)
          (corrugationScale L k) a b y x u v| ≤ C*s*corrugationLowErrorRate L T k) ∧
      (T < corrugationFrequency k*χ₀*l →
        |corrugationMetricError g χ (corrugationPeriodicWell amp) s (corrugationFrequency k)
          (corrugationScale L k) a b y x u v| ≤
            C*s*corrugationHighErrorRate L T k*(corrugationFrequency k*χ₀*l)) := by
  obtain ⟨c,hc0,M,hM,hmetric⟩ := compact_metric_comparison g hD (hg.continuousOn.mono hDU)
    (fun y hy ↦ hp y (hDU hy))
  obtain ⟨G,hG,hΓ⟩ := compact_connection_bound g hD hU hDU hg hp
  obtain ⟨C,hC,hbound⟩ := corrugation_actual_bounded_regime_errors χ hχ hc hχrange hA hχA
    ha ha1 (show 0 ≤ M*(1+c⁻¹) by positivity) hG.le (show 0 < 1+c⁻¹ by positivity)
  refine ⟨C,hC,?_⟩
  intro s L hs hL k y hy x hx e he u v hu hv
  exact hbound g s L hs hL k _ _ y x u v
    (metric_unit_coordinate_bound (g x) hc0 (hmetric x hx).2 u hu)
    (metric_unit_coordinate_bound (g x) hc0 (hmetric x hx).2 v hv)
    (frozenFrame_pair_norm_bound (g y) hc0 hM.le (hmetric y hy).2 (hmetric y hy).1 e he)
    (hΓ x hx)

end
end Yau.Geometry

end OAI
end

theorem solution : type_of% @OAI.Yau.Geometry.corrugation_actual_metric_unit_errors_oai := @OAI.Yau.Geometry.corrugation_actual_metric_unit_errors_oai
