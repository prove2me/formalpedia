-- Prove2me | solution 1 for OAI.Yau.Geometry.corrugation_grid_integrated_gain
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T00:25:07.177048+00:00
-- url     : https://prove2.me/submissions/2304f73e-0a9a-46dd-a339-15a067f25f16

import Mathlib
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Algebra.Order.Floor.Ring
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
import Mathlib.Topology.Order.Compact
import Definitions.Def_OAIQ237Ny002
import Theorems.Thm_OAI_Yau_Geometry_corrugation_speed_freezing

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

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Charts_CorrugationFrameOperatorBounds
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Yau.Jets
noncomputable section

lemma frozenFrame_operator_bound (g : _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ)
    {c : ℝ} (hc : 0 < c) (hg : ∀ v : _root_.OAI.Yau.Jets.Coord, c*‖v‖^2 ≤ g v v)
    (e : _root_.OAI.Yau.Jets.Coord ≃L[ℝ] _root_.OAI.Yau.Jets.Coord)
    (he : ∀ i j, g (e (Pi.single i 1)) (e (Pi.single j 1)) = if i=j then 1 else 0)
    (v : _root_.OAI.Yau.Jets.Coord) : ‖e v‖ ≤ (4*(1+c⁻¹))*‖v‖ := by
  have hv : v = ∑ i : Fin 4, v i • Pi.single i (1:ℝ) := by
    ext j
    simp [Pi.single_apply,Finset.sum_apply]
  have hu : ∀ i : Fin 4, ‖e (Pi.single i 1)‖ ≤ 1+c⁻¹ :=
    fun i ↦ metric_unit_coordinate_bound g hc hg _ (by simpa using he i i)
  calc
    ‖e v‖ = ‖∑ i : Fin 4, v i • e (Pi.single i 1)‖ := by conv_lhs => rw [hv,map_sum]; simp only [map_smul]
    _ ≤ ∑ i : Fin 4, ‖v i • e (Pi.single i 1)‖ := norm_sum_le _ _
    _ ≤ ∑ _i : Fin 4, ‖v‖*(1+c⁻¹) := by
      apply Finset.sum_le_sum
      intro i _
      rw [norm_smul]
      exact mul_le_mul (norm_le_pi_norm v i) (hu i) (norm_nonneg _) (norm_nonneg _)
    _ = _ := by simp <;> ring

lemma frozenFrame_inverse_operator_bound (g : _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ)
    {c M : ℝ} (hc : 0 < c) (hM : 0 ≤ M)
    (hg : ∀ v : _root_.OAI.Yau.Jets.Coord, c*‖v‖^2 ≤ g v v) (hupper : ‖g‖ ≤ M)
    (e : _root_.OAI.Yau.Jets.Coord ≃L[ℝ] _root_.OAI.Yau.Jets.Coord)
    (he : ∀ i j, g (e (Pi.single i 1)) (e (Pi.single j 1)) = if i=j then 1 else 0)
    (v : _root_.OAI.Yau.Jets.Coord) : ‖e.symm v‖ ≤ (M*(1+c⁻¹))*‖v‖ := by
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
  intro i
  exact ((frozenFrameCovector e i).le_opNorm v).trans
    (mul_le_mul_of_nonneg_right (frozenFrameCovector_norm_bound g hc hM hg hupper e he i) (norm_nonneg v))

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Hausdorff_HausdorffDistortion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open scoped ENNReal NNReal

lemma ofReal_le_of_fourth_power_mul_le {A : ℝ} {C : ℝ≥0} (hC : 0 < C)
    {m : ℝ≥0∞} (h : ENNReal.ofReal A ≤ (C : ℝ≥0∞)^4*m) :
    ENNReal.ofReal (A/(C:ℝ)^4) ≤ m := by
  rw [ENNReal.ofReal_div_of_pos (by positivity), ENNReal.ofReal_pow (by positivity),
    ENNReal.ofReal_coe_nnreal]
  exact (ENNReal.div_le_iff' (by positivity) (by finiteness)).mpr h

end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Charts_CorrugationFrameVolume
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Yau.Jets Set MeasureTheory
open scoped ENNReal NNReal
noncomputable section

lemma frozenFrame_volume_lower (g : _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ)
    {c M A : ℝ} (hc : 0 < c) (hM : 0 < M)
    (hg : ∀ v : _root_.OAI.Yau.Jets.Coord, c*‖v‖^2 ≤ g v v) (hupper : ‖g‖ ≤ M)
    (e : _root_.OAI.Yau.Jets.Coord ≃L[ℝ] _root_.OAI.Yau.Jets.Coord)
    (he : ∀ i j, g (e (Pi.single i 1)) (e (Pi.single j 1)) = if i=j then 1 else 0)
    (y : _root_.OAI.Yau.Jets.Coord) (s : Set _root_.OAI.Yau.Jets.Coord) (hs : ENNReal.ofReal A ≤ volume s) :
    ENNReal.ofReal (A/(M*(1+c⁻¹))^4) ≤ volume ((fun v ↦ y+e v) '' s) := by
  let K : ℝ≥0 := ⟨M*(1+c⁻¹),by positivity⟩
  have hK : 0 < K := by change 0 < M*(1+c⁻¹); positivity
  have hLip : LipschitzWith K (fun x : _root_.OAI.Yau.Jets.Coord ↦ e.symm (x-y)) := by
    apply LipschitzWith.of_dist_le_mul
    intro x z
    simp only [dist_eq_norm,← map_sub,sub_sub_sub_cancel_right]
    exact frozenFrame_inverse_operator_bound g hc hM.le hg hupper e he (x-z)
  have hh := hLip.hausdorffMeasure_image_le (by norm_num : (0:ℝ) ≤ 4)
    ((fun v ↦ y+e v) '' s)
  have himg : (fun x : _root_.OAI.Yau.Jets.Coord ↦ e.symm (x-y)) '' ((fun v ↦ y+e v) '' s) = s := by
    rw [← Set.image_comp]
    simp
  have hv : (Measure.hausdorffMeasure (4:ℝ) : Measure _root_.OAI.Yau.Jets.Coord) = volume := by
    simpa using hausdorffMeasure_pi_real (ι := Fin 4)
  rw [himg,hv] at hh
  have hh' : ENNReal.ofReal A ≤ (K:ℝ≥0∞)^4 * volume ((fun v ↦ y+e v) '' s) := by
    simpa using hs.trans hh
  exact ofReal_le_of_fourth_power_mul_le hK hh'

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
-- module Solutions.OAIQ237_NY.NodalSets_Charts_MetricNormalizationStabilityLemmas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Yau.Geometry

open Yau.Jets

lemma sqrt_difference_bound_of_reference {a b m E : ℝ}
    (ha : 0 ≤ a) (hm : 0 < m) (hb : m^2 ≤ b) (hab : |a-b| ≤ E) :
    |Real.sqrt a-Real.sqrt b| ≤ E/m := by
  have hb0 : 0 ≤ b := (sq_nonneg m).trans hb
  have hmb : m ≤ Real.sqrt b := (Real.le_sqrt hm.le hb0).mpr hb
  have hsum : m ≤ Real.sqrt a+Real.sqrt b := by linarith [Real.sqrt_nonneg a]
  have hid : (Real.sqrt a-Real.sqrt b)*(Real.sqrt a+Real.sqrt b) = a-b := by
    nlinarith [Real.sq_sqrt ha,Real.sq_sqrt hb0]
  have hh : |Real.sqrt a-Real.sqrt b| *(Real.sqrt a+Real.sqrt b) ≤ E := by
    simpa only [abs_mul,abs_of_nonneg (by positivity : 0 ≤ Real.sqrt a+Real.sqrt b)] using
      (show |(Real.sqrt a-Real.sqrt b)*(Real.sqrt a+Real.sqrt b)| ≤ E by rw [hid]; exact hab)
  apply (le_div_iff₀ hm).mpr
  exact (mul_le_mul_of_nonneg_left hsum (abs_nonneg _)).trans hh

end Yau.Geometry

end

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

lemma corrugationCellRadius_properties (z : ℝ × ℝ) :
    0 ≤ corrugationCellRadius z ∧
    (corrugationCellRadius z)^2 = (corrugationCellPoint z).1^2+(corrugationCellPoint z).2^2 :=
  ⟨Real.sqrt_nonneg _,Real.sq_sqrt (by positivity)⟩

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_CorrugationAnnulusCell
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Set
noncomputable section

lemma centered_cell_integer_of_bounds (t : ℝ) (j : ℤ)
    (hlo : -1/2 ≤ t-(j:ℝ)) (hhi : t-(j:ℝ) < 1/2) :
    ⌊t+(1/2:ℝ)⌋ = j := by
  apply Int.floor_eq_iff.mpr
  constructor <;> linarith

lemma corrugationCellRadius_rectangle (z : ℝ × ℝ) (j k : ℤ)
    (h1 : z.1-(j:ℝ) ∈ Icc (1/16:ℝ) (3/32))
    (h2 : z.2-(k:ℝ) ∈ Icc (0:ℝ) (1/32)) :
    corrugationCellRadius z ∈ Icc (1/16:ℝ) (1/8) := by
  have hj := centered_cell_integer_of_bounds z.1 j (by linarith [h1.1]) (by linarith [h1.2])
  have hk := centered_cell_integer_of_bounds z.2 k (by linarith [h2.1]) (by linarith [h2.2])
  have hr := corrugationCellRadius_properties z
  have he : (corrugationCellRadius z)^2 = (z.1-(j:ℝ))^2+(z.2-(k:ℝ))^2 := by
    simpa only [corrugationCellPoint,corrugationCellIndex,hj,hk] using hr.2
  have hsq1 : (z.1-(j:ℝ))^2 ≤ (3/32:ℝ)^2 := sq_le_sq' (by linarith [h1.1]) h1.2
  have hsq2 : (z.2-(k:ℝ))^2 ≤ (1/32:ℝ)^2 := sq_le_sq' (by linarith [h2.1]) h2.2
  constructor
  · nlinarith [h1.1,sq_nonneg (z.2-(k:ℝ))]
  · nlinarith [hr.1]

lemma corrugation_rectangle_fixed_slope :
    ∃ l₀ : ℝ, 0 < l₀ ∧ ∀ (z : ℝ × ℝ) (j k : ℤ),
      z.1-(j:ℝ) ∈ Icc (1/16:ℝ) (3/32) →
      z.2-(k:ℝ) ∈ Icc (0:ℝ) (1/32) →
      l₀ ≤ corrugationSlope corrugationFixedAmplitude (1/4) (corrugationCellRadius z) := by
  obtain ⟨l₀,hl₀,hann⟩ := corrugationFixedAmplitude_spec.2.2.2
  exact ⟨l₀,hl₀,fun z j k h1 h2 ↦ hann _ (corrugationCellRadius_rectangle z j k h1 h2)⟩

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_CorrugationAnnulusBoxes
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Yau.Jets Set MeasureTheory
open scoped ENNReal
noncomputable section

lemma corrugationAnnulusBox_fast {r J : ℝ} (hJ : 0 < J) (j k : ℕ)
    {v : _root_.OAI.Yau.Jets.Coord} (hv : v ∈ corrugationAnnulusBox r J j k) :
    J*v 2-(j:ℝ) ∈ Icc (1/16:ℝ) (3/32) ∧
    J*v 3-(k:ℝ) ∈ Icc (0:ℝ) (1/32) := by
  have h2 : ((j:ℝ)+1/16)/J ≤ v 2 ∧ v 2 ≤ ((j:ℝ)+3/32)/J := ⟨hv.1 2,hv.2 2⟩
  have h3 : (k:ℝ)/J ≤ v 3 ∧ v 3 ≤ ((k:ℝ)+1/32)/J := ⟨hv.1 3,hv.2 3⟩
  have h2a := (div_le_iff₀ hJ).mp h2.1
  have h2b := (le_div_iff₀ hJ).mp h2.2
  have h3a := (div_le_iff₀ hJ).mp h3.1
  have h3b := (le_div_iff₀ hJ).mp h3.2
  constructor <;> constructor <;> linarith

lemma corrugationAnnulusBox_norm {r J : ℝ} (hr : 0 ≤ r) (hJ : 0 < J)
    {n : ℕ} (hn : (n:ℝ) ≤ J*r) (j k : Fin n)
    {v : _root_.OAI.Yau.Jets.Coord} (hv : v ∈ corrugationAnnulusBox r J j k) : ‖v‖ ≤ r := by
  have hj : (j:ℝ)+1 ≤ n := by exact_mod_cast j.isLt
  have hk : (k:ℝ)+1 ≤ n := by exact_mod_cast k.isLt
  have h2 := corrugationAnnulusBox_fast hJ j k hv
  apply (pi_norm_le_iff_of_nonneg hr).mpr
  intro i
  have hlo := hv.1 i
  have hhi := hv.2 i
  fin_cases i <;> simp only [Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val,
    Fin.reduceFinMk] at hlo hhi ⊢
  · exact abs_le.mpr ⟨hlo,hhi⟩
  · exact abs_le.mpr ⟨hlo,hhi⟩
  · change |v 2| ≤ r
    have hj0 : (0:ℝ) ≤ j := by positivity
    rw [abs_le]
    constructor <;> nlinarith [h2.1.1,h2.1.2]
  · change |v 3| ≤ r
    have hk0 : (0:ℝ) ≤ k := by positivity
    rw [abs_le]
    constructor <;> nlinarith [h2.2.1,h2.2.2]

lemma corrugationAnnulusBox_disjoint {r J : ℝ} (hJ : 0 < J)
    (p q : ℕ × ℕ) (hpq : p ≠ q) :
    Disjoint (corrugationAnnulusBox r J p.1 p.2) (corrugationAnnulusBox r J q.1 q.2) := by
  apply Set.disjoint_left.mpr
  intro v hv hw
  have hp := corrugationAnnulusBox_fast hJ p.1 p.2 hv
  have hq := corrugationAnnulusBox_fast hJ q.1 q.2 hw
  have he : p.1 ≠ q.1 ∨ p.2 ≠ q.2 := by
    by_contra h
    simp only [not_or,not_not] at h
    exact hpq (Prod.ext h.1 h.2)
  rcases he with he | he
  · rcases lt_or_gt_of_ne he with he | he
    · have hh : (p.1:ℝ)+1 ≤ q.1 := by exact_mod_cast he
      linarith [hp.1.1,hp.1.2,hq.1.1,hq.1.2]
    · have hh : (q.1:ℝ)+1 ≤ p.1 := by exact_mod_cast he
      linarith [hp.1.1,hp.1.2,hq.1.1,hq.1.2]
  · rcases lt_or_gt_of_ne he with he | he
    · have hh : (p.2:ℝ)+1 ≤ q.2 := by exact_mod_cast he
      linarith [hp.2.1,hp.2.2,hq.2.1,hq.2.2]
    · have hh : (q.2:ℝ)+1 ≤ p.2 := by exact_mod_cast he
      linarith [hp.2.1,hp.2.2,hq.2.1,hq.2.2]

lemma corrugationAnnulusBox_volume {r J : ℝ} (hr : 0 ≤ r) (hJ : 0 < J) (j k : ℕ) :
    volume (corrugationAnnulusBox r J j k) = ENNReal.ofReal (r^2/(256*J^2)) := by
  rw [corrugationAnnulusBox,Real.volume_Icc_pi]
  simp only [Fin.prod_univ_succ,Matrix.cons_val_zero,Matrix.cons_val_succ,Fin.prod_univ_zero,mul_one]
  have h1 : r- -r = 2*r := by ring
  have h2 : ((j:ℝ)+3/32)/J-((j:ℝ)+1/16)/J = 1/(32*J) := by ring
  have h3 : ((k:ℝ)+1/32)/J-(k:ℝ)/J = 1/(32*J) := by ring
  rw [h1,h2,h3]
  rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ 1/(32*J)),
    ← ENNReal.ofReal_mul (by positivity : 0 ≤ 2*r),
    ← ENNReal.ofReal_mul (by positivity : 0 ≤ 2*r)]
  congr 1
  ring

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_CorrugationAnnulusPacking
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Yau.Jets Set MeasureTheory
open scoped ENNReal
noncomputable section

lemma corrugationAnnulusPacking_compact (r J : ℝ) (n : ℕ) :
    IsCompact (corrugationAnnulusPacking r J n) := by
  simp only [corrugationAnnulusPacking,Finset.mem_univ,iUnion_true]
  exact isCompact_iUnion (fun _ ↦ isCompact_Icc)

lemma corrugationAnnulusPacking_volume {r J : ℝ} (hr : 0 ≤ r) (hJ : 0 < J) (n : ℕ) :
    volume (corrugationAnnulusPacking r J n) = ENNReal.ofReal ((n:ℝ)^2*r^2/(256*J^2)) := by
  have hd : Set.PairwiseDisjoint ((Finset.univ : Finset (Fin n × Fin n)) : Set (Fin n × Fin n))
      (fun p ↦ corrugationAnnulusBox r J p.1 p.2) := by
    intro p _ q _ hpq
    apply corrugationAnnulusBox_disjoint hJ (p.1.val,p.2.val) (q.1.val,q.2.val)
    intro he
    exact hpq (Prod.ext (Fin.ext (congrArg Prod.fst he)) (Fin.ext (congrArg Prod.snd he)))
  rw [corrugationAnnulusPacking,measure_biUnion_finset hd (fun _ _ ↦ measurableSet_Icc)]
  simp_rw [corrugationAnnulusBox_volume hr hJ]
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_prod,Fintype.card_fin,nsmul_eq_mul]
  rw [show ((n*n:ℕ):ℝ≥0∞) = ENNReal.ofReal ((n:ℝ)^2) by simp [pow_two],
    ← ENNReal.ofReal_mul (sq_nonneg (n:ℝ))]
  congr 1
  ring

lemma corrugationAnnulusPacking_volume_lower {r J : ℝ} (hr : 0 < r) (hJ : 0 < J)
    (hlarge : 2 ≤ J*r) :
    ENNReal.ofReal (r^4/1024) ≤ volume (corrugationAnnulusPacking r J ⌊J*r⌋₊) := by
  rw [corrugationAnnulusPacking_volume hr.le hJ]
  apply ENNReal.ofReal_le_ofReal
  have hn : J*r/2 ≤ (⌊J*r⌋₊:ℝ) := by
    have h := Nat.lt_floor_add_one (J*r)
    linarith
  have hn0 : (0:ℝ) ≤ ⌊J*r⌋₊ := by positivity
  apply (le_div_iff₀ (by positivity : 0 < 256*J^2)).mpr
  have hsq : (J*r/2)^2 ≤ (⌊J*r⌋₊:ℝ)^2 := sq_le_sq' (by linarith [mul_pos hJ hr]) hn
  have hh := mul_le_mul_of_nonneg_right hsq (sq_nonneg r)
  nlinarith only [hh]

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_CorrugationFixedCutoff
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

lemma corrugationFixedCutoff_spec : ∃ C : ℝ,
    0 < C ∧ ContDiff ℝ ∞ corrugationFixedCutoff ∧ HasCompactSupport corrugationFixedCutoff ∧
    tsupport corrugationFixedCutoff ⊆ ball (0:_root_.OAI.Yau.Jets.Coord) (1/2) ∧
    (∀ x, 0 ≤ corrugationFixedCutoff x ∧ corrugationFixedCutoff x ≤ 1) ∧
    (∀ x ∈ closedBall (0:_root_.OAI.Yau.Jets.Coord) (1/4), corrugationFixedCutoff =ᶠ[𝓝 x] (fun _ ↦ 1)) ∧
    ∀ x, ‖fderiv ℝ corrugationFixedCutoff x‖ ≤ C*(corrugationFixedCutoff x)^((7:ℝ)/8) :=
  Classical.choose_spec exists_corrugation_cutoff

end
end Yau.Geometry

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
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_CorrugationAnnulusFraction
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Yau.Jets Set MeasureTheory Metric
open scoped ENNReal Topology
noncomputable section

theorem corrugation_annulus_fraction {c M : ℝ} (hc : 0 < c) (hM : 0 < M) :
    ∃ δ l₀ B : ℝ, 0 < δ ∧ 0 < l₀ ∧ 0 < B ∧
      ∀ (g : _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ),
      (∀ v : _root_.OAI.Yau.Jets.Coord, c*‖v‖^2 ≤ g v v) → ‖g‖ ≤ M →
      ∀ e : _root_.OAI.Yau.Jets.Coord ≃L[ℝ] _root_.OAI.Yau.Jets.Coord,
      (∀ i j, g (e (Pi.single i 1)) (e (Pi.single j 1)) = if i=j then 1 else 0) →
      ∀ (y : _root_.OAI.Yau.Jets.Coord) (J R : ℝ), 0 < J → 0 < R → B ≤ J*R →
      ∃ A : Set _root_.OAI.Yau.Jets.Coord, IsCompact A ∧ A ⊆ closedBall y (R/4) ∧
        ENNReal.ofReal (δ*R^4) ≤ volume A ∧
        ∀ x ∈ A, corrugationFixedCutoff (R⁻¹ • (x-y)) = 1 ∧
          l₀ ≤ corrugationSlope corrugationFixedAmplitude (1/4)
            (corrugationCellRadius (corrugationFastMap J (frozenFrameCovector e 2)
              (frozenFrameCovector e 3) (x-y))) := by
  let C : ℝ := 16*(1+c⁻¹)
  let K : ℝ := M*(1+c⁻¹)
  have hC : 0 < C := by dsimp [C] <;> positivity
  have hK : 0 < K := by dsimp [K] <;> positivity
  obtain ⟨l₀,hl₀,hwell⟩ := corrugation_rectangle_fixed_slope
  refine ⟨1/(1024*C^4*K^4),l₀,2*C,by positivity,hl₀,by positivity,?_⟩
  intro g hg hupper e he y J R hJ hR hlarge
  let r : ℝ := R/C
  have hr : 0 < r := div_pos hR hC
  have hlarge' : 2 ≤ J*r := by
    dsimp [r]
    rw [← mul_div_assoc,le_div_iff₀ hC]
    exact hlarge
  let n : ℕ := ⌊J*r⌋₊
  let P := corrugationAnnulusPacking r J n
  let A := (fun v ↦ y+e v) '' P
  have hP : IsCompact P := corrugationAnnulusPacking_compact r J n
  have hsub : ∀ x ∈ A, ∃ v ∈ P, x=y+e v ∧ ‖v‖ ≤ r := by
    intro x hx
    obtain ⟨v,hv,rfl⟩ := hx
    refine ⟨v,hv,rfl,?_⟩
    obtain ⟨p,_,hvp⟩ := Set.mem_iUnion₂.mp hv
    exact corrugationAnnulusBox_norm hr.le hJ (Nat.floor_le (mul_pos hJ hr).le) p.1 p.2 hvp
  have hdist : ∀ x ∈ A, ‖x-y‖ ≤ R/4 := by
    intro x hx
    obtain ⟨v,hv,rfl,hvn⟩ := hsub x hx
    simp only [add_sub_cancel_left]
    calc
      ‖e v‖ ≤ (4*(1+c⁻¹))*‖v‖ := frozenFrame_operator_bound g hc hg e he v
      _ ≤ (4*(1+c⁻¹))*r := mul_le_mul_of_nonneg_left hvn (by positivity)
      _ = R/4 := by dsimp [r,C]; field_simp <;> ring
  refine ⟨A,hP.image (continuous_const.add e.continuous),?_,?_,?_⟩
  · intro x hx
    simpa only [mem_closedBall,dist_eq_norm] using hdist x hx
  · have hv := frozenFrame_volume_lower g hc hM hg hupper e he y P
      (corrugationAnnulusPacking_volume_lower hr hJ hlarge')
    convert hv using 1
    all_goals try with_reducible_and_instances rfl
    dsimp [r,K]
    congr 1
    field_simp
  · intro x hx
    constructor
    · obtain ⟨_,_,_,_,_,_,hcenter,_⟩ := corrugationFixedCutoff_spec
      apply (hcenter (R⁻¹ • (x-y)) ?_).eq_of_nhds
      rw [mem_closedBall,dist_zero_right,norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hR)]
      calc
        _ ≤ R⁻¹*(R/4) := mul_le_mul_of_nonneg_left (hdist x hx) (inv_nonneg.mpr hR.le)
        _ = 1/4 := by field_simp
    · obtain ⟨v,hv,rfl,hvn⟩ := hsub x hx
      obtain ⟨p,_,hvp⟩ := Set.mem_iUnion₂.mp hv
      have hh := corrugationAnnulusBox_fast hJ p.1 p.2 hvp
      have heq : corrugationFastMap J (frozenFrameCovector e 2) (frozenFrameCovector e 3)
          (y+e v-y) = (J*v 2,J*v 3) := by
        simp [corrugationFastMap,frozenFrameCovector,ContinuousLinearMap.prod_apply]
      rw [heq]
      exact hwell _ (p.1:ℕ) (p.2:ℕ) hh.1 hh.2

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_CorrugationAssembly
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Yau.Jets Set Metric Filter
open scoped ContDiff Topology
noncomputable section
variable {ι : Type*}

lemma corrugationSum_smooth (I : Finset ι) (χ : _root_.OAI.Yau.Jets.Coord → ℝ) (hχ : ContDiff ℝ ∞ χ)
    (amp J R : ℝ) (s : ι → ℝ) (e : ι → _root_.OAI.Yau.Jets.Coord ≃L[ℝ] _root_.OAI.Yau.Jets.Coord) (y : ι → _root_.OAI.Yau.Jets.Coord) :
    ContDiff ℝ ∞ (corrugationSum I χ amp J R s e y) := by
  apply ContDiff.sum
  intro i _
  exact localizedCorrugation_smooth χ _ hχ (corrugationPeriodicWell_smooth amp) _ _ _ _ _ _

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

lemma unit_interval_subdivision {n : ℕ} (hn : 0 < n) {t : ℝ}
    (ht0 : 0 ≤ t) (htn : t ≤ n) :
    ∃ k : Fin n, (k:ℝ) ≤ t ∧ t ≤ (k:ℝ)+1 := by
  by_cases he : t = n
  · refine ⟨⟨n-1,by omega⟩,?_,?_⟩
    all_goals
      have hn1 : ((n-1:ℕ):ℝ)+1 = n := by exact_mod_cast (Nat.sub_add_cancel hn)
      change _ ≤ _
      rw [he]
      linarith
  · have ht : t < n := lt_of_le_of_ne htn he
    let k : ℕ := ⌊t⌋₊
    have hk0 : (k:ℝ) ≤ t := Nat.floor_le ht0
    have hk1 : t < (k:ℝ)+1 := Nat.lt_floor_add_one t
    have hkn : k < n := by exact_mod_cast (hk0.trans_lt ht)
    exact ⟨⟨k,hkn⟩,hk0,hk1.le⟩

lemma corrugationCube_closed_cover (o : _root_.OAI.Yau.Jets.Coord) {L : ℝ} (hL : 0 < L)
    {n : ℕ} (hn : 0 < n) (x : _root_.OAI.Yau.Jets.Coord) (hx : x ∈ Set.Icc o (fun i ↦ o i+L)) :
    ∃ k : Fin 4 → Fin n,
      x ∈ closedBall (corrugationCubeCenter o L n k) ((L/(n:ℝ))/2) := by
  have hnR : (0:ℝ) < n := by exact_mod_cast hn
  have hR : 0 < L/(n:ℝ) := div_pos hL hnR
  have hRn : (L/(n:ℝ))*(n:ℝ) = L := div_mul_cancel₀ L hnR.ne'
  have hk : ∀ i : Fin 4, ∃ k : Fin n,
      (k:ℝ) ≤ (x i-o i)/(L/(n:ℝ)) ∧ (x i-o i)/(L/(n:ℝ)) ≤ (k:ℝ)+1 := by
    intro i
    apply unit_interval_subdivision hn
    · exact div_nonneg (sub_nonneg.mpr (hx.1 i)) hR.le
    · apply (div_le_iff₀ hR).mpr
      have hi := hx.2 i
      nlinarith
  choose k hk using hk
  refine ⟨k,?_⟩
  rw [mem_closedBall,dist_eq_norm]
  apply (pi_norm_le_iff_of_nonneg (by positivity : 0 ≤ (L/(n:ℝ))/2)).mpr
  intro i
  have hlo := (le_div_iff₀ hR).mp (hk i).1
  have hhi := (div_le_iff₀ hR).mp (hk i).2
  change |x i-(o i+(L/(n:ℝ))*((k i:ℝ)+1/2))| ≤ _
  rw [abs_le]
  constructor <;> nlinarith

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_CorrugationCubeMeasure
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Yau.Jets Set Metric MeasureTheory
open scoped ENNReal
noncomputable section

lemma corrugationCube_closed_inside (o : _root_.OAI.Yau.Jets.Coord) {L : ℝ} (hL : 0 < L)
    {n : ℕ} (hn : 0 < n) (k : Fin 4 → Fin n) :
    closedBall (corrugationCubeCenter o L n k) ((L/(n:ℝ))/2) ⊆ Icc o (fun i ↦ o i+L) := by
  have hnR : (0:ℝ) < n := by exact_mod_cast hn
  have hR : 0 < L/(n:ℝ) := div_pos hL hnR
  have hRn : (L/(n:ℝ))*(n:ℝ) = L := div_mul_cancel₀ L hnR.ne'
  intro x hx
  have hdist : ‖x-corrugationCubeCenter o L n k‖ ≤ (L/(n:ℝ))/2 := by
    simpa only [mem_closedBall,dist_eq_norm] using hx
  constructor <;> intro i
  all_goals
    have hi := (norm_le_pi_norm (x-corrugationCubeCenter o L n k) i).trans hdist
    change |x i-(o i+(L/(n:ℝ))*((k i:ℝ)+1/2))| ≤ _ at hi
    have ha := abs_le.mp hi
    have hk0 : (0:ℝ) ≤ (k i:ℝ) := by positivity
    have hk1 : (k i:ℝ)+1 ≤ n := by exact_mod_cast (k i).isLt
    nlinarith

lemma coordinate_cube_volume (y : _root_.OAI.Yau.Jets.Coord) {R : ℝ} (hR : 0 ≤ R) :
    volume (closedBall y (R/2)) = ENNReal.ofReal (R^4) := by
  rw [Real.volume_pi_closedBall y (by positivity)]
  norm_num [show 2*(R/2)=R by ring]

lemma coordinate_cube_volume_real (y : _root_.OAI.Yau.Jets.Coord) {R : ℝ} (hR : 0 ≤ R) :
    volume.real (closedBall y (R/2)) = R^4 := by
  rw [measureReal_def,coordinate_cube_volume y hR,ENNReal.toReal_ofReal (by positivity)]

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

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_CorrugationOldSpeed
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

lemma metricGradient_contDiffAt_local
    (g : _root_.OAI.Yau.Jets.Coord → _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ) (S : _root_.OAI.Yau.Jets.Coord → ℝ) (x : _root_.OAI.Yau.Jets.Coord)
    (hg : ContDiffAt ℝ ∞ g x) (hS : ContDiffAt ℝ ∞ S x)
    (hp : ∀ v, v ≠ 0 → 0 < g x v v) :
    ContDiffAt ℝ ∞ (metricGradient g S) x := by
  have hi : ContDiffAt ℝ ∞
      (ContinuousLinearMap.inverse : (_root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ) → ((_root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ) →L[ℝ] _root_.OAI.Yau.Jets.Coord)) (g x) := by
    convert contDiffAt_map_inverse (n := ∞) (positiveMetricEquiv (g x) hp) using 1
    all_goals try with_reducible_and_instances rfl
    rfl
  exact (hi.comp x hg).clm_apply (hS.fderiv_right (m := ∞) (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top))

theorem corrugation_old_speed_freezing
    (g : _root_.OAI.Yau.Jets.Coord → _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ) (S : _root_.OAI.Yau.Jets.Coord → ℝ)
    {D U : Set _root_.OAI.Yau.Jets.Coord} (hD : IsCompact D) (hconv : Convex ℝ D)
    (hU : IsOpen U) (hDU : D ⊆ U)
    (hg : ContDiffOn ℝ ∞ g U) (hS : ContDiffOn ℝ ∞ S U)
    (hp : ∀ y ∈ U, ∀ v, v ≠ 0 → 0 < g y v v)
    (hn : ∀ y ∈ D, metricGradient g S y ≠ 0) :
    ∃ C : ℝ, 0 < C ∧ ∀ x ∈ D, ∀ y ∈ D,
      |corrugationOldSlope g S x-corrugationOldSlope g S y| ≤
        corrugationOldSlope g S y*C*‖x-y‖ := by
  obtain ⟨m,hm,B,hB,hs⟩ := corrugationOldSlope_compact_bounds g S hD hU hDU hg hS hp hn
  have hgrad : ContDiffOn ℝ ∞ (metricGradient g S) U := by
    intro x hx
    exact (metricGradient_contDiffAt_local g S x (hg.contDiffAt (hU.mem_nhds hx))
      (hS.contDiffAt (hU.mem_nhds hx)) (hp x hx)).contDiffWithinAt
  have hsq : ContDiffOn ℝ ∞ (fun x ↦ g x (metricGradient g S x) (metricGradient g S x)) U :=
    (hg.clm_apply hgrad).clm_apply hgrad
  obtain ⟨A,hA,hfreeze⟩ := smooth_compact_freezing _ hD hconv hU hDU hsq
  refine ⟨A/m^2,by positivity,?_⟩
  intro x hx y hy
  have hxp := hp x (hDU hx) _ (hn x hx)
  have hyp := hp y (hDU hy) _ (hn y hy)
  have hsy : m^2 ≤ g y (metricGradient g S y) (metricGradient g S y) := by
    have hh := Real.sq_sqrt hyp.le
    have hh' := (hs y hy).1
    change m ≤ Real.sqrt _ at hh'
    nlinarith
  have hh := sqrt_difference_bound_of_reference hxp.le hm hsy (hfreeze x hx y hy)
  change |corrugationOldSlope g S x-corrugationOldSlope g S y| ≤ _ at hh
  have hmul := mul_le_mul_of_nonneg_right (hs y hy).1
    (show 0 ≤ (A/m^2)*‖x-y‖ by positivity)
  calc
    _ ≤ (A*‖x-y‖)/m := hh
    _ = m*((A/m^2)*‖x-y‖) := by field_simp
    _ ≤ corrugationOldSlope g S y*((A/m^2)*‖x-y‖) := hmul
    _ = _ := by ring

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
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_CorrugationNormalizedGradient
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

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_IntegratedSpeedGain
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Set MeasureTheory
noncomputable section
variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

lemma integrated_speed_gain {Q A : Set X} (hQ : MeasurableSet Q) (hA : MeasurableSet A)
    (hAQ : A ⊆ Q) (hfin : μ Q ≠ ⊤) (f : X → ℝ) (hf : IntegrableOn f Q μ)
    (a b : ℝ) (hbase : ∀ x ∈ Q, a ≤ f x) (hgain : ∀ x ∈ A, a+b ≤ f x) :
    a*μ.real Q+b*μ.real A ≤ ∫ x in Q, f x ∂μ := by
  have ha : IntegrableOn (fun _ : X ↦ a) Q μ := integrableOn_const hfin
  have hb : IntegrableOn (fun _ : X ↦ b) Q μ := integrableOn_const hfin
  have hi : IntegrableOn (A.indicator (fun _ : X ↦ b)) Q μ := hb.indicator hA
  have hle : ∫ x in Q, a+A.indicator (fun _ : X ↦ b) x ∂μ ≤ ∫ x in Q, f x ∂μ := by
    apply setIntegral_mono_on (ha.add hi) hf hQ
    intro x hx
    by_cases hxA : x ∈ A
    · simpa only [Pi.add_apply,Set.indicator_of_mem hxA] using hgain x hxA
    · simpa only [Pi.add_apply,Set.indicator_of_notMem hxA,add_zero] using hbase x hx
  rw [integral_add ha hi,setIntegral_indicator hA,Set.inter_eq_right.mpr hAQ,
    setIntegral_const,setIntegral_const] at hle
  simpa only [smul_eq_mul,mul_comm] using hle

lemma integrated_speed_factor {Q A : Set X} (hQ : MeasurableSet Q) (hA : MeasurableSet A)
    (hAQ : A ⊆ Q) (hfin : μ Q ≠ ⊤) (f old : X → ℝ)
    (hf : IntegrableOn f Q μ) (ho : IntegrableOn old Q μ)
    {s δ q ε : ℝ} (hs : 0 < s) (hδ : 0 < δ) (hq : 1 < q)
    (hfrac : δ*μ.real Q ≤ μ.real A)
    (hbudget : ε*(2+δ*(q-1)/2) ≤ δ*(q-1)/2)
    (hbase : ∀ x ∈ Q, s*(1-ε) ≤ f x)
    (hgain : ∀ x ∈ A, s*(q-ε) ≤ f x)
    (hold : ∀ x ∈ Q, old x ≤ s*(1+ε)) :
    (1+δ*(q-1)/2)*(∫ x in Q, old x ∂μ) ≤ ∫ x in Q, f x ∂μ := by
  have hh := integrated_speed_gain hQ hA hAQ hfin f hf (s*(1-ε)) (s*(q-1)) hbase
    (fun x hx ↦ by convert hgain x hx using 1; ring)
  have hupper : ∫ x in Q, old x ∂μ ≤ s*(1+ε)*μ.real Q := by
    have h := setIntegral_mono_on ho (integrableOn_const hfin) hQ hold
    simpa only [setIntegral_const,smul_eq_mul,mul_comm] using h
  have hv : 0 ≤ μ.real Q := measureReal_nonneg
  have hco : 0 ≤ 1+δ*(q-1)/2 := by positivity
  have hb := mul_le_mul_of_nonneg_left hbudget (mul_nonneg hs.le hv)
  have hm := mul_le_mul_of_nonneg_left hfrac (mul_nonneg hs.le (sub_nonneg.mpr hq.le))
  calc
    _ ≤ (1+δ*(q-1)/2)*(s*(1+ε)*μ.real Q) := mul_le_mul_of_nonneg_left hupper hco
    _ ≤ s*(1-ε)*μ.real Q+s*(q-1)*(δ*μ.real Q) := by nlinarith only [hb]
    _ ≤ s*(1-ε)*μ.real Q+s*(q-1)*μ.real A := add_le_add le_rfl hm
    _ ≤ _ := hh

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_CorrugationCellGain
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Yau.Jets Set Filter Metric MeasureTheory
open scoped ContDiff Topology ENNReal
noncomputable section

theorem corrugation_cell_integrated_gain {c M : ℝ} (hc : 0 < c) (hM : 0 < M) :
    ∃ γ : ℝ, 0 < γ ∧
      ∀ (g : _root_.OAI.Yau.Jets.Coord → _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ) (S : _root_.OAI.Yau.Jets.Coord → ℝ)
      (D U : Set _root_.OAI.Yau.Jets.Coord), IsCompact D → Convex ℝ D → IsOpen U → D ⊆ U →
      ContDiffOn ℝ ∞ g U → ContDiffOn ℝ ∞ S U →
      (∀ y ∈ U, ∀ v, v ≠ 0 → 0 < g y v v) →
      (∀ y ∈ D, metricGradient g S y ≠ 0) →
      (∀ y ∈ D, ‖g y‖ ≤ M ∧ ∀ v, c*‖v‖^2 ≤ g y v v) →
      ∀ L : ℝ, 0 < L → ∀ᶠ k : ℕ in atTop,
      ∀ y ∈ D, closedBall y (corrugationScale L k/2) ⊆ D →
      ∀ e : _root_.OAI.Yau.Jets.Coord ≃L[ℝ] _root_.OAI.Yau.Jets.Coord,
      e (Pi.single 0 1) = (corrugationOldSlope g S y)⁻¹ • metricGradient g S y →
      (∀ i j, g y (e (Pi.single i 1)) (e (Pi.single j 1)) = if i=j then 1 else 0) →
      let W := localizedCorrugation corrugationFixedCutoff (corrugationPeriodicWell corrugationFixedAmplitude)
        (corrugationOldSlope g S y) (corrugationFrequency k) (corrugationScale L k)
        (frozenFrameCovector e 2) (frozenFrameCovector e 3) y
      (1+γ)*(∫ x in closedBall y (corrugationScale L k/2), corrugationOldSlope g S x) ≤
        ∫ x in closedBall y (corrugationScale L k/2), corrugationOldSlope g (S+W) x := by
  obtain ⟨δ,l₀,B,hδ,hl₀,hB,hfrac⟩ := corrugation_annulus_fraction hc hM
  let q : ℝ := Real.sqrt (1+l₀^2)
  have hq : 1 < q := by
    dsimp [q]
    exact (Real.lt_sqrt (by norm_num)).mpr (by nlinarith [sq_pos_of_pos hl₀])
  let γ : ℝ := δ*(q-1)/2
  have hγ : 0 < γ := by dsimp [γ] <;> positivity
  refine ⟨γ,hγ,?_⟩
  intro g S D U hD hconv hU hDU hg hS hp hn hcmp L hL
  obtain ⟨Cχ,hCχ,hχ,hχc,hχsupp,hχrange,hχcenter,hχder⟩ := corrugationFixedCutoff_spec
  obtain ⟨C,hC,hnew⟩ := corrugation_speed_freezing g S corrugationFixedCutoff hD hconv
    hU hDU hg hS hp hn hχ hχc (fun x ↦ (hχrange x).1) (fun x ↦ (hχrange x).2)
    corrugationFixedAmplitude_spec.1.le corrugationFixedAmplitude_spec.2.1 hL
  obtain ⟨C₀,hC₀,hold⟩ := corrugation_old_speed_freezing g S hD hconv hU hDU hg hS hp hn
  let E := fun k ↦ (C+C₀)*corrugationGradientRate L k
  have hE : Tendsto (fun k ↦ E k*(2+γ)) atTop (𝓝 0) := by
    simpa [E] using ((corrugationGradientRate_tendsto hL).const_mul (C+C₀)).mul_const (2+γ)
  filter_upwards [hnew,hE.eventually_lt_const hγ,
    (corrugation_frequency_scale_tendsto hL).eventually_ge_atTop B] with k hk hEk hBk
  intro y hy hQD e he0 he
  dsimp only
  let R := corrugationScale L k
  let J := corrugationFrequency k
  let s := corrugationOldSlope g S y
  let W := localizedCorrugation corrugationFixedCutoff (corrugationPeriodicWell corrugationFixedAmplitude)
    s J R (frozenFrameCovector e 2) (frozenFrameCovector e 3) y
  let Q := closedBall y (R/2)
  have hR : 0 < R := corrugationScale_positive hL k
  have hJ : 0 < J := corrugationFrequency_positive k
  have hs : 0 < s := corrugationOldSlope_positive g S y (hp y (hDU hy)) (hn y hy)
  have hρ : 0 ≤ corrugationGradientRate L k := (corrugationGradientRate_positive hL k).le
  have hRρ : R ≤ corrugationGradientRate L k := by
    dsimp [R,corrugationGradientRate]
    have hh : 0 ≤ 1/(corrugationFrequency k*corrugationScale L k) := by positivity
    linarith
  have hdist : ∀ x ∈ Q, ‖x-y‖ ≤ R := by
    intro x hx
    have hh : ‖x-y‖ ≤ R/2 := by simpa only [Q,mem_closedBall,dist_eq_norm] using hx
    linarith
  obtain ⟨A,hA,hAsmall,hvol,hgood⟩ := hfrac (g y) (hcmp y hy).2 (hcmp y hy).1 e he y J R hJ hR hBk
  have hAQ : A ⊆ Q := hAsmall.trans (closedBall_subset_closedBall (by linarith))
  have hfin : volume Q ≠ ⊤ := (isCompact_closedBall y (R/2)).measure_ne_top
  have hvolreal : δ*volume.real Q ≤ volume.real A := by
    rw [coordinate_cube_volume_real y hR.le]
    exact (ENNReal.toReal_ofReal (by positivity : 0 ≤ δ*R^4)).symm.trans_le
      (ENNReal.toReal_mono hA.measure_ne_top hvol)
  have hW : ContDiff ℝ ∞ W := localizedCorrugation_smooth _ _ hχ
    (corrugationPeriodicWell_smooth _) _ _ _ _ _ _
  have hfs : IntegrableOn (corrugationOldSlope g (S+W)) Q :=
    ((corrugationOldSlope_continuousOn g (S+W) hU hg (hS.add hW.contDiffOn) hp).mono
      (hQD.trans hDU)).integrableOn_compact (isCompact_closedBall y (R/2))
  have hos : IntegrableOn (corrugationOldSlope g S) Q :=
    ((corrugationOldSlope_continuousOn g S hU hg hS hp).mono
      (hQD.trans hDU)).integrableOn_compact (isCompact_closedBall y (R/2))
  have happrox : ∀ x ∈ Q,
      s*Real.sqrt (1+(corrugationFixedCutoff (R⁻¹ • (x-y))*
        corrugationSlope corrugationFixedAmplitude (1/4)
          (corrugationCellRadius (corrugationFastMap J (frozenFrameCovector e 2)
            (frozenFrameCovector e 3) (x-y))))^2)-s*E k ≤ corrugationOldSlope g (S+W) x := by
    intro x hx
    have hh := (abs_le.mp (hk y hy x (hQD hx) (hdist x hx) e he0 he)).1
    have herr : s*C*corrugationGradientRate L k ≤ s*E k := by
      dsimp [E]
      nlinarith [mul_nonneg (mul_nonneg hs.le hC₀.le) hρ]
    change -(s*C*corrugationGradientRate L k) ≤ corrugationOldSlope g (S+W) x-_ at hh
    linarith
  apply integrated_speed_factor measurableSet_closedBall hA.measurableSet hAQ hfin
    (corrugationOldSlope g (S+W)) (corrugationOldSlope g S) hfs hos hs hδ hq hvolreal hEk.le
  · intro x hx
    have hroot : 1 ≤ Real.sqrt (1+(corrugationFixedCutoff (R⁻¹ • (x-y))*
        corrugationSlope corrugationFixedAmplitude (1/4)
          (corrugationCellRadius (corrugationFastMap J (frozenFrameCovector e 2)
            (frozenFrameCovector e 3) (x-y))))^2) := by
      apply Real.one_le_sqrt.mpr
      linarith [sq_nonneg (corrugationFixedCutoff (R⁻¹ • (x-y))*
        corrugationSlope corrugationFixedAmplitude (1/4)
          (corrugationCellRadius (corrugationFastMap J (frozenFrameCovector e 2)
            (frozenFrameCovector e 3) (x-y))))]
    have hh := mul_le_mul_of_nonneg_left hroot hs.le
    linarith [happrox x hx]
  · intro x hx
    have hh := happrox x (hAQ hx)
    rw [(hgood x hx).1,one_mul] at hh
    have hroot : q ≤ Real.sqrt (1+(corrugationSlope corrugationFixedAmplitude (1/4)
        (corrugationCellRadius (corrugationFastMap J (frozenFrameCovector e 2)
          (frozenFrameCovector e 3) (x-y))))^2) := by
      apply Real.sqrt_le_sqrt
      have h := (hgood x hx).2
      nlinarith
    have hmul := mul_le_mul_of_nonneg_left hroot hs.le
    linarith
  · intro x hx
    have hh := (abs_le.mp (hold x (hQD hx) y hy)).2
    have herr : s*C₀*‖x-y‖ ≤ s*E k := by
      calc
        _ ≤ s*C₀*corrugationGradientRate L k :=
          mul_le_mul_of_nonneg_left ((hdist x hx).trans hRρ) (mul_nonneg hs.le hC₀.le)
        _ ≤ s*E k := by dsimp [E] <;> nlinarith [mul_nonneg (mul_nonneg hs.le hC.le) hρ]
    linarith

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_CorrugationGridAssembly
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Yau.Jets Set Metric Filter
open scoped ContDiff Topology
noncomputable section

lemma corrugationGridSum_smooth (o : _root_.OAI.Yau.Jets.Coord) (L : ℝ) (n : ℕ) (χ : _root_.OAI.Yau.Jets.Coord → ℝ)
    (hχ : ContDiff ℝ ∞ χ) (amp J : ℝ)
    (s : (Fin 4 → Fin n) → ℝ) (e : (Fin 4 → Fin n) → _root_.OAI.Yau.Jets.Coord ≃L[ℝ] _root_.OAI.Yau.Jets.Coord) :
    ContDiff ℝ ∞ (corrugationGridSum o L n χ amp J s e) :=
  corrugationSum_smooth _ χ hχ _ _ _ _ _ _

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_CorrugationClosedCubeLocality
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Yau.Jets Set Metric Filter
open scoped ContDiff Topology
noncomputable section

lemma corrugationCube_closed_open_disjoint (o : _root_.OAI.Yau.Jets.Coord) {L : ℝ} (hL : 0 < L)
    {n : ℕ} (hn : 0 < n) (k j : Fin 4 → Fin n) (hkj : k ≠ j) :
    Disjoint (closedBall (corrugationCubeCenter o L n k) ((L/(n:ℝ))/2))
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
  apply closedBall_disjoint_ball
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

lemma corrugationGridSum_closed_cube_eventually (o : _root_.OAI.Yau.Jets.Coord) {L : ℝ} (hL : 0 < L)
    {n : ℕ} (hn : 0 < n) (χ : _root_.OAI.Yau.Jets.Coord → ℝ) (hχ : tsupport χ ⊆ ball (0:_root_.OAI.Yau.Jets.Coord) (1/2))
    (amp J : ℝ) (s : (Fin 4 → Fin n) → ℝ) (e : (Fin 4 → Fin n) → _root_.OAI.Yau.Jets.Coord ≃L[ℝ] _root_.OAI.Yau.Jets.Coord)
    (i : Fin 4 → Fin n) (x : _root_.OAI.Yau.Jets.Coord)
    (hx : x ∈ closedBall (corrugationCubeCenter o L n i) ((L/(n:ℝ))/2)) :
    corrugationGridSum o L n χ amp J s e =ᶠ[𝓝 x]
      localizedCorrugation χ (corrugationPeriodicWell amp) (s i) J (L/(n:ℝ))
        (frozenFrameCovector (e i) 2) (frozenFrameCovector (e i) 3) (corrugationCubeCenter o L n i) := by
  classical
  let w := fun j ↦ localizedCorrugation χ (corrugationPeriodicWell amp) (s j) J (L/(n:ℝ))
    (frozenFrameCovector (e j) 2) (frozenFrameCovector (e j) 3) (corrugationCubeCenter o L n j)
  have hnR : (0:ℝ) < n := by exact_mod_cast hn
  have hz : ∀ j, j ≠ i → w j =ᶠ[𝓝 x] 0 := by
    intro j hji
    apply notMem_tsupport_iff_eventuallyEq.mp
    intro hj
    have hb := localizedCorrugation_cube χ _ hχ _ _ (div_pos hL hnR) _ _ _ hj
    exact Set.disjoint_left.mp (corrugationCube_closed_open_disjoint o hL hn i j hji.symm) hx hb
  have he : ∀ᶠ z in 𝓝 x, ∀ j, j ≠ i → w j z = 0 := by
    apply Filter.eventually_all.mpr
    intro j
    by_cases hji : j=i
    · simp [hji]
    · filter_upwards [hz j hji] with z hz
      exact fun _ ↦ hz
  filter_upwards [he] with z hz
  change ∑ j ∈ (Finset.univ : Finset (Fin 4 → Fin n)), w j z = w i z
  exact Finset.sum_eq_single i (fun j _ hji ↦ hz j hji) (by simp)

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_CorrugationCubeIntegral
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Yau.Jets Set Metric MeasureTheory Filter
noncomputable section

lemma coordinate_ball_ae_closed (y : _root_.OAI.Yau.Jets.Coord) {r : ℝ} (hr : 0 < r) :
    ball y r =ᵐ[volume] closedBall y r := by
  apply ae_eq_of_subset_of_measure_ge ball_subset_closedBall
  · rw [Real.volume_pi_ball y hr,Real.volume_pi_closedBall y hr.le]
  · exact measurableSet_ball.nullMeasurableSet
  · exact (isCompact_closedBall y r).measure_ne_top

lemma corrugation_cube_integral_sum (o : _root_.OAI.Yau.Jets.Coord) {L : ℝ} (hL : 0 < L)
    {n : ℕ} (hn : 0 < n) (f : _root_.OAI.Yau.Jets.Coord → ℝ)
    (hf : IntegrableOn f (Icc o (fun i ↦ o i+L))) :
    ∫ x in Icc o (fun i ↦ o i+L), f x =
      ∑ i : Fin 4 → Fin n, ∫ x in closedBall (corrugationCubeCenter o L n i) ((L/(n:ℝ))/2), f x := by
  let O := fun i : Fin 4 → Fin n ↦ ball (corrugationCubeCenter o L n i) ((L/(n:ℝ))/2)
  let Q := fun i : Fin 4 → Fin n ↦ closedBall (corrugationCubeCenter o L n i) ((L/(n:ℝ))/2)
  have hnR : (0:ℝ) < n := by exact_mod_cast hn
  have hR : 0 < (L/(n:ℝ))/2 := by positivity
  have heq : ∀ i, O i =ᵐ[volume] Q i := fun i ↦ coordinate_ball_ae_closed _ hR
  have hcover : (⋃ i, Q i) = Icc o (fun i ↦ o i+L) := by
    apply Set.Subset.antisymm
    · exact Set.iUnion_subset (fun i ↦ corrugationCube_closed_inside o hL hn i)
    · intro x hx
      obtain ⟨i,hi⟩ := corrugationCube_closed_cover o hL hn x hx
      exact Set.mem_iUnion.mpr ⟨i,hi⟩
  have hU : (⋃ i, O i) =ᵐ[volume] Icc o (fun i ↦ o i+L) := by
    rw [← hcover]
    exact Filter.EventuallyEq.countable_iUnion heq
  have hsum := integral_iUnion_fintype (fun i ↦ measurableSet_ball (x := corrugationCubeCenter o L n i))
    (fun i j hij ↦ corrugationCube_balls_disjoint o hL hn i j hij)
    (fun i ↦ hf.mono_set (ball_subset_closedBall.trans (corrugationCube_closed_inside o hL hn i)))
  calc
    _ = ∫ x in ⋃ i, O i, f x := (setIntegral_congr_set hU).symm
    _ = ∑ i, ∫ x in O i, f x := hsum
    _ = _ := Finset.sum_congr rfl (fun i _ ↦ setIntegral_congr_set (heq i))

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_CorrugationGridProperties
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

lemma corrugationEnvelopePerturbation_smooth (o : _root_.OAI.Yau.Jets.Coord) (L : ℝ) (k : ℕ)
    (g : _root_.OAI.Yau.Jets.Coord → _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ) (S χ : _root_.OAI.Yau.Jets.Coord → ℝ) (amp : ℝ)
    (e : (Fin 4 → Fin (corrugationSubdivision k)) → _root_.OAI.Yau.Jets.Coord ≃L[ℝ] _root_.OAI.Yau.Jets.Coord)
    (hχ : ContDiff ℝ ∞ χ) :
    ContDiff ℝ ∞ (corrugationEnvelopePerturbation o L k g S χ amp e) :=
  corrugationGridSum_smooth o L _ χ hχ _ _ _ _

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_CorrugationGridGain
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Yau.Jets Set Filter Metric MeasureTheory
open scoped ContDiff Topology
noncomputable section

theorem corrugation_grid_integrated_gain_oai {c M : ℝ} (hc : 0 < c) (hM : 0 < M) :
    ∃ γ : ℝ, 0 < γ ∧ ∀ (o : _root_.OAI.Yau.Jets.Coord) (L : ℝ), 0 < L →
      ∀ (g : _root_.OAI.Yau.Jets.Coord → _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ) (S : _root_.OAI.Yau.Jets.Coord → ℝ)
      (U : Set _root_.OAI.Yau.Jets.Coord), IsOpen U → Icc o (fun j ↦ o j+L) ⊆ U →
      ContDiffOn ℝ ∞ g U → ContDiffOn ℝ ∞ S U →
      (∀ y ∈ U, ∀ v, v ≠ 0 → 0 < g y v v) →
      (∀ y ∈ Icc o (fun j ↦ o j+L), metricGradient g S y ≠ 0) →
      (∀ y ∈ Icc o (fun j ↦ o j+L), ‖g y‖ ≤ M ∧ ∀ v, c*‖v‖^2 ≤ g y v v) →
      ∀ᶠ k : ℕ in atTop,
      ∀ e : (Fin 4 → Fin (corrugationSubdivision k)) → _root_.OAI.Yau.Jets.Coord ≃L[ℝ] _root_.OAI.Yau.Jets.Coord,
      (∀ i, let y := corrugationCubeCenter o L (corrugationSubdivision k) i
        e i (Pi.single 0 1) = (corrugationOldSlope g S y)⁻¹ • metricGradient g S y ∧
        (∀ a b, g y (e i (Pi.single a 1)) (e i (Pi.single b 1)) = if a=b then 1 else 0)) →
      (1+γ)*(∫ x in Icc o (fun j ↦ o j+L), corrugationOldSlope g S x) ≤
        ∫ x in Icc o (fun j ↦ o j+L), corrugationOldSlope g
          (S+corrugationEnvelopePerturbation o L k g S corrugationFixedCutoff corrugationFixedAmplitude e) x := by
  obtain ⟨γ,hγ,hcell⟩ := corrugation_cell_integrated_gain hc hM
  refine ⟨γ,hγ,?_⟩
  intro o L hL g S U hU hDU hg hS hp hn hcmp
  have hev := hcell g S (Icc o (fun j ↦ o j+L)) U isCompact_Icc
    (convex_Icc o (fun j ↦ o j+L)) hU hDU hg hS hp hn hcmp L hL
  filter_upwards [hev] with k hk
  intro e he
  let n := corrugationSubdivision k
  let y := corrugationCubeCenter o L n
  let W := corrugationEnvelopePerturbation o L k g S corrugationFixedCutoff corrugationFixedAmplitude e
  obtain ⟨_,_,hχ,_,hsupp,_,_,_⟩ := corrugationFixedCutoff_spec
  have hW : ContDiff ℝ ∞ W := corrugationEnvelopePerturbation_smooth o L k g S _ _ e hχ
  have ho : IntegrableOn (corrugationOldSlope g S) (Icc o (fun j ↦ o j+L)) :=
    ((corrugationOldSlope_continuousOn g S hU hg hS hp).mono hDU).integrableOn_Icc
  have hf : IntegrableOn (corrugationOldSlope g (S+W)) (Icc o (fun j ↦ o j+L)) :=
    ((corrugationOldSlope_continuousOn g (S+W) hU hg (hS.add hW.contDiffOn) hp).mono hDU).integrableOn_Icc
  rw [corrugation_cube_integral_sum o hL (corrugationSubdivision_positive k) _ ho,
    corrugation_cube_integral_sum o hL (corrugationSubdivision_positive k) _ hf,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  have hi := hk (y i) (corrugationCubeCenter_mem o hL (corrugationSubdivision_positive k) i)
    (corrugationCube_closed_inside o hL (corrugationSubdivision_positive k) i) (e i) (he i).1 (he i).2
  apply hi.trans_eq
  apply setIntegral_congr_fun measurableSet_closedBall
  intro x hx
  have heq := corrugationGridSum_closed_cube_eventually o hL (corrugationSubdivision_positive k)
    corrugationFixedCutoff hsupp corrugationFixedAmplitude (corrugationFrequency k)
    (fun j ↦ corrugationOldSlope g S (y j)) e i x hx
  have heq' := Filter.EventuallyEq.add (Filter.EventuallyEq.rfl (f := S)) heq
  exact (congrArg (fun p : _root_.OAI.Yau.Jets.Coord ↦ Real.sqrt (g x p p))
    (congrArg (fun d : _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ ↦ ContinuousLinearMap.inverse (g x) d) heq'.fderiv_eq)).symm

end
end Yau.Geometry

end OAI
end

theorem solution : type_of% @OAI.Yau.Geometry.corrugation_grid_integrated_gain_oai := @OAI.Yau.Geometry.corrugation_grid_integrated_gain_oai
