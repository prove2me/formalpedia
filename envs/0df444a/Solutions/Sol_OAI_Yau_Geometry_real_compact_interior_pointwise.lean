-- Prove2me | solution 1 for OAI.Yau.Geometry.real_compact_interior_pointwise
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T00:29:14.759209+00:00
-- url     : https://prove2.me/submissions/dbbc4f24-570f-4083-a5a3-356d9ec2c518

import Mathlib
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Abs
import Mathlib.Analysis.Calculus.Deriv.Pi
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Pi
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.Calculus.TaylorIntegral
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.Normed.Lp.SmoothApprox
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.Finsupp.Weight
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.OfFn
import Mathlib.Data.Matrix.Basic
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.LinearAlgebra.Basis.SMul
import Mathlib.LinearAlgebra.Determinant
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.QuadraticForm.Basic
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousCompMeasurePreserving
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.ContDiff
import Mathlib.MeasureTheory.Integral.IntervalIntegral.DistLEIntegral
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.Algebra.Support
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Topology.Order.Compact
import Definitions.Def_OAIQ237Ny004

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_RealCompactMultiplierLemmas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Yau

open MeasureTheory Set

theorem real_L2_test_pairing {X : Type*} [MeasurableSpace X] {m : Measure X}
    (f : Lp ℝ 2 m) (g : X → ℝ) (hg : MemLp g 2 m) :
    Integrable (fun x ↦ f x*g x) m ∧
    inner ℝ f (hg.toLp g) = ∫ x, f x*g x ∂m := by
  have he : (fun x ↦ inner ℝ (f x) (hg.toLp g x)) =ᵐ[m] (fun x ↦ f x*g x) := by
    filter_upwards [hg.coeFn_toLp] with x hx
    rw [hx]
    change g x*f x = f x*g x
    ring
  exact ⟨(L2.integrable_inner f (hg.toLp g)).congr he,by rw [L2.inner_def,integral_congr_ae he]⟩

theorem real_toLp_inner {X : Type*} [MeasurableSpace X] {m : Measure X}
    (f g : X → ℝ) (hf : MemLp f 2 m) (hg : MemLp g 2 m) :
    inner ℝ (hf.toLp f) (hg.toLp g) = ∫ x, f x*g x ∂m := by
  rw [(real_L2_test_pairing _ g hg).2]
  apply integral_congr_ae
  filter_upwards [hf.coeFn_toLp] with x hx
  rw [hx]

end Yau

end

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_AnchoredCubeBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Analysis
open MeasureTheory Set Function
open scoped ENNReal ContDiff
noncomputable section
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] in
lemma inUnitCube_update {x : ι → ℝ} (hx : InUnitCube x)
    (i : ι) {t : ℝ} (ht : |t| ≤ 1) : InUnitCube (update x i t) := by
  intro j
  by_cases h : j = i
  · subst j; simpa using ht
  · simpa [update_of_ne h] using hx j

end
end Yau.Analysis

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_CoordinatePartialJets
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Analysis
open scoped ContDiff
noncomputable section
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma partialJet_smooth (f : (ι → ℝ) → ℝ) (hf : ContDiff ℝ ∞ f)
    (ds : List ι) : ContDiff ℝ ∞ (partialJet f ds) := by
  induction ds with
  | nil => exact hf
  | cons i ds ih =>
    exact (ih.fderiv_right (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).clm_apply contDiff_const

end
end Yau.Analysis

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_RealIntervalL2Embedding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open MeasureTheory Set
open scoped ContDiff
noncomputable section

lemma real_interval_square_variation (f : ℝ → ℝ) (hf : ContDiff ℝ ∞ f)
    (a b : ℝ) (ha : a ∈ Icc (-1:ℝ) 1) (hb : b ∈ Icc (-1:ℝ) 1) :
    |f b^2-f a^2| ≤ ∫ t in Icc (-1:ℝ) 1, (f t^2+(deriv f t)^2) := by
  have hcont : Continuous (fun t ↦ f t^2+(deriv f t)^2) :=
    (hf.continuous.pow 2).add ((hf.continuous_deriv (by simp)).pow 2)
  have hpos (t : ℝ) : 0 ≤ f t^2+(deriv f t)^2 := add_nonneg (sq_nonneg _) (sq_nonneg _)
  have hder (t : ℝ) : ‖deriv (fun s ↦ f s^2) t‖ ≤ f t^2+(deriv f t)^2 := by
    have he : deriv (fun s ↦ f s^2) t = 2*f t*deriv f t := by
      simpa only [Pi.pow_apply,Nat.cast_ofNat,show 2-1=1 from rfl,pow_one] using
        ((hf.differentiable (by simp) t).hasDerivAt.fun_pow 2).deriv
    rw [he,Real.norm_eq_abs]
    exact abs_le.mpr ⟨by nlinarith [sq_nonneg (f t+deriv f t)],
      by nlinarith [sq_nonneg (f t-deriv f t)]⟩
  have hordered (c d : ℝ) (hc : c ∈ Icc (-1:ℝ) 1) (hd : d ∈ Icc (-1:ℝ) 1)
      (hcd : c ≤ d) : |f d^2-f c^2| ≤ ∫ t in Icc (-1:ℝ) 1, (f t^2+(deriv f t)^2) := by
    have h := norm_sub_le_integral_of_norm_deriv_le_of_le hcd
      (hf.pow 2).continuous.continuousOn ((hf.pow 2).differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).differentiableOn
      (Filter.Eventually.of_forall (fun t _ ↦ hder t)) (hcont.intervalIntegrable c d)
    rw [intervalIntegral.integral_of_le hcd] at h
    have hm : (∫ t in Ioc c d, (f t^2+(deriv f t)^2)) ≤
        ∫ t in Icc (-1:ℝ) 1, (f t^2+(deriv f t)^2) := by
      apply setIntegral_mono_set (hcont.continuousOn.integrableOn_compact isCompact_Icc)
        (Filter.Eventually.of_forall hpos)
      exact Filter.Eventually.of_forall (fun t ht ↦ ⟨hc.1.trans ht.1.le,ht.2.trans hd.2⟩)
    have hh : |f d^2-f c^2| ≤ ∫ t in Ioc c d, (f t^2+(deriv f t)^2) := by
      simpa only [Real.norm_eq_abs] using h
    exact hh.trans hm
  rcases le_total a b with hab | hba
  · exact hordered a b ha hb hab
  · simpa only [abs_sub_comm] using hordered b a hb ha hba

theorem real_interval_l2_embedding (f : ℝ → ℝ) (hf : ContDiff ℝ ∞ f)
    (x : ℝ) (hx : x ∈ Icc (-1:ℝ) 1) :
    f x^2 ≤ 2*(∫ t in Icc (-1:ℝ) 1, (f t^2+(deriv f t)^2)) := by
  have hfi : IntegrableOn (fun t ↦ f t^2) (Icc (-1:ℝ) 1) :=
    (hf.continuous.pow 2).continuousOn.integrableOn_compact isCompact_Icc
  have hdi : IntegrableOn (fun t ↦ (deriv f t)^2) (Icc (-1:ℝ) 1) :=
    ((hf.continuous_deriv (by simp)).pow 2).continuousOn.integrableOn_compact isCompact_Icc
  obtain ⟨y,hy,hmin⟩ := isCompact_Icc.exists_isMinOn (show (Icc (-1:ℝ) 1).Nonempty from ⟨0,by norm_num⟩)
    (hf.continuous.pow 2).continuousOn
  have hm := setIntegral_mono_on
    (integrableOn_const (isCompact_Icc.measure_ne_top (μ := volume))) hfi measurableSet_Icc
    (fun t ht ↦ hmin ht)
  have hm' : 2*f y^2 ≤ ∫ t in Icc (-1:ℝ) 1, f t^2 := by
    norm_num at hm
    exact hm
  have hd : 0 ≤ ∫ t in Icc (-1:ℝ) 1, (deriv f t)^2 := integral_nonneg (fun t ↦ sq_nonneg _)
  have hv := (le_abs_self (f x^2-f y^2)).trans (real_interval_square_variation f hf y x hy hx)
  rw [integral_add hfi hdi] at hv ⊢
  nlinarith [sq_nonneg (f y)]

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_RealCubeL2Control
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Yau.Analysis MeasureTheory Set Function
open scoped ContDiff
noncomputable section

lemma real_coordinate_update_continuous (i : Fin 4) :
    Continuous (fun z : Yau.Jets.Coord × ℝ ↦ update z.1 i z.2) := by
  apply continuous_pi
  intro j
  by_cases hj : j=i
  · subst j; simpa using (continuous_snd : Continuous (fun z : Yau.Jets.Coord × ℝ ↦ z.2))
  · simpa only [update_of_ne hj,Function.comp_def] using (continuous_apply j).comp
      (continuous_fst : Continuous (fun z : Yau.Jets.Coord × ℝ ↦ z.1))

lemma realCubeL2Control_continuous (W : Yau.Jets.Coord → ℝ) (hW : ContDiff ℝ ∞ W)
    (is ds : List (Fin 4)) : Continuous (realCubeL2Control W is ds) := by
  induction is generalizing ds with
  | nil => exact ((partialJet_smooth W hW ds).pow 2).continuous
  | cons i is ih =>
    apply continuous_const.mul
    apply continuous_parametric_integral_of_continuous _ isCompact_Icc
    exact ((ih ds).comp (real_coordinate_update_continuous i)).add
      ((ih (i::ds)).comp (real_coordinate_update_continuous i))

theorem partialJet_sq_le_realCubeL2Control (W : Yau.Jets.Coord → ℝ) (hW : ContDiff ℝ ∞ W)
    (is ds : List (Fin 4)) (x : Yau.Jets.Coord) (hx : InUnitCube x) :
    (partialJet W ds x)^2 ≤ realCubeL2Control W is ds x := by
  induction is generalizing ds x with
  | nil => exact le_rfl
  | cons i is ih =>
    have hd (t : ℝ) : deriv (fun s ↦ partialJet W ds (update x i s)) t =
        partialJet W (i::ds) (update x i t) := by
      change deriv (partialJet W ds ∘ update x i) t = _
      rw [((partialJet_smooth W hW ds).differentiable (by simp) (update x i t)).hasFDerivAt.comp_hasDerivAt t
        (hasDerivAt_update x i t) |>.deriv]
      rfl
    have h := real_interval_l2_embedding (fun t ↦ partialJet W ds (update x i t))
      ((partialJet_smooth W hW ds).comp (contDiff_update ∞ x i)) (x i) (abs_le.mp (hx i))
    simp only [update_eq_self] at h
    simp_rw [hd] at h
    have hc (es : List (Fin 4)) : Continuous (fun t ↦ partialJet W es (update x i t)) :=
      (partialJet_smooth W hW es).continuous.comp (contDiff_update (𝕜 := ℝ) ∞ x i).continuous
    have hc' (es : List (Fin 4)) : Continuous (fun t ↦ realCubeL2Control W is es (update x i t)) :=
      (realCubeL2Control_continuous W hW is es).comp (contDiff_update (𝕜 := ℝ) ∞ x i).continuous
    have hm := setIntegral_mono_on (μ := volume)
      (((hc ds).pow 2).add ((hc (i::ds)).pow 2)).continuousOn.integrableOn_Icc
      ((hc' ds).add (hc' (i::ds))).continuousOn.integrableOn_Icc measurableSet_Icc
      (fun t ht ↦ add_le_add
        (ih ds _ (inUnitCube_update hx i (abs_le.mpr ht)))
        (ih (i::ds) _ (inUnitCube_update hx i (abs_le.mpr ht))))
    exact h.trans (mul_le_mul_of_nonneg_left hm (by norm_num))

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_RealTransportDerivatives
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau
open scoped ContDiff
noncomputable section
variable {n : ℕ}

lemma real_coordPartial_commute (u : Coord n → ℝ) (hu : ContDiff ℝ ∞ u)
    (x : Coord n) (i j : Fin n) :
    coordPartial (fun y ↦ coordPartial u y j) x i =
      coordPartial (fun y ↦ coordPartial u y i) x j := by
  have hd := (hu.fderiv_right (m := ∞) (by simp)).differentiable (by simp) x
  unfold coordPartial
  rw [fderiv_clm_apply hd (differentiableAt_const _),
    fderiv_clm_apply hd (differentiableAt_const _)]
  simp only [fderiv_fun_const,Pi.zero_apply,ContinuousLinearMap.comp_zero,
    ContinuousLinearMap.flip_apply,zero_add]
  exact hu.contDiffAt.isSymmSndFDerivAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) _ _

end
end Yau

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_RealFiniteJetSquare
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Yau.Analysis
open scoped ContDiff
noncomputable section

lemma realFiniteJetSquare_nonneg (W : Yau.Jets.Coord → ℝ) (n : ℕ) (x : Yau.Jets.Coord) :
    0 ≤ realFiniteJetSquare W n x :=
  Finset.sum_nonneg (fun _ _ ↦ Finset.sum_nonneg (fun _ _ ↦ sq_nonneg _))

lemma realFiniteJetSquare_smooth (W : Yau.Jets.Coord → ℝ) (hW : ContDiff ℝ ∞ W) (n : ℕ) :
    ContDiff ℝ ∞ (realFiniteJetSquare W n) :=
  ContDiff.sum (fun _ _ ↦ ContDiff.sum (fun w _ ↦ (partialJet_smooth W hW (List.ofFn w)).pow 2))

lemma partialJet_sq_le_realFiniteJetSquare (W : Yau.Jets.Coord → ℝ) (n : ℕ)
    (ds : List (Fin 4)) (hd : ds.length ≤ n) (x : Yau.Jets.Coord) :
    (partialJet W ds x)^2 ≤ realFiniteJetSquare W n x := by
  have h₁ : (partialJet W ds x)^2 ≤
      ∑ w : Fin ds.length → Fin 4, (partialJet W (List.ofFn w) x)^2 := by
    simpa only [List.ofFn_get] using
      (Finset.single_le_sum (fun w _ ↦ sq_nonneg (partialJet W (List.ofFn w) x))
        (Finset.mem_univ ds.get))
  exact h₁.trans (Finset.single_le_sum (s := Finset.range (n+1)) (a := ds.length)
    (f := fun r ↦ ∑ w : Fin r → Fin 4, (partialJet W (List.ofFn w) x)^2)
    (fun r _ ↦ Finset.sum_nonneg (fun w _ ↦ sq_nonneg (partialJet W (List.ofFn w) x)))
    (Finset.mem_range.mpr (by omega)))

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_RealCubeAverage
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Yau.Analysis MeasureTheory Set Function
open scoped ContDiff
noncomputable section

lemma realCubeAverage_continuous (F : Yau.Jets.Coord → ℝ) (hF : Continuous F)
    (is : List (Fin 4)) : Continuous (realCubeAverage F is) := by
  induction is with
  | nil => exact hF
  | cons i is ih =>
    apply continuous_parametric_integral_of_continuous _ isCompact_Icc
    exact ih.comp (real_coordinate_update_continuous i)

theorem realCubeL2Control_le_average (W : Yau.Jets.Coord → ℝ) (hW : ContDiff ℝ ∞ W)
    (n : ℕ) (is ds : List (Fin 4)) (hd : ds.length+is.length ≤ n) (x : Yau.Jets.Coord) :
    realCubeL2Control W is ds x ≤
      4^is.length * realCubeAverage (realFiniteJetSquare W n) is x := by
  induction is generalizing ds x with
  | nil => simpa [realCubeL2Control,realCubeAverage] using
      partialJet_sq_le_realFiniteJetSquare W n ds (by simpa using hd) x
  | cons i is ih =>
    have hi (es : List (Fin 4)) : IntegrableOn
        (fun t ↦ realCubeL2Control W is es (update x i t)) (Icc (-1:ℝ) 1) :=
      ((realCubeL2Control_continuous W hW is es).comp
        (contDiff_update (𝕜 := ℝ) ∞ x i).continuous).continuousOn.integrableOn_Icc
    have ha : IntegrableOn
        (fun t ↦ realCubeAverage (realFiniteJetSquare W n) is (update x i t))
        (Icc (-1:ℝ) 1) :=
      ((realCubeAverage_continuous _ (realFiniteJetSquare_smooth W hW n).continuous is).comp
        (contDiff_update (𝕜 := ℝ) ∞ x i).continuous).continuousOn.integrableOn_Icc
    have hm := setIntegral_mono_on (μ := volume) ((hi ds).add (hi (i::ds)))
      ((ha.const_mul (4^is.length)).add (ha.const_mul (4^is.length))) measurableSet_Icc
      (fun t _ ↦ add_le_add (ih ds (by simpa using (show ds.length+is.length ≤ n by
          simp only [List.length_cons] at hd; omega)) _)
        (ih (i::ds) (by simp only [List.length_cons] at hd ⊢; omega) _))
    simp only [Pi.add_apply,integral_add (ha.const_mul _) (ha.const_mul _),
      integral_const_mul] at hm
    change 2 * _ ≤ _
    calc
      _ ≤ 2*(4^is.length * (∫ t in Icc (-1:ℝ) 1,
          realCubeAverage (realFiniteJetSquare W n) is (update x i t)) +
        4^is.length * (∫ t in Icc (-1:ℝ) 1,
          realCubeAverage (realFiniteJetSquare W n) is (update x i t))) :=
        mul_le_mul_of_nonneg_left hm (by norm_num)
      _ = _ := by simp only [List.length_cons,realCubeAverage,pow_succ] <;> ring

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_RealFinCubeFubini
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open MeasureTheory Set Function
noncomputable section

lemma realFinCube_volume (n : ℕ) :
    (volume : Measure (Fin n → ℝ)).restrict (realFinCube n) =
      Measure.pi (fun _ : Fin n ↦ volume.restrict (Icc (-1:ℝ) 1)) :=
  Measure.restrict_pi_pi _ _

lemma realFinCube_integrable (n : ℕ) (F : (Fin n → ℝ) → ℝ) (hF : Continuous F) :
    IntegrableOn F (realFinCube n) :=
  hF.continuousOn.integrableOn_compact (isCompact_univ_pi (fun _ ↦ isCompact_Icc))

theorem realFinCube_integral_succ (n : ℕ) (F : (Fin (n+1) → ℝ) → ℝ)
    (hF : Continuous F) :
    (∫ z in realFinCube (n+1), F z) =
      ∫ t in Icc (-1:ℝ) 1, ∫ z in realFinCube n, F (Fin.cons t z) := by
  have hi := realFinCube_integrable (n+1) F hF
  rw [IntegrableOn,realFinCube_volume] at hi
  let μ := fun _ : Fin (n+1) ↦ volume.restrict (Icc (-1:ℝ) 1)
  have hm := (measurePreserving_piFinSuccAbove μ 0).symm
  have hh := hm.integrable_comp_of_integrable hi
  have he := hm.integral_comp' F
  simp only [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
    Equiv.coe_fn_mk,Fin.insertNth_zero] at hh he
  simp only [realFinCube_volume]
  exact he.symm.trans (integral_prod _ hh)

lemma realFinCube_integral_zero (F : (Fin 0 → ℝ) → ℝ) :
    (∫ z in realFinCube 0, F z) = F Fin.elim0 := by
  have hs : realFinCube 0 = univ := by ext z; simp [realFinCube]
  rw [hs,Measure.restrict_univ,Measure.volume_pi_eq_dirac Fin.elim0,integral_dirac]

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_RealL2DifferenceQuotient
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau
open MeasureTheory
noncomputable section

theorem realL2Translate_ae {n : ℕ} (v : Fin n → ℝ) (f : RealEuclideanL2 n) :
    (realL2Translate v f : (Fin n → ℝ) → ℝ) =ᵐ[volume] (fun x ↦ f (x+v)) :=
  Lp.coeFn_compMeasurePreserving f (measurePreserving_add_right volume v)

end
end Yau

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_RealInteriorWeakProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau
open MeasureTheory Set
open scoped ContDiff
noncomputable section

theorem real_interior_weak_product {n : ℕ} {K : Set (Coord n)} (hK : IsCompact K)
    (u g a : Coord n → ℝ) (hu : MemLp u 2 (volume.restrict K))
    (hg : MemLp g 2 (volume.restrict K)) (ha : ContDiff ℝ ∞ a) (i : Fin n)
    (hweak : ∀ psi : Coord n → ℝ, ContDiff ℝ ∞ psi → HasCompactSupport psi → tsupport psi ⊆ K →
      (∫ x in K, u x*coordPartial psi x i)=-(∫ x in K, g x*psi x)) :
    MemLp (fun x ↦ a x*u x) 2 (volume.restrict K) ∧
    MemLp (fun x ↦ a x*g x+coordPartial a x i*u x) 2 (volume.restrict K) ∧
    ∀ psi : Coord n → ℝ, ContDiff ℝ ∞ psi → HasCompactSupport psi → tsupport psi ⊆ K →
      IntegrableOn (fun x ↦ (a x*u x)*coordPartial psi x i) K ∧
      IntegrableOn (fun x ↦ (a x*g x+coordPartial a x i*u x)*psi x) K ∧
      (∫ x in K, (a x*u x)*coordPartial psi x i) =
        -(∫ x in K, (a x*g x+coordPartial a x i*u x)*psi x) := by
  obtain ⟨_,_,hba⟩ := real_compact_multiplier_bound hK a ha.continuous
  obtain ⟨_,_,hbd⟩ := real_compact_multiplier_bound hK (fun x ↦ coordPartial a x i)
    (real_coordPartial_smooth a ha i).continuous
  have hau := (hba u hu).1
  have hag := (hba g hg).1
  have hdu := (hbd u hu).1
  refine ⟨hau,hag.add hdu,fun psi hp hc hs ↦ ?_⟩
  have hpsi := real_continuous_memLp_compact hK psi hp.continuous
  have hdpsi := real_continuous_memLp_compact hK _ (real_coordPartial_smooth psi hp i).continuous
  have hi1 : IntegrableOn (fun x ↦ (a x*u x)*coordPartial psi x i) K := hau.integrable_mul hdpsi
  have hi2 : IntegrableOn (fun x ↦ (a x*g x)*psi x) K := hag.integrable_mul hpsi
  have hi3 : IntegrableOn (fun x ↦ (coordPartial a x i*u x)*psi x) K := hdu.integrable_mul hpsi
  have heq := hweak (fun x ↦ a x*psi x) (ha.mul hp) hc.mul_left (tsupport_mul_subset_right.trans hs)
  have heleft : (fun x ↦ u x*coordPartial (fun y ↦ a y*psi y) x i) =
      fun x ↦ (coordPartial a x i*u x)*psi x+(a x*u x)*coordPartial psi x i := by
    funext x
    rw [real_coordPartial_mul a psi ha hp]
    ring
  have heright : (fun x ↦ g x*(a x*psi x)) = fun x ↦ (a x*g x)*psi x := by funext x; ring
  rw [heleft,heright,integral_add hi3 hi1] at heq
  have heprod : (fun x ↦ (a x*g x+coordPartial a x i*u x)*psi x) =
      fun x ↦ (a x*g x)*psi x+(coordPartial a x i*u x)*psi x := by funext x; ring
  refine ⟨hi1,(hag.add hdu).integrable_mul hpsi,?_⟩
  rw [heprod,integral_add hi2 hi3]
  linarith only [heq]

end
end Yau

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_RealLocalWeakCutoff
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau
open MeasureTheory Set
open scoped ContDiff
noncomputable section

theorem real_local_weak_cutoff {n : ℕ} {K : Set (Coord n)} (hK : IsCompact K)
    (u g eta : Coord n → ℝ) (hu : MemLp u 2 (volume.restrict K))
    (hg : MemLp g 2 (volume.restrict K)) (he : ContDiff ℝ ∞ eta)
    (hs : tsupport eta ⊆ K) (i : Fin n)
    (hweak : ∀ phi : Coord n → ℝ, ContDiff ℝ ∞ phi → HasCompactSupport phi → tsupport phi ⊆ K →
      (∫ x in K, u x*coordPartial phi x i)=-(∫ x in K, g x*phi x)) :
    MemLp (fun x ↦ eta x*u x) 2 volume ∧
    MemLp (fun x ↦ eta x*g x+coordPartial eta x i*u x) 2 volume ∧
    ∀ phi : Coord n → ℝ, ContDiff ℝ ∞ phi → HasCompactSupport phi →
      Integrable (fun x ↦ eta x*u x*coordPartial phi x i) ∧
      Integrable (fun x ↦ (eta x*g x+coordPartial eta x i*u x)*phi x) ∧
      (∫ x, eta x*u x*coordPartial phi x i) =
        -(∫ x, (eta x*g x+coordPartial eta x i*u x)*phi x) := by
  have hpart : tsupport (fun x ↦ coordPartial eta x i) ⊆ K :=
    (tsupport_fderiv_apply_subset ℝ (Pi.single i 1)).trans hs
  have hval := real_compact_localL2_product hK eta u he.continuous hs hu
  have h1 := real_compact_localL2_product hK eta g he.continuous hs hg
  have h2 := real_compact_localL2_product hK (fun x ↦ coordPartial eta x i) u
    (real_coordPartial_smooth eta he i).continuous hpart hu
  refine ⟨hval,h1.add h2,fun phi hp hc ↦ ?_⟩
  have hphi := real_compact_continuous_memLp phi hp.continuous hc
  have hi1 : Integrable (fun x ↦ eta x*g x*phi x) := h1.integrable_mul hphi
  have hi2 : Integrable (fun x ↦ coordPartial eta x i*u x*phi x) := h2.integrable_mul hphi
  have hi3 : Integrable (fun x ↦ eta x*u x*coordPartial phi x i) := hval.integrable_mul
    (real_compact_continuous_memLp _ (real_coordPartial_smooth phi hp i).continuous
      (hc.fderiv_apply ℝ (Pi.single i 1)))
  have hw := hweak (fun x ↦ eta x*phi x) (he.mul hp) hc.mul_left
    (tsupport_mul_subset_left.trans hs)
  have he1 : (fun x ↦ g x*(eta x*phi x)) = fun x ↦ eta x*g x*phi x := by funext x; ring
  have he2 : (fun x ↦ u x*coordPartial (fun y ↦ eta y*phi y) x i) =
      fun x ↦ coordPartial eta x i*u x*phi x+eta x*u x*coordPartial phi x i := by
    funext x
    rw [real_coordPartial_mul eta phi he hp]
    ring
  rw [he1,he2,integral_add hi2.integrableOn hi3.integrableOn] at hw
  have hz (x : Coord n) (hx : x ∉ K) : eta x=0 :=
    image_eq_zero_of_notMem_tsupport (fun h ↦ hx (hs h))
  have hdz (x : Coord n) (hx : x ∉ K) : coordPartial eta x i=0 :=
    image_eq_zero_of_notMem_tsupport (f := fun y ↦ coordPartial eta y i) (fun h ↦ hx (hpart h))
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx ↦ by rw [hdz x hx,zero_mul,zero_mul]),
    setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx ↦ by rw [hz x hx,zero_mul,zero_mul]),
    setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx ↦ by rw [hz x hx,zero_mul,zero_mul])] at hw
  have heG : (fun x ↦ (eta x*g x+coordPartial eta x i*u x)*phi x) =
      fun x ↦ eta x*g x*phi x+coordPartial eta x i*u x*phi x := by funext x; ring
  refine ⟨hi3,by rw [heG]; exact hi1.add hi2,?_⟩
  rw [heG,integral_add hi1 hi2]
  linarith only [hw]

end
end Yau

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_RealL2PairingRepresentatives
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau
open MeasureTheory
noncomputable section

theorem real_L2_inner_reps {n : ℕ} (u v : RealEuclideanL2 n)
    (a b : (Fin n → ℝ) → ℝ)
    (ha : (u : (Fin n → ℝ) → ℝ) =ᵐ[volume] a)
    (hb : (v : (Fin n → ℝ) → ℝ) =ᵐ[volume] b) :
    Integrable (fun x ↦ a x*b x) ∧ inner ℝ u v = ∫ x, a x*b x := by
  have hm : MemLp a 2 volume := (memLp_congr_ae ha).mp (Lp.memLp u)
  have hn : MemLp b 2 volume := (memLp_congr_ae hb).mp (Lp.memLp v)
  refine ⟨hm.integrable_mul hn,?_⟩
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [ha,hb] with x h1 h2
  rw [h1,h2]
  change b x*a x=a x*b x
  ring

end
end Yau

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Coefficients_RealFintypeCoefficientBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau
open MeasureTheory Set
noncomputable section

theorem real_compact_fintype_coefficient_L2_bound {n : ℕ} {I : Type*} [Fintype I] {K : Set (Coord n)}
    (hK : IsCompact K) (A : Coord n → I → ℝ) (hA : ∀ j, Continuous (fun x ↦ A x j)) :
    ∃ C > 0, ∀ U : I → Coord n → ℝ, (∀ j, MemLp (U j) 2 (volume.restrict K)) →
      MemLp (fun x ↦ ∑ j, A x j*U j x) 2 (volume.restrict K) ∧
      (∫ x in K, (∑ j, A x j*U j x)^2) ≤ C*(∑ j, ∫ x in K, (U j x)^2) := by
  obtain ⟨B,hB,hb⟩ := (hK.image (continuous_pi hA)).isBounded.exists_pos_norm_le
  refine ⟨((Fintype.card I:ℝ)+1)*B^2,by positivity,fun U hU ↦ ?_⟩
  have hprod (j : I) : MemLp (fun x ↦ A x j*U j x) 2 (volume.restrict K) := by
    obtain ⟨_,_,hbound⟩ := real_compact_multiplier_bound hK (fun x ↦ A x j) (hA j)
    exact (hbound (U j) (hU j)).1
  have hsum : MemLp (fun x ↦ ∑ j, A x j*U j x) 2 (volume.restrict K) :=
    memLp_finsetSum Finset.univ (fun j _ ↦ hprod j)
  refine ⟨hsum,?_⟩
  have hisum := integrable_finsetSum Finset.univ (fun j _ ↦ (hU j).integrable_sq)
  rw [← integral_finsetSum Finset.univ (fun j _ ↦ (hU j).integrable_sq),← integral_const_mul]
  apply setIntegral_mono_on hsum.integrable_sq (hisum.const_mul _) hK.measurableSet
  intro x hx
  have hcoef (j : I) : (A x j)^2 ≤ B^2 := by
    have ht := (norm_le_pi_norm (A x) j).trans (hb _ ⟨x,hx,rfl⟩)
    rw [Real.norm_eq_abs] at ht
    nlinarith [sq_abs (A x j),abs_nonneg (A x j)]
  have hcoefsum := Finset.sum_le_sum (s := Finset.univ) (fun j _ ↦ hcoef j)
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul] at hcoefsum
  have hCS := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun j ↦ A x j) (fun j ↦ U j x)
  have hn : 0 ≤ ∑ j, (U j x)^2 := Finset.sum_nonneg (fun _ _ ↦ sq_nonneg _)
  have hmul := mul_le_mul_of_nonneg_right hcoefsum hn
  have hextra := mul_nonneg (sq_nonneg B) hn
  nlinarith only [hCS,hmul,hextra]

theorem real_compact_fintype_coefficient_common_bound {n : ℕ} {I : Type*} [Fintype I]
    {K : Set (Coord n)} (hK : IsCompact K) (A : Coord n → I → ℝ)
    (hA : ∀ j, Continuous (fun x ↦ A x j)) :
    ∃ C > 0, ∀ U : I → Coord n → ℝ, (∀ j, MemLp (U j) 2 (volume.restrict K)) →
      ∀ E : ℝ, 0 ≤ E → (∀ j, (∫ x in K, (U j x)^2) ≤ E) →
        MemLp (fun x ↦ ∑ j, A x j*U j x) 2 (volume.restrict K) ∧
        (∫ x in K, (∑ j, A x j*U j x)^2) ≤ C*E := by
  obtain ⟨C,hC,hb⟩ := real_compact_fintype_coefficient_L2_bound hK A hA
  refine ⟨C*((Fintype.card I:ℝ)+1),by positivity,fun U hU E hE hbound ↦ ?_⟩
  have h := hb U hU
  refine ⟨h.1,h.2.trans ?_⟩
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun j _ ↦ hbound j)
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul] at hs
  have hs' : (∑ j, ∫ x in K, (U j x)^2) ≤ ((Fintype.card I:ℝ)+1)*E := by nlinarith only [hs,hE]
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hs' hC.le

end
end Yau

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_PartialJetGerm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Analysis
open Filter
open scoped Topology
noncomputable section

theorem partialJet_eventuallyEq (f g : (Fin 4 → ℝ) → ℝ) (x : Fin 4 → ℝ)
    (h : f =ᶠ[𝓝 x] g) (ds : List (Fin 4)) :
    partialJet f ds =ᶠ[𝓝 x] partialJet g ds := by
  induction ds with
  | nil => exact h
  | cons i ds ih =>
    filter_upwards [ih.fderiv (𝕜 := ℝ)] with y hy
    exact congrArg (fun A ↦ A (Pi.single i 1)) hy

theorem partialJet_germ_eq (f g : (Fin 4 → ℝ) → ℝ) (x : Fin 4 → ℝ)
    (h : f =ᶠ[𝓝 x] g) (ds : List (Fin 4)) :
    partialJet f ds x = partialJet g ds x :=
  (partialJet_eventuallyEq f g x h ds).eq_of_nhds

end
end Yau.Analysis

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_RealL2TranslationContinuity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau
open MeasureTheory Filter
open scoped Topology
noncomputable section

theorem realL2Translate_continuous {n : ℕ} (u : RealEuclideanL2 n) :
    Continuous (fun v : (Fin n → ℝ) ↦ realL2Translate v u) := by
  let shift : (Fin n → ℝ) → C((Fin n → ℝ),(Fin n → ℝ)) := fun v ↦ ⟨fun x ↦ x+v,continuous_id.add continuous_const⟩
  have hc : Continuous shift := ContinuousMap.continuous_of_continuous_uncurry shift
    (continuous_snd.add continuous_fst)
  exact continuous_const.compMeasurePreservingLp hc
    (fun v ↦ measurePreserving_add_right volume v) (by norm_num : (2:ENNReal) ≠ ⊤)

theorem realL2Translate_zero {n : ℕ} (u : RealEuclideanL2 n) : realL2Translate 0 u=u := by
  apply Lp.ext
  filter_upwards [realL2Translate_ae (0 : (Fin n → ℝ)) u] with x hx
  simpa only [add_zero] using hx

end
end Yau

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_RealCompactTestDerivative
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau
open MeasureTheory Set
open scoped ContDiff
noncomputable section

theorem real_compact_test_derivative {n : ℕ} (u phi : Coord n → ℝ)
    (hu : ContDiff ℝ ∞ u) (hp : ContDiff ℝ ∞ phi) (hc : HasCompactSupport phi)
    (i : Fin n) (K : Set (Coord n)) (hK : tsupport phi ⊆ K) :
    Integrable (fun x ↦ coordPartial u x i*phi x) ∧
    Integrable (fun x ↦ u x*coordPartial phi x i) ∧
    (∫ x in K, coordPartial u x i*phi x) = -(∫ x in K, u x*coordPartial phi x i) := by
  have h1 : Integrable (fun x ↦ coordPartial u x i*phi x) :=
    ((real_coordPartial_smooth u hu i).continuous.mul hp.continuous).integrable_of_hasCompactSupport hc.mul_left
  have h2 : Integrable (fun x ↦ u x*coordPartial phi x i) :=
    (hu.continuous.mul (real_coordPartial_smooth phi hp i).continuous).integrable_of_hasCompactSupport
      (hc.fderiv_apply ℝ (Pi.single i 1)).mul_left
  have h3 : Integrable (fun x ↦ phi x*u x) :=
    (hp.continuous.mul hu.continuous).integrable_of_hasCompactSupport hc.mul_right
  have h := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    (μ := volume) (f := phi) (g := u) (v := Pi.single i 1)
    (by simpa only [coordPartial,mul_comm] using h2)
    (by simpa only [coordPartial,mul_comm] using h1) h3
    (fun x _ ↦ hp.differentiable (by simp) x) (fun x _ ↦ hu.differentiable (by simp) x)
  have hz1 : ∀ x, x ∉ K → coordPartial u x i*phi x = 0 := by
    intro x hx
    rw [image_eq_zero_of_notMem_tsupport (fun h ↦ hx (hK h)),mul_zero]
  have hz2 : ∀ x, x ∉ K → u x*coordPartial phi x i = 0 := by
    intro x hx
    unfold coordPartial
    rw [fderiv_of_notMem_tsupport ℝ (fun h ↦ hx (hK h))]
    simp
  refine ⟨h1,h2,?_⟩
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero hz1,
    setIntegral_eq_integral_of_forall_compl_eq_zero hz2]
  simpa only [coordPartial,mul_comm] using h

end
end Yau

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_RealWeakConvolution
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau
open MeasureTheory Set ContinuousLinearMap
open scoped ContDiff Convolution
noncomputable section

theorem real_convolution_coordPartial {n : ℕ} (u k : Coord n → ℝ)
    (hu : LocallyIntegrable u volume) (hk : ContDiff ℝ ∞ k)
    (hc : HasCompactSupport k) (x : Coord n) (i : Fin n) :
    coordPartial (u ⋆ k) x i = ∫ y, u y * coordPartial k (x-y) i := by
  unfold coordPartial
  rw [(hc.hasFDerivAt_convolution_right (lsmul ℝ ℝ) hu (hk.of_le (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)) x).fderiv]
  exact convolution_precompR_apply (lsmul ℝ ℝ) hu
    (hc.fderiv ℝ) (hk.continuous_fderiv (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)) x (Pi.single i 1)

theorem real_weak_convolution_derivative {n : ℕ} (u g k : Coord n → ℝ)
    (hu : LocallyIntegrable u volume) (hk : ContDiff ℝ ∞ k)
    (hc : HasCompactSupport k) (i : Fin n)
    (hw : ∀ psi : Coord n → ℝ, ContDiff ℝ ∞ psi → HasCompactSupport psi →
      (∫ y, u y * coordPartial psi y i) = -(∫ y, g y * psi y)) :
    (fun x ↦ coordPartial (u ⋆ k) x i) = g ⋆ k := by
  funext x
  let psi : Coord n → ℝ := fun y ↦ k (x-y)
  have hp : ContDiff ℝ ∞ psi := hk.comp (contDiff_const.sub contDiff_id)
  have hpc : HasCompactSupport psi :=
    hc.comp_homeomorph ((Homeomorph.neg (Coord n)).trans (Homeomorph.addLeft x))
  have hd (y : Coord n) : coordPartial psi y i = -coordPartial k (x-y) i := by
    unfold coordPartial
    have ht := (hk.differentiable (by simp) (x-y)).hasFDerivAt.comp y
      ((hasFDerivAt_const x y).sub (hasFDerivAt_id y))
    change HasFDerivAt psi _ y at ht
    rw [ht.fderiv]
    simp
  have he := hw psi hp hpc
  simp only [hd, mul_neg, integral_neg] at he
  rw [real_convolution_coordPartial u k hu hk hc, convolution_def]
  exact neg_injective he

theorem real_compact_convolution_smooth {n : ℕ} (u k : Coord n → ℝ)
    (hu : LocallyIntegrable u volume) (huc : HasCompactSupport u)
    (hk : ContDiff ℝ ∞ k) (hkc : HasCompactSupport k) :
    ContDiff ℝ ∞ (u ⋆ k) ∧ HasCompactSupport (u ⋆ k) :=
  ⟨hkc.contDiff_convolution_right (lsmul ℝ ℝ) hu hk,
    huc.convolution (lsmul ℝ ℝ) hkc⟩

end
end Yau

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_RealL2Convolution
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau
open MeasureTheory Set Filter ContinuousLinearMap
open scoped ContDiff Convolution Topology
noncomputable section

theorem realL2Convolution_integrable {n : ℕ} (k : Coord n → ℝ)
    (hk : Continuous k) (hc : HasCompactSupport k) (U : RealEuclideanL2 n) :
    Integrable (fun t ↦ k t • realL2Translate (-t) U) :=
  (hk.smul ((realL2Translate_continuous U).comp continuous_neg)).integrable_of_hasCompactSupport
    (hc.smul_right)

theorem real_convolution_test_pairing {n : ℕ} (u k phi : Coord n → ℝ)
    (hu : Integrable u) (hk : Integrable k) (hp : Continuous phi)
    (hc : HasCompactSupport phi) :
    (∫ x, (u ⋆ k) x * phi x) = ∫ t, k t * ∫ x, u (x-t)*phi x := by
  obtain ⟨B,_,hb⟩ := (hc.isCompact_range hp).isBounded.exists_pos_norm_le
  have hi : Integrable (fun z : Coord n × Coord n ↦ (k z.2 * u (z.1-z.2))*phi z.1)
      (volume.prod volume) :=
    (hk.convolution_integrand (lsmul ℝ ℝ) hu).mul_bdd
      (hp.comp continuous_fst).aestronglyMeasurable
      (Eventually.of_forall (fun z ↦ hb _ (mem_range_self z.1)))
  calc
    _ = ∫ x, ∫ t, (k t*u (x-t))*phi x := by
      apply integral_congr_ae
      apply Eventually.of_forall
      intro x
      dsimp only
      rw [convolution_lsmul_swap, ← integral_mul_const]
      apply integral_congr_ae
      exact Eventually.of_forall (fun t ↦ by ring)
    _ = ∫ t, ∫ x, (k t*u (x-t))*phi x := integral_integral_swap hi
    _ = _ := by
      apply integral_congr_ae
      apply Eventually.of_forall
      intro t
      dsimp only
      rw [← integral_const_mul]
      apply integral_congr_ae
      exact Eventually.of_forall (fun x ↦ by ring)

theorem realL2Convolution_smooth_pairing {n : ℕ} (u k phi : Coord n → ℝ)
    (hu : Integrable u) (hum : MemLp u 2 volume) (hk : Continuous k)
    (hkc : HasCompactSupport k) (hp : ContDiff ℝ ∞ phi) (hpc : HasCompactSupport phi) :
    inner ℝ (realL2Convolution k (hum.toLp u))
      ((real_compact_continuous_memLp phi hp.continuous hpc).toLp phi) =
      ∫ x, (u ⋆ k) x * phi x := by
  let P := (real_compact_continuous_memLp phi hp.continuous hpc).toLp phi
  rw [real_convolution_test_pairing u k phi hu
    (hk.integrable_of_hasCompactSupport hkc) hp.continuous hpc]
  change inner ℝ (∫ t, k t • realL2Translate (-t) (hum.toLp u)) P = _
  rw [real_inner_comm, ← integral_inner (realL2Convolution_integrable k hk hkc _)]
  apply integral_congr_ae
  apply Eventually.of_forall
  intro t
  dsimp only
  rw [inner_smul_right, real_inner_comm]
  have ht : (realL2Translate (-t) (hum.toLp u) : Coord n → ℝ) =ᵐ[volume]
      (fun x ↦ u (x-t)) := by
    have he := (measurePreserving_add_right (G := Coord n) volume (-t)).quasiMeasurePreserving.ae_eq_comp
      hum.coeFn_toLp
    simpa only [sub_eq_add_neg, Function.comp_def] using (realL2Translate_ae (-t) (hum.toLp u)).trans he
  rw [(real_L2_inner_reps _ P _ phi ht
    (real_compact_continuous_memLp phi hp.continuous hpc).coeFn_toLp).2]

theorem real_L2_eq_of_smooth_pairings {n : ℕ} (U V : RealEuclideanL2 n)
    (he : ∀ phi : Coord n → ℝ, ∀ hp : ContDiff ℝ ∞ phi, ∀ hc : HasCompactSupport phi,
      inner ℝ U ((real_compact_continuous_memLp phi hp.continuous hc).toLp phi) =
      inner ℝ V ((real_compact_continuous_memLp phi hp.continuous hc).toLp phi)) : U=V := by
  have hclosed : IsClosed {W : RealEuclideanL2 n | inner ℝ U W=inner ℝ V W} :=
    isClosed_eq (continuous_const.inner continuous_id) (continuous_const.inner continuous_id)
  have hsub : {W : RealEuclideanL2 n | ∃ phi : Coord n → ℝ,
      (W : Coord n → ℝ) =ᵐ[volume] phi ∧ HasCompactSupport phi ∧ ContDiff ℝ ∞ phi} ⊆
      {W : RealEuclideanL2 n | inner ℝ U W=inner ℝ V W} := by
    rintro W ⟨phi,hw,hc,hp⟩
    have hm := real_compact_continuous_memLp phi hp.continuous hc
    have hW : W=hm.toLp phi := Lp.ext (hw.trans hm.coeFn_toLp.symm)
    change inner ℝ U W=inner ℝ V W
    simpa only [hW] using he phi hp hc
  apply ext_inner_right ℝ
  intro W
  apply closure_minimal hsub hclosed
  exact (Lp.dense_hasCompactSupport_contDiff (μ := (volume : Measure (Coord n))) (F := ℝ)
    (by norm_num : (2:ENNReal) ≠ ⊤)) W

theorem realL2Convolution_eq_toLp {n : ℕ} (u k : Coord n → ℝ)
    (hu : Integrable u) (hum : MemLp u 2 volume) (hk : ContDiff ℝ ∞ k)
    (hkc : HasCompactSupport k) (hm : MemLp (u ⋆ k) 2 volume) :
    realL2Convolution k (hum.toLp u) = hm.toLp (u ⋆ k) := by
  apply real_L2_eq_of_smooth_pairings
  intro phi hp hc
  rw [realL2Convolution_smooth_pairing u k phi hu hum hk.continuous hkc hp hc,
    real_toLp_inner]

theorem realL2Convolution_normed_tendsto {n : ℕ}
    (b : ℕ → ContDiffBump (0 : Coord n))
    (hb : Tendsto (fun m ↦ (b m).rOut) atTop (𝓝 0)) (U : RealEuclideanL2 n) :
    Tendsto (fun m ↦ realL2Convolution ((b m).normed volume) U) atTop (𝓝 U) := by
  have ht := ContDiffBump.convolution_tendsto_right_of_continuous
    (μ := (volume : Measure (Coord n))) hb (realL2Translate_continuous U) (0 : Coord n)
  simpa only [convolution_def, lsmul_apply, zero_sub, realL2Translate_zero,
    realL2Convolution] using ht

end
end Yau

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_RealMollifierSupport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau
open MeasureTheory Set Filter Metric ContinuousLinearMap
open scoped ContDiff Convolution Topology Pointwise
noncomputable section

theorem realMollifierBump_radius_tendsto {n : ℕ} (r : ℝ) (hr : 0 < r) :
    Tendsto (fun m ↦ (realMollifierBump (n := n) r hr m).rOut) atTop (𝓝 0) := by
  simpa only [realMollifierBump, mul_zero] using
    tendsto_one_div_add_atTop_nhds_zero_nat.const_mul r

end
end Yau

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_RealCompactH1Approximation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau
open MeasureTheory Set Filter
open scoped ContDiff Convolution Topology
noncomputable section

theorem real_compact_memLp_integrable {n : ℕ} (u : Coord n → ℝ)
    (hu : MemLp u 2 volume) (hc : HasCompactSupport u) : Integrable u := by
  let : IsFiniteMeasure (volume.restrict (tsupport u)) :=
    isFiniteMeasure_restrict.mpr hc.measure_ne_top
  apply (integrableOn_iff_integrable_of_support_subset (subset_tsupport u)).mp
  exact (hu.restrict _).integrable (by norm_num)

theorem real_compact_convolution_L2_tendsto {n : ℕ} (u : Coord n → ℝ)
    (hu : MemLp u 2 volume) (hc : HasCompactSupport u)
    (b : ℕ → ContDiffBump (0 : Coord n))
    (hb : Tendsto (fun m ↦ (b m).rOut) atTop (𝓝 0)) :
    Tendsto (fun m ↦ realSmoothCompactL2 (u ⋆ (b m).normed volume)
      ((b m).hasCompactSupport_normed.contDiff_convolution_right
        (ContinuousLinearMap.lsmul ℝ ℝ) (hu.locallyIntegrable (by norm_num)) (b m).contDiff_normed)
      (hc.convolution (ContinuousLinearMap.lsmul ℝ ℝ) (b m).hasCompactSupport_normed))
      atTop (𝓝 (hu.toLp u)) := by
  have ht := realL2Convolution_normed_tendsto b hb (hu.toLp u)
  convert ht using 1
  all_goals try with_reducible_and_instances rfl
  funext m
  exact (realL2Convolution_eq_toLp u _ (real_compact_memLp_integrable u hu hc) hu
    (b m).contDiff_normed (b m).hasCompactSupport_normed _).symm

end
end Yau

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_RealSupportedWeakGlobal
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau
open MeasureTheory Set Filter
open scoped ContDiff Topology
noncomputable section

theorem real_supported_local_weak_global {Q K : Set Jets.Coord}
    (hQ : IsCompact Q) (hK : IsCompact K) (hKQ : K ⊆ interior Q)
    (u g : Jets.Coord → ℝ) (hu : MemLp u 2 (volume.restrict Q))
    (hg : MemLp g 2 (volume.restrict Q)) (hsu : tsupport u ⊆ K) (hsg : tsupport g ⊆ K)
    (i : Fin 4)
    (hw : ∀ psi, ContDiff ℝ ∞ psi → HasCompactSupport psi → tsupport psi ⊆ Q →
      (∫ x in Q, u x*coordPartial psi x i)=-(∫ x in Q, g x*psi x)) :
    MemLp u 2 volume ∧ MemLp g 2 volume ∧
    ∀ psi, ContDiff ℝ ∞ psi → HasCompactSupport psi →
      Integrable (fun x ↦ u x*coordPartial psi x i) ∧ Integrable (fun x ↦ g x*psi x) ∧
      (∫ x, u x*coordPartial psi x i)=-(∫ x, g x*psi x) := by
  obtain ⟨eta,he,hc,hs,hb,h1⟩ := Geometry.compact_smooth_cutoff hK isOpen_interior hKQ
  have h := real_local_weak_cutoff hQ u g eta hu hg he (hs.trans interior_subset) i hw
  have hm (v : Jets.Coord → ℝ) (hv : tsupport v ⊆ K) : (fun x ↦ eta x*v x)=v := by
    funext x
    by_cases hx : x ∈ K
    · rw [(h1 x hx).self_of_nhds,one_mul]
    · rw [image_eq_zero_of_notMem_tsupport (fun ht ↦ hx (hv ht)),mul_zero]
  have hd : (fun x ↦ coordPartial eta x i*u x)=(fun _ ↦ (0:ℝ)) := by
    funext x
    by_cases hx : x ∈ K
    · have hd := (h1 x hx).fderiv_eq (𝕜 := ℝ)
      simp [coordPartial,hd]
    · rw [image_eq_zero_of_notMem_tsupport (fun ht ↦ hx (hsu ht)),mul_zero]
  have hcomb : (fun x ↦ eta x*g x+coordPartial eta x i*u x)=g := by
    funext x
    rw [congrFun (hm g hsg) x,congrFun hd x,add_zero]
  rw [hm u hsu,hcomb] at h
  simp_rw [show ∀ x, eta x*u x=u x from fun x ↦ congrFun (hm u hsu) x,
    show ∀ x, eta x*g x+coordPartial eta x i*u x=g x from fun x ↦ congrFun hcomb x] at h
  exact h

end
end Yau

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_RealWeakJetPairings
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau
open MeasureTheory Set Yau.Analysis
open scoped ContDiff
noncomputable section

lemma partialJet_append_word {n : ℕ} (f : Coord n → ℝ) (ds es : List (Fin n)) :
    partialJet f (ds++es) = partialJet (partialJet f es) ds := by
  induction ds with
  | nil => rfl
  | cons i ds ih => simp only [List.cons_append,partialJet,ih]

lemma partialJet_tsupport_subset {n : ℕ} (f : Coord n → ℝ) (ds : List (Fin n)) :
    tsupport (partialJet f ds) ⊆ tsupport f := by
  induction ds with
  | nil => exact Subset.rfl
  | cons i ds ih =>
    exact (tsupport_fderiv_apply_subset ℝ (Pi.single i 1)).trans ih

lemma partialJet_compactSupport {n : ℕ} (f : Coord n → ℝ)
    (hf : HasCompactSupport f) (ds : List (Fin n)) :
    HasCompactSupport (partialJet f ds) :=
  hf.of_isClosed_subset (isClosed_tsupport _) (partialJet_tsupport_subset f ds)

lemma partialJet_perm_word {n : ℕ} (f : Coord n → ℝ) (hf : ContDiff ℝ ∞ f)
    {ds es : List (Fin n)} (h : ds.Perm es) : partialJet f ds = partialJet f es := by
  induction h with
  | nil => rfl
  | cons i h ih => simp only [partialJet,ih]
  | swap i j ds =>
    funext x
    exact real_coordPartial_commute (partialJet f ds) (partialJet_smooth f hf ds) x j i
  | trans h1 h2 ih1 ih2 => exact ih1.trans ih2

theorem real_weak_jet_test_reversal {n : ℕ} {Q : Set (Coord n)}
    (U : List (Fin n) → Coord n → ℝ) (M : ℕ)
    (hweak : ∀ es, es.length < M → ∀ i psi,
      ContDiff ℝ ∞ psi → HasCompactSupport psi → tsupport psi ⊆ Q →
      (∫ x in Q, U es x*coordPartial psi x i)=-(∫ x in Q, U (i::es) x*psi x))
    (ds : List (Fin n)) (hlen : ds.length ≤ M)
    (psi : Coord n → ℝ) (hp : ContDiff ℝ ∞ psi)
    (hc : HasCompactSupport psi) (hs : tsupport psi ⊆ Q) :
    (∫ x in Q, U ds x*psi x) = (-1:ℝ)^ds.length *
      (∫ x in Q, U [] x*partialJet psi ds.reverse x) := by
  induction ds generalizing psi with
  | nil => simp [partialJet]
  | cons i ds ih =>
    have hlt : ds.length < M := by simp only [List.length_cons] at hlen; omega
    have hw := hweak ds hlt i psi hp hc hs
    have hi := ih (by omega) (fun x ↦ coordPartial psi x i)
      (real_coordPartial_smooth psi hp i) (hc.fderiv_apply ℝ (Pi.single i 1))
      ((tsupport_fderiv_apply_subset ℝ (Pi.single i 1)).trans hs)
    have hr : partialJet psi (i::ds).reverse =
        partialJet (fun x ↦ coordPartial psi x i) ds.reverse := by
      rw [List.reverse_cons,partialJet_append_word]
      rfl
    rw [hr,List.length_cons,pow_succ]
    rw [hi] at hw
    linarith only [hw]

theorem real_weak_jet_pairing_perm {n : ℕ} {Q : Set (Coord n)}
    (U : List (Fin n) → Coord n → ℝ) (M : ℕ)
    (hweak : ∀ es, es.length < M → ∀ i psi,
      ContDiff ℝ ∞ psi → HasCompactSupport psi → tsupport psi ⊆ Q →
      (∫ x in Q, U es x*coordPartial psi x i)=-(∫ x in Q, U (i::es) x*psi x))
    {ds es : List (Fin n)} (hlen : ds.length ≤ M) (hperm : ds.Perm es)
    (psi : Coord n → ℝ) (hp : ContDiff ℝ ∞ psi)
    (hc : HasCompactSupport psi) (hs : tsupport psi ⊆ Q) :
    (∫ x in Q, U ds x*psi x)=(∫ x in Q, U es x*psi x) := by
  rw [real_weak_jet_test_reversal U M hweak ds hlen psi hp hc hs,
    real_weak_jet_test_reversal U M hweak es (by simpa only [← hperm.length_eq] using hlen) psi hp hc hs,
    hperm.length_eq,partialJet_perm_word psi hp
      ((List.reverse_perm ds).trans (hperm.trans (List.reverse_perm es).symm))]

end
end Yau

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_RealInteriorWeakAddLemmas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Yau

open MeasureTheory Set
open scoped ContDiff

theorem real_interior_weak_add {n : ℕ} {K : Set (Coord n)} (hK : IsCompact K)
    (u v g h : Coord n → ℝ)
    (hu : MemLp u 2 (volume.restrict K)) (hv : MemLp v 2 (volume.restrict K))
    (hg : MemLp g 2 (volume.restrict K)) (hh : MemLp h 2 (volume.restrict K))
    (i : Fin n)
    (hw : ∀ psi, ContDiff ℝ ∞ psi → HasCompactSupport psi → tsupport psi ⊆ K →
      (∫ x in K, u x*coordPartial psi x i)=-(∫ x in K, g x*psi x))
    (hvweak : ∀ psi, ContDiff ℝ ∞ psi → HasCompactSupport psi → tsupport psi ⊆ K →
      (∫ x in K, v x*coordPartial psi x i)=-(∫ x in K, h x*psi x)) :
    MemLp (fun x ↦ u x+v x) 2 (volume.restrict K) ∧
    MemLp (fun x ↦ g x+h x) 2 (volume.restrict K) ∧
    ∀ psi, ContDiff ℝ ∞ psi → HasCompactSupport psi → tsupport psi ⊆ K →
      IntegrableOn (fun x ↦ (u x+v x)*coordPartial psi x i) K ∧
      IntegrableOn (fun x ↦ (g x+h x)*psi x) K ∧
      (∫ x in K, (u x+v x)*coordPartial psi x i)=-(∫ x in K, (g x+h x)*psi x) := by
  refine ⟨hu.add hv,hg.add hh,fun psi hp hc hs ↦ ?_⟩
  have ht := real_continuous_memLp_compact hK psi hp.continuous
  have hdt := real_continuous_memLp_compact hK _ (real_coordPartial_smooth psi hp i).continuous
  refine ⟨(hu.add hv).integrable_mul hdt,(hg.add hh).integrable_mul ht,?_⟩
  have hiu : IntegrableOn (fun x ↦ u x*coordPartial psi x i) K := hu.integrable_mul hdt
  have hiv : IntegrableOn (fun x ↦ v x*coordPartial psi x i) K := hv.integrable_mul hdt
  have hig : IntegrableOn (fun x ↦ g x*psi x) K := hg.integrable_mul ht
  have hih : IntegrableOn (fun x ↦ h x*psi x) K := hh.integrable_mul ht
  simp_rw [add_mul]
  rw [integral_add hiu hiv,
    integral_add hig hih,hw psi hp hc hs,hvweak psi hp hc hs]
  ring

end Yau

end

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_RealJetProductExpansion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Yau.Analysis
open scoped ContDiff
noncomputable section

lemma realJetErrorTerms_orders (extra ds : List (Fin 4)) (he : extra.length ≤ 1)
    (t : List (Fin 4) × List (Fin 4)) (ht : t ∈ realJetErrorTerms extra ds) :
    t.1.length ≤ ds.length ∧ t.2.length ≤ ds.length := by
  induction ds generalizing t with
  | nil => simp [realJetErrorTerms] at ht
  | cons l ds ih =>
    simp only [realJetErrorTerms,List.mem_append,List.mem_map,List.mem_singleton] at ht
    rcases ht with (⟨s,hs,rfl⟩ | ⟨s,hs,rfl⟩) | rfl
    · have h := ih s hs; simp only [List.length_cons]; omega
    · have h := ih s hs; simp only [List.length_cons]; omega
    · simp only [List.length_cons,List.length_nil,List.length_append]; omega

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_RealWeakJetProducts
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau
open MeasureTheory Set Yau.Analysis
open scoped ContDiff
noncomputable section

theorem real_weak_jet_product_derivative {Q : Set Jets.Coord} (hQ : IsCompact Q)
    (A : Jets.Coord → ℝ) (hA : ContDiff ℝ ∞ A)
    (U : List (Fin 4) → Jets.Coord → ℝ)
    (ts : List (List (Fin 4) × List (Fin 4))) (i : Fin 4)
    (hU : ∀ t ∈ ts, MemLp (U t.2) 2 (volume.restrict Q))
    (hD : ∀ t ∈ ts, MemLp (U (i::t.2)) 2 (volume.restrict Q))
    (hweak : ∀ t ∈ ts, ∀ psi : Jets.Coord → ℝ,
      ContDiff ℝ ∞ psi → HasCompactSupport psi → tsupport psi ⊆ Q →
      (∫ x in Q, U t.2 x*coordPartial psi x i)=-(∫ x in Q, U (i::t.2) x*psi x)) :
    let V := realWeakJetProductSum A U ts
    let D := realWeakJetProductSum A U
      (ts.map (fun t ↦ (i::t.1,t.2)) ++ ts.map (fun t ↦ (t.1,i::t.2)))
    MemLp V 2 (volume.restrict Q) ∧ MemLp D 2 (volume.restrict Q) ∧
    ∀ psi : Jets.Coord → ℝ, ContDiff ℝ ∞ psi → HasCompactSupport psi → tsupport psi ⊆ Q →
      IntegrableOn (fun x ↦ V x*coordPartial psi x i) Q ∧
      IntegrableOn (fun x ↦ D x*psi x) Q ∧
      (∫ x in Q, V x*coordPartial psi x i)=-(∫ x in Q, D x*psi x) := by
  dsimp only
  induction ts with
  | nil =>
    simp [realWeakJetProductSum]
    exact MemLp.zero
  | cons t ts ih =>
    have hp := real_interior_weak_product hQ (U t.2) (U (i::t.2)) (partialJet A t.1)
      (hU t (by simp)) (hD t (by simp)) (partialJet_smooth A hA t.1) i (hweak t (by simp))
    have ht := ih (fun s hs ↦ hU s (List.mem_cons_of_mem _ hs))
      (fun s hs ↦ hD s (List.mem_cons_of_mem _ hs))
      (fun s hs ↦ hweak s (List.mem_cons_of_mem _ hs))
    have hadd := real_interior_weak_add hQ _ _ _ _ hp.1 ht.1 hp.2.1 ht.2.1 i
      (fun psi hp0 hc hs ↦ (hp.2.2 psi hp0 hc hs).2.2)
      (fun psi hp0 hc hs ↦ (ht.2.2 psi hp0 hc hs).2.2)
    have hfun : (fun x ↦ partialJet A t.1 x*U (i::t.2) x+
        coordPartial (partialJet A t.1) x i*U t.2 x+
        realWeakJetProductSum A U (ts.map (fun s ↦ (i::s.1,s.2))++ts.map (fun s ↦ (s.1,i::s.2))) x) =
        realWeakJetProductSum A U ((t::ts).map (fun s ↦ (i::s.1,s.2))++(t::ts).map (fun s ↦ (s.1,i::s.2))) := by
      funext x
      simp only [realWeakJetProductSum,List.map_append,List.map_cons,List.sum_cons,List.sum_append,partialJet,coordPartial]
      ring
    rw [hfun] at hadd
    simp_rw [show ∀ x, _ = _ from fun x ↦ congrFun hfun x] at hadd
    exact hadd

end
end Yau

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_RealWeakJetLeibniz
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau
open MeasureTheory Set Yau.Analysis Yau.Geometry
open scoped ContDiff
noncomputable section

lemma real_weak_jet_product_memLp {Q : Set Jets.Coord} (hQ : IsCompact Q)
    (A : Jets.Coord → ℝ) (hA : ContDiff ℝ ∞ A)
    (U : List (Fin 4) → Jets.Coord → ℝ)
    (ts : List (List (Fin 4) × List (Fin 4)))
    (hU : ∀ t ∈ ts, MemLp (U t.2) 2 (volume.restrict Q)) :
    MemLp (realWeakJetProductSum A U ts) 2 (volume.restrict Q) := by
  induction ts with
  | nil => exact MemLp.zero
  | cons t ts ih =>
    obtain ⟨_,_,hb⟩ := real_compact_multiplier_bound hQ _ (partialJet_smooth A hA t.1).continuous
    exact ((hb _ (hU t (by simp))).1).add (ih (fun s hs ↦ hU s (List.mem_cons_of_mem _ hs)))

lemma real_weak_jet_expansion_memLp {Q : Set Jets.Coord} (hQ : IsCompact Q)
    (A : Jets.Coord → ℝ) (hA : ContDiff ℝ ∞ A)
    (U : List (Fin 4) → Jets.Coord → ℝ) (N : ℕ)
    (hU : ∀ es, es.length ≤ N+1 → MemLp (U es) 2 (volume.restrict Q))
    (extra ds : List (Fin 4)) (he : extra.length ≤ 1) (hd : ds.length ≤ N) :
    MemLp (realWeakJetExpansion A U extra ds) 2 (volume.restrict Q) := by
  obtain ⟨_,_,hb⟩ := real_compact_multiplier_bound hQ A hA.continuous
  exact ((hb _ (hU _ (by simp only [List.length_append]; omega))).1).add
    (real_weak_jet_product_memLp hQ A hA U _ (fun t ht ↦ hU _
      (((realJetErrorTerms_orders extra ds he t ht).2.trans hd).trans (Nat.le_succ N))))

theorem real_weak_jet_expansion_derivative {Q : Set Jets.Coord} (hQ : IsCompact Q)
    (A : Jets.Coord → ℝ) (hA : ContDiff ℝ ∞ A)
    (U : List (Fin 4) → Jets.Coord → ℝ) (N : ℕ)
    (hU : ∀ es, es.length ≤ N+1 → MemLp (U es) 2 (volume.restrict Q))
    (hweak : ∀ es, es.length ≤ N → ∀ i psi,
      ContDiff ℝ ∞ psi → HasCompactSupport psi → tsupport psi ⊆ Q →
      (∫ x in Q, U es x*coordPartial psi x i)=-(∫ x in Q, U (i::es) x*psi x))
    (extra ds : List (Fin 4)) (he : extra.length ≤ 1) (hd : ds.length < N) (i : Fin 4) :
    MemLp (realWeakJetExpansion A U extra ds) 2 (volume.restrict Q) ∧
    MemLp (realWeakJetExpansion A U extra (i::ds)) 2 (volume.restrict Q) ∧
    ∀ psi : Jets.Coord → ℝ, ContDiff ℝ ∞ psi → HasCompactSupport psi → tsupport psi ⊆ Q →
      IntegrableOn (fun x ↦ realWeakJetExpansion A U extra ds x*coordPartial psi x i) Q ∧
      IntegrableOn (fun x ↦ realWeakJetExpansion A U extra (i::ds) x*psi x) Q ∧
      (∫ x in Q, realWeakJetExpansion A U extra ds x*coordPartial psi x i) =
        -(∫ x in Q, realWeakJetExpansion A U extra (i::ds) x*psi x) := by
  have hord : (extra++ds).length ≤ N := by simp only [List.length_append]; omega
  have hnew : (extra++i::ds).length ≤ N+1 := by simp only [List.length_append,List.length_cons]; omega
  have hcanonical : ∀ psi : Jets.Coord → ℝ,
      ContDiff ℝ ∞ psi → HasCompactSupport psi → tsupport psi ⊆ Q →
      (∫ x in Q, U (extra++ds) x*coordPartial psi x i) =
        -(∫ x in Q, U (extra++i::ds) x*psi x) := by
    intro psi hp hc hs
    rw [hweak _ hord i psi hp hc hs]
    congr 1
    exact real_weak_jet_pairing_perm U (N+1) (fun es hh ↦ hweak es (by omega))
      (by simp only [List.length_cons]; omega) List.perm_middle.symm psi hp hc hs
  have hm := real_interior_weak_product hQ (U (extra++ds)) (U (extra++i::ds)) A
    (hU _ (hord.trans (Nat.le_succ N))) (hU _ hnew) hA i hcanonical
  have ht := real_weak_jet_product_derivative hQ A hA U (realJetErrorTerms extra ds) i
    (fun t ht ↦ hU _ (by have h := (realJetErrorTerms_orders extra ds he t ht).2; omega))
    (fun t ht ↦ hU _ (by
      have h := (realJetErrorTerms_orders extra ds he t ht).2
      simp only [List.length_cons]; omega))
    (fun t ht ↦ hweak _ (by have h := (realJetErrorTerms_orders extra ds he t ht).2; omega) i)
  have ha := real_interior_weak_add hQ _ _ _ _ hm.1 ht.1 hm.2.1 ht.2.1 i
    (fun psi hp hc hs ↦ (hm.2.2 psi hp hc hs).2.2)
    (fun psi hp hc hs ↦ (ht.2.2 psi hp hc hs).2.2)
  have heq : (fun x ↦ A x*U (extra++i::ds) x+coordPartial A x i*U (extra++ds) x+
      realWeakJetProductSum A U ((realJetErrorTerms extra ds).map (fun t ↦ (i::t.1,t.2))++
        (realJetErrorTerms extra ds).map (fun t ↦ (t.1,i::t.2))) x) =
      realWeakJetExpansion A U extra (i::ds) := by
    funext x
    simp only [realWeakJetExpansion,realJetErrorTerms,realWeakJetProductSum,List.map_append,
      List.sum_append,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,partialJet,coordPartial]
    ring
  rw [heq] at ha
  simp_rw [show ∀ x, _ = _ from fun x ↦ congrFun heq x] at ha
  exact ha

end
end Yau

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_RealCutoffWeakJets
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau
open MeasureTheory Set Yau.Analysis Yau.Geometry
open scoped ContDiff
noncomputable section

lemma realWeakJetProductSum_support (A : Jets.Coord → ℝ)
    (U : List (Fin 4) → Jets.Coord → ℝ) (ts : List (List (Fin 4) × List (Fin 4))) :
    tsupport (realWeakJetProductSum A U ts) ⊆ tsupport A := by
  induction ts with
  | nil =>
    change tsupport (fun _ : Jets.Coord ↦ (0:ℝ)) ⊆ tsupport A
    simp
  | cons t ts ih =>
    exact (tsupport_add _ _).trans (union_subset
      (tsupport_mul_subset_left.trans (partialJet_tsupport_subset A t.1)) ih)

lemma realWeakJetExpansion_support (A : Jets.Coord → ℝ)
    (U : List (Fin 4) → Jets.Coord → ℝ) (extra ds : List (Fin 4)) :
    tsupport (realWeakJetExpansion A U extra ds) ⊆ tsupport A :=
  (tsupport_add _ _).trans (union_subset tsupport_mul_subset_left (realWeakJetProductSum_support A U _))

theorem real_cutoff_finite_weak_jet {Q : Set Jets.Coord} (hQ : IsCompact Q)
    (eta : Jets.Coord → ℝ) (he : ContDiff ℝ ∞ eta) (hc : HasCompactSupport eta)
    (hs : tsupport eta ⊆ interior Q) (U : List (Fin 4) → Jets.Coord → ℝ) (N : ℕ)
    (hU : ∀ es, es.length ≤ N+1 → MemLp (U es) 2 (volume.restrict Q))
    (hw : ∀ es, es.length ≤ N → ∀ i psi,
      ContDiff ℝ ∞ psi → HasCompactSupport psi → tsupport psi ⊆ Q →
      (∫ x in Q, U es x*coordPartial psi x i)=-(∫ x in Q, U (i::es) x*psi x)) :
    let V := realWeakJetExpansion eta U []
    (∀ ds, ds.length ≤ N → MemLp (V ds) 2 volume ∧ tsupport (V ds) ⊆ tsupport eta) ∧
    ∀ ds, ds.length < N → ∀ i psi,
      ContDiff ℝ ∞ psi → HasCompactSupport psi →
      Integrable (fun x ↦ V ds x*coordPartial psi x i) ∧ Integrable (fun x ↦ V (i::ds) x*psi x) ∧
      (∫ x, V ds x*coordPartial psi x i)=-(∫ x, V (i::ds) x*psi x) := by
  have hv (ds : List (Fin 4)) (hd : ds.length ≤ N) :
      MemLp (realWeakJetExpansion eta U [] ds) 2 volume := by
    have hl := real_weak_jet_expansion_memLp hQ eta he U N hU [] ds (by simp) hd
    have hg := (memLp_indicator_iff_restrict hQ.measurableSet).mpr hl
    have hid : Q.indicator (realWeakJetExpansion eta U [] ds)=realWeakJetExpansion eta U [] ds := by
      apply indicator_eq_self.mpr
      exact subset_tsupport _ |>.trans ((realWeakJetExpansion_support eta U [] ds).trans (hs.trans interior_subset))
    rwa [hid] at hg
  refine ⟨fun ds hd ↦ ⟨hv ds hd,realWeakJetExpansion_support eta U [] ds⟩,?_⟩
  intro ds hd i
  have hl := real_weak_jet_expansion_derivative hQ eta he U N hU hw [] ds (by simp) hd i
  exact (real_supported_local_weak_global hQ hc hs _ _ hl.1 hl.2.1
    (realWeakJetExpansion_support eta U [] ds) (realWeakJetExpansion_support eta U [] (i::ds)) i
    (fun psi hp hc hs ↦ (hl.2.2 psi hp hc hs).2.2)).2.2

end
end Yau

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_RealFinitePositiveBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau

theorem real_finite_positive_majorant {ι : Type*} [Fintype ι] (C : ι → ℝ) :
    ∃ B > 0, ∀ i, C i ≤ B := by
  classical
  refine ⟨(∑ i, |C i|)+1,by linarith [Finset.sum_nonneg (s := Finset.univ) (fun i _ ↦ abs_nonneg (C i))],?_⟩
  intro i
  have hs := Finset.single_le_sum (f := fun j ↦ |C j|) (fun j _ ↦ abs_nonneg (C j)) (Finset.mem_univ i)
  linarith [le_abs_self (C i)]

end Yau

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_RealFiniteWordBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau
noncomputable section

theorem real_finite_word_positive_majorant (n N : ℕ) (C : List (Fin n) → ℝ) :
    ∃ B > 0, ∀ ds, ds.length ≤ N → C ds ≤ B := by
  obtain ⟨B,hB,hb⟩ := real_finite_positive_majorant
    (fun e : Σ r : Fin (N+1), Fin r.val → Fin n ↦ C (List.ofFn e.2))
  refine ⟨B,hB,fun ds hd ↦ ?_⟩
  simpa only [List.ofFn_get] using hb ⟨⟨ds.length,by omega⟩,ds.get⟩

end
end Yau

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_RealWeakJetProductBound
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau
open MeasureTheory Set Yau.Analysis
open scoped ContDiff
noncomputable section

theorem real_weak_jet_product_bound {Q : Set Jets.Coord} (hQ : IsCompact Q)
    (A : Jets.Coord → ℝ) (hA : ContDiff ℝ ∞ A)
    (ts : List (List (Fin 4) × List (Fin 4))) :
    ∃ C > 0, ∀ U : List (Fin 4) → Jets.Coord → ℝ,
      (∀ t ∈ ts, MemLp (U t.2) 2 (volume.restrict Q)) →
      ∀ E : ℝ, 0 ≤ E → (∀ t ∈ ts, (∫ x in Q, (U t.2 x)^2) ≤ E) →
      MemLp (realWeakJetProductSum A U ts) 2 (volume.restrict Q) ∧
      (∫ x in Q, (realWeakJetProductSum A U ts x)^2) ≤ C*E := by
  obtain ⟨C,hC,hb⟩ := real_compact_fintype_coefficient_common_bound hQ
    (fun x (a : Fin ts.length) ↦ partialJet A (ts.get a).1 x)
    (fun a ↦ (partialJet_smooth A hA (ts.get a).1).continuous)
  refine ⟨C,hC,fun U hU E hE hUE ↦ ?_⟩
  have h := hb (fun a ↦ U (ts.get a).2) (fun a ↦ hU _ (List.get_mem ..))
    E hE (fun a ↦ hUE _ (List.get_mem ..))
  have heq : (fun x ↦ ∑ a : Fin ts.length, partialJet A (ts.get a).1 x*U (ts.get a).2 x) =
      realWeakJetProductSum A U ts := by
    funext x
    dsimp [realWeakJetProductSum]
    rw [← List.sum_ofFn]
    congr 1
    exact List.ofFn_getElem_eq_map ts (fun t ↦ partialJet A t.1 x*U t.2 x)
  rw [heq] at h
  simp_rw [show ∀ x, _ = _ from fun x ↦ congrFun heq x] at h
  exact h

end
end Yau

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_RealCutoffWeakJetBounds
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau
open MeasureTheory Set Yau.Analysis Yau.Geometry
open scoped ContDiff
noncomputable section

theorem real_cutoff_weak_jet_square_bound {Q : Set Jets.Coord} (hQ : IsCompact Q)
    (eta : Jets.Coord → ℝ) (he : ContDiff ℝ ∞ eta)
    (hs : tsupport eta ⊆ Q) (N : ℕ) :
    ∃ C > 0, ∀ U : List (Fin 4) → Jets.Coord → ℝ,
      (∀ es, es.length ≤ N → MemLp (U es) 2 (volume.restrict Q)) →
      ∀ E : ℝ, 0 ≤ E → (∀ es, es.length ≤ N → (∫ x in Q, (U es x)^2) ≤ E) →
      ∀ ds, ds.length ≤ N →
        (∫ x, (realWeakJetExpansion eta U [] ds x)^2) ≤ C*E := by
  have hex (ds : List (Fin 4)) :=
    real_weak_jet_product_bound hQ eta he (([],ds)::realJetErrorTerms [] ds)
  choose C hC hb using hex
  obtain ⟨B,hB,hmajor⟩ := real_finite_word_positive_majorant 4 N C
  refine ⟨B,hB,fun U hU E hE hUE ds hd ↦ ?_⟩
  have hord (t : List (Fin 4) × List (Fin 4))
      (ht : t ∈ ([],ds)::realJetErrorTerms [] ds) : t.2.length ≤ N := by
    rcases List.mem_cons.mp ht with rfl | ht
    · exact hd
    · exact ((realJetErrorTerms_orders [] ds (by simp) t ht).2).trans hd
  have h := hb ds U (fun t ht ↦ hU _ (hord t ht)) E hE (fun t ht ↦ hUE _ (hord t ht))
  have hid : realWeakJetProductSum eta U (([],ds)::realJetErrorTerms [] ds)=
      realWeakJetExpansion eta U [] ds := by
    funext x
    simp only [realWeakJetProductSum,List.map_cons,List.sum_cons,partialJet,
      realWeakJetExpansion,List.nil_append]
  rw [hid] at h
  have hz : ∀ x, x ∉ Q → (realWeakJetExpansion eta U [] ds x)^2=0 := by
    intro x hx
    rw [image_eq_zero_of_notMem_tsupport (fun hh ↦ hx
      (hs (realWeakJetExpansion_support eta U [] ds hh))),zero_pow (by decide)]
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hz]
  exact h.2.trans (mul_le_mul_of_nonneg_right (hmajor ds hd) hE)

end
end Yau

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_RealCubeL2EmbeddingLemmas
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Yau.Geometry

open Yau.Analysis MeasureTheory Set Function Metric
open scoped ContDiff

lemma realFinCube_four_eq_closedBall : realFinCube 4 = closedBall (0 : Yau.Jets.Coord) 1 := by
  rw [closedBall_pi _ (by norm_num : (0:ℝ) ≤ 1)]
  simp [realFinCube,Real.closedBall_eq_Icc]

theorem realFinCube_integral_four (F : Yau.Jets.Coord → ℝ) (hF : Continuous F) :
    (∫ z in realFinCube 4, F z) =
      ∫ a in Icc (-1:ℝ) 1, ∫ b in Icc (-1:ℝ) 1,
        ∫ c in Icc (-1:ℝ) 1, ∫ d in Icc (-1:ℝ) 1, F ![a,b,c,d] := by
  rw [realFinCube_integral_succ 3 F hF]
  apply integral_congr_ae
  filter_upwards [] with a
  have ha : Continuous (fun z : Fin 3 → ℝ ↦ F (Fin.cons a z)) :=
    hF.comp (continuous_const.finCons continuous_id)
  rw [realFinCube_integral_succ 2 _ ha]
  apply integral_congr_ae
  filter_upwards [] with b
  have hb : Continuous (fun z : Fin 2 → ℝ ↦ F (Fin.cons a (Fin.cons b z))) :=
    ha.comp (continuous_const.finCons continuous_id)
  rw [realFinCube_integral_succ 1 _ hb]
  apply integral_congr_ae
  filter_upwards [] with c
  have hc : Continuous (fun z : Fin 1 → ℝ ↦ F (Fin.cons a (Fin.cons b (Fin.cons c z)))) :=
    hb.comp (continuous_const.finCons continuous_id)
  rw [realFinCube_integral_succ 0 _ hc]
  apply integral_congr_ae
  filter_upwards [] with d
  rw [realFinCube_integral_zero]
  rfl

theorem realCubeAverage_all (F : Yau.Jets.Coord → ℝ) (hF : Continuous F)
    (x : Yau.Jets.Coord) :
    realCubeAverage F [0,1,2,3] x = ∫ z in closedBall (0 : Yau.Jets.Coord) 1, F z := by
  rw [← realFinCube_four_eq_closedBall,realFinCube_integral_four F hF]
  simp only [realCubeAverage]
  apply integral_congr_ae
  filter_upwards [] with a
  apply integral_congr_ae
  filter_upwards [] with b
  apply integral_congr_ae
  filter_upwards [] with c
  apply integral_congr_ae
  filter_upwards [] with d
  congr 1
  ext i
  fin_cases i <;> simp

theorem real_cube_l2_embedding (W : Yau.Jets.Coord → ℝ) (hW : ContDiff ℝ ∞ W)
    (ds : List (Fin 4)) (x : Yau.Jets.Coord) (hx : InUnitCube x) :
    (partialJet W ds x)^2 ≤ 256 * (∫ z in closedBall (0 : Yau.Jets.Coord) 1,
      realFiniteJetSquare W (ds.length+4) z) := by
  have h := (partialJet_sq_le_realCubeL2Control W hW [0,1,2,3] ds x hx).trans
    (realCubeL2Control_le_average W hW (ds.length+4) [0,1,2,3] ds (by simp) x)
  rw [realCubeAverage_all _ (realFiniteJetSquare_smooth W hW _).continuous] at h
  norm_num at h ⊢
  exact h

open MeasureTheory Set Function

end Yau.Geometry

end

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_RealTranslatedJetEmbedding
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Yau.Analysis MeasureTheory Set Function Metric
open scoped ContDiff
noncomputable section

lemma partialJet_translate (W : Yau.Jets.Coord → ℝ) (a : Yau.Jets.Coord)
    (ds : List (Fin 4)) (x : Yau.Jets.Coord) :
    partialJet (fun z ↦ W (a+z)) ds x = partialJet W ds (a+x) := by
  induction ds generalizing x with
  | nil => rfl
  | cons i ds ih =>
    have he : partialJet (fun z ↦ W (a+z)) ds = fun z ↦ partialJet W ds (a+z) := funext ih
    change fderiv ℝ (partialJet (fun z ↦ W (a+z)) ds) x _ = _
    rw [he,fderiv_comp_add_left]
    rfl

lemma realFiniteJetSquare_translate (W : Yau.Jets.Coord → ℝ) (a : Yau.Jets.Coord)
    (n : ℕ) (x : Yau.Jets.Coord) :
    realFiniteJetSquare (fun z ↦ W (a+z)) n x = realFiniteJetSquare W n (a+x) := by
  simp only [realFiniteJetSquare,partialJet_translate]

lemma real_integral_ball_translate (F : Yau.Jets.Coord → ℝ) (a : Yau.Jets.Coord) (r : ℝ) :
    (∫ z in closedBall (0 : Yau.Jets.Coord) r, F (a+z)) = ∫ z in closedBall a r, F z := by
  have hs : (fun z : Yau.Jets.Coord ↦ a+z) ⁻¹' closedBall a r = closedBall 0 r := by
    ext z
    simp only [mem_preimage,mem_closedBall,dist_self_add_left,dist_zero_right]
  rw [← hs]
  exact (measurePreserving_add_left volume a).setIntegral_preimage_emb
    (MeasurableEquiv.addLeft a).measurableEmbedding F _

theorem real_point_jet_l2_embedding (W : Yau.Jets.Coord → ℝ) (hW : ContDiff ℝ ∞ W)
    (ds : List (Fin 4)) (x : Yau.Jets.Coord) :
    (partialJet W ds x)^2 ≤ 256 * (∫ z in closedBall x 1,
      realFiniteJetSquare W (ds.length+4) z) := by
  have h := real_cube_l2_embedding (fun z ↦ W (x+z))
    (hW.comp (contDiff_const.add contDiff_id)) ds 0 (by intro i; simp)
  simp only [partialJet_translate,add_zero,realFiniteJetSquare_translate,
    real_integral_ball_translate] at h
  exact h

theorem real_uniform_jet_l2_embedding (W : Yau.Jets.Coord → ℝ) (hW : ContDiff ℝ ∞ W)
    (n : ℕ) (y : Yau.Jets.Coord) (r : ℝ) (ds : List (Fin 4)) (hd : ds.length ≤ n)
    (x : Yau.Jets.Coord) (hx : x ∈ closedBall y r) :
    (partialJet W ds x)^2 ≤ 256 * (∫ z in closedBall y (r+1), realFiniteJetSquare W (n+4) z) := by
  have hsub : closedBall x 1 ⊆ closedBall y (r+1) := by
    intro z hz
    exact (dist_triangle z x y).trans (by linarith [mem_closedBall.mp hz,mem_closedBall.mp hx])
  have hs (z : Yau.Jets.Coord) : realFiniteJetSquare W (ds.length+4) z ≤ realFiniteJetSquare W (n+4) z := by
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega))
    intro a _ _
    exact Finset.sum_nonneg (fun _ _ ↦ sq_nonneg _)
  have hi (m : ℕ) (a : Yau.Jets.Coord) (s : ℝ) :
      IntegrableOn (realFiniteJetSquare W m) (closedBall a s) :=
    (realFiniteJetSquare_smooth W hW m).continuous.continuousOn.integrableOn_compact (isCompact_closedBall a s)
  have hmono := (setIntegral_mono_on (hi (ds.length+4) x 1) (hi (n+4) x 1)
    isClosed_closedBall.measurableSet (fun z _ ↦ hs z)).trans
    (setIntegral_mono_set (hi (n+4) y (r+1))
      (Filter.Eventually.of_forall (realFiniteJetSquare_nonneg W (n+4)))
      (Filter.Eventually.of_forall hsub))
  exact (real_point_jet_l2_embedding W hW ds x).trans
    (mul_le_mul_of_nonneg_left hmono (by norm_num))

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_RealGlobalJetEmbedding
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Yau.Analysis MeasureTheory Set Metric
open scoped ContDiff
noncomputable section

theorem real_global_jet_l2_embedding (W : Yau.Jets.Coord → ℝ)
    (hW : ContDiff ℝ ∞ W) (hc : HasCompactSupport W) (n : ℕ)
    (E : List (Fin 4) → ℝ)
    (hb : ∀ es, es.length ≤ n+4 → (∫ x, (partialJet W es x)^2) ≤ E es)
    (ds : List (Fin 4)) (hd : ds.length ≤ n) (x : Yau.Jets.Coord) :
    (partialJet W ds x)^2 ≤
      256 * ∑ r ∈ Finset.range (n+5), ∑ w : Fin r → Fin 4, E (List.ofFn w) := by
  have hi (es : List (Fin 4)) : Integrable (fun x ↦ (partialJet W es x)^2) :=
    (Yau.real_compact_continuous_memLp _ (partialJet_smooth W hW es).continuous
      (partialJet_compactSupport W hc es)).integrable_sq
  have hf : Integrable (realFiniteJetSquare W (n+4)) :=
    integrable_finsetSum _ (fun r _ ↦ integrable_finsetSum _ (fun w _ ↦ hi (List.ofFn w)))
  have h := real_uniform_jet_l2_embedding W hW n x 0 ds hd x (by simp)
  have hm := integral_mono_measure (Measure.restrict_le_self :
      volume.restrict (closedBall x (0+1)) ≤ volume)
    (Filter.Eventually.of_forall (realFiniteJetSquare_nonneg W (n+4))) hf
  have hs : (∫ z, realFiniteJetSquare W (n+4) z) ≤
      ∑ r ∈ Finset.range (n+5), ∑ w : Fin r → Fin 4, E (List.ofFn w) := by
    unfold realFiniteJetSquare
    rw [integral_finsetSum _ (fun r _ ↦ integrable_finsetSum _ (fun w _ ↦ hi (List.ofFn w)))]
    apply Finset.sum_le_sum
    intro r hr
    rw [integral_finsetSum _ (fun w _ ↦ hi (List.ofFn w))]
    apply Finset.sum_le_sum
    intro w _
    apply hb
    simp only [List.length_ofFn]
    exact Nat.le_of_lt_succ (Finset.mem_range.mp hr)
  exact h.trans (mul_le_mul_of_nonneg_left (hm.trans hs) (by norm_num))

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_RealGlobalJetCommonBound
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Yau.Analysis MeasureTheory Set
open scoped ContDiff
noncomputable section

theorem real_global_jet_common_bound (n : ℕ) :
    ∃ C > 0, ∀ W : Yau.Jets.Coord → ℝ, ContDiff ℝ ∞ W → HasCompactSupport W →
      ∀ E : ℝ, 0 ≤ E →
      (∀ es, es.length ≤ n+4 → (∫ x, (partialJet W es x)^2) ≤ E) →
      ∀ ds, ds.length ≤ n → ∀ x, (partialJet W ds x)^2 ≤ C*E := by
  let A : ℝ := ∑ r ∈ Finset.range (n+5), ∑ _w : Fin r → Fin 4, (1:ℝ)
  have hA : 0 ≤ A := Finset.sum_nonneg (fun _ _ ↦ Finset.sum_nonneg (fun _ _ ↦ by norm_num))
  refine ⟨256*(A+1),mul_pos (by norm_num) (by linarith only [hA]),fun W hW hc E hE hb ds hd x ↦ ?_⟩
  have h := real_global_jet_l2_embedding W hW hc n (fun _ ↦ E) hb ds hd x
  have hs : (∑ r ∈ Finset.range (n+5), ∑ _w : Fin r → Fin 4, E)=A*E := by
    simp only [A,Finset.sum_mul,one_mul]
  rw [hs] at h
  nlinarith

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_RealL2PointwiseLimit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau
open MeasureTheory Filter
open scoped Topology ContDiff
noncomputable section

theorem real_L2_pointwise_limit_ae {n : ℕ} (w : ℕ → Coord n → ℝ)
    (hw : ∀ j, MemLp (w j) 2 volume) (u v : Coord n → ℝ)
    (hu : MemLp u 2 volume)
    (hl : Tendsto (fun j ↦ (hw j).toLp (w j)) atTop (𝓝 (hu.toLp u)))
    (hp : ∀ x, Tendsto (fun j ↦ w j x) atTop (𝓝 (v x))) :
    v =ᵐ[volume] u := by
  have hm := (tendstoInMeasure_of_tendsto_Lp hl).congr
    (fun j ↦ (hw j).coeFn_toLp) hu.coeFn_toLp
  obtain ⟨nu,hnu,ha⟩ := hm.exists_seq_tendsto_ae
  filter_upwards [ha] with x hx
  exact tendsto_nhds_unique ((hp x).comp hnu.tendsto_atTop) hx

end
end Yau

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_RealWeakJetConvolution
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau
open MeasureTheory Set Yau.Analysis
open scoped ContDiff Convolution
noncomputable section

theorem real_weak_jet_convolution {n : ℕ}
    (U : List (Fin n) → Coord n → ℝ) (N : ℕ)
    (hU : ∀ es, es.length ≤ N → LocallyIntegrable (U es) volume)
    (hw : ∀ es, es.length < N → ∀ i psi,
      ContDiff ℝ ∞ psi → HasCompactSupport psi →
      (∫ x, U es x*coordPartial psi x i)=-(∫ x, U (i::es) x*psi x))
    (k : Coord n → ℝ) (hk : ContDiff ℝ ∞ k) (hc : HasCompactSupport k)
    (ds : List (Fin n)) (hd : ds.length ≤ N) :
    partialJet (U [] ⋆ k) ds=U ds ⋆ k := by
  induction ds with
  | nil => rfl
  | cons i ds ih =>
    have hlt : ds.length < N := by simp only [List.length_cons] at hd; omega
    change (fun x ↦ coordPartial (partialJet (U [] ⋆ k) ds) x i)=_
    rw [ih (by omega)]
    exact real_weak_convolution_derivative (U ds) (U (i::ds)) k (hU ds (by omega)) hk hc i (hw ds hlt i)

end
end Yau

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_RealSmoothWeakJetIdentification
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau
open MeasureTheory Set Filter Yau.Analysis
open scoped ContDiff Convolution Topology
noncomputable section

theorem real_smooth_partialJet_convolution {n : ℕ} (v k : Coord n → ℝ)
    (hv : ContDiff ℝ ∞ v) (hk : ContDiff ℝ ∞ k) (hc : HasCompactSupport k)
    (ds : List (Fin n)) :
    partialJet (v ⋆ k) ds=partialJet v ds ⋆ k := by
  apply real_weak_jet_convolution (partialJet v) ds.length
    (fun es _ ↦ (partialJet_smooth v hv es).continuous.locallyIntegrable)
  · intro es _ i psi hp hc
    have h := (real_compact_test_derivative (partialJet v es) psi
      (partialJet_smooth v hv es) hp hc i univ (subset_univ _)).2.2
    simp only [Measure.restrict_univ] at h
    simpa only [neg_neg,partialJet,coordPartial] using congrArg Neg.neg h.symm
  · exact hk
  · exact hc
  · exact le_rfl

theorem real_smooth_weak_jet_ae {n : ℕ}
    (U : List (Fin n) → Coord n → ℝ) (N : ℕ)
    (hU : ∀ es, es.length ≤ N → MemLp (U es) 2 volume ∧ HasCompactSupport (U es))
    (hw : ∀ es, es.length < N → ∀ i psi,
      ContDiff ℝ ∞ psi → HasCompactSupport psi →
      (∫ x, U es x*coordPartial psi x i)=-(∫ x, U (i::es) x*psi x))
    (v : Coord n → ℝ) (hv : ContDiff ℝ ∞ v) (ha : v =ᵐ[volume] U [])
    (ds : List (Fin n)) (hd : ds.length ≤ N) :
    partialJet v ds =ᵐ[volume] U ds := by
  let b : ℕ → ContDiffBump (0 : Coord n) := realMollifierBump 1 (by norm_num)
  let w : ℕ → Coord n → ℝ := fun j ↦ U ds ⋆ (b j).normed volume
  have hs (j : ℕ) : ContDiff ℝ ∞ (w j) ∧ HasCompactSupport (w j) :=
    real_compact_convolution_smooth _ _ ((hU ds hd).1.locallyIntegrable (by norm_num))
      (hU ds hd).2 (b j).contDiff_normed (b j).hasCompactSupport_normed
  have he (j : ℕ) : w j=partialJet v ds ⋆ (b j).normed volume := by
    rw [← real_smooth_partialJet_convolution v _ hv (b j).contDiff_normed (b j).hasCompactSupport_normed ds,
      convolution_congr (ContinuousLinearMap.lsmul ℝ ℝ) ha Filter.EventuallyEq.rfl,
      real_weak_jet_convolution U N (fun es hh ↦ (hU es hh).1.locallyIntegrable (by norm_num))
        hw _ (b j).contDiff_normed (b j).hasCompactSupport_normed ds hd]
  have hl := real_compact_convolution_L2_tendsto (U ds) (hU ds hd).1 (hU ds hd).2 b
    (realMollifierBump_radius_tendsto 1 (by norm_num))
  apply real_L2_pointwise_limit_ae w
    (fun j ↦ real_compact_continuous_memLp _ (hs j).1.continuous (hs j).2)
    (U ds) (partialJet v ds) (hU ds hd).1 hl
  intro x
  have ht := ContDiffBump.convolution_tendsto_right_of_continuous
    (μ := (volume : Measure (Coord n)))
    (realMollifierBump_radius_tendsto (n := n) 1 (by norm_num))
    (partialJet_smooth v hv ds).continuous x
  convert ht using 1
  all_goals try with_reducible_and_instances rfl
  funext j
  rw [he,convolution_lsmul_swap,convolution_def]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun y ↦ by
    dsimp only [ContinuousLinearMap.lsmul_apply,smul_eq_mul]
    ring)

end
end Yau

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_RealSmoothCutoffJetBound
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau
open MeasureTheory Set Yau.Analysis Yau.Geometry
open scoped ContDiff
noncomputable section

theorem real_smooth_cutoff_jet_bound {Q : Set Jets.Coord} (hQ : IsCompact Q)
    (eta : Jets.Coord → ℝ) (he : ContDiff ℝ ∞ eta) (hc : HasCompactSupport eta)
    (hs : tsupport eta ⊆ interior Q) (n : ℕ) :
    ∃ C > 0, ∀ U : List (Fin 4) → Jets.Coord → ℝ,
      (∀ es, es.length ≤ n+5 → MemLp (U es) 2 (volume.restrict Q)) →
      (∀ es, es.length ≤ n+4 → ∀ i psi,
        ContDiff ℝ ∞ psi → HasCompactSupport psi → tsupport psi ⊆ Q →
        (∫ x in Q, U es x*coordPartial psi x i)=-(∫ x in Q, U (i::es) x*psi x)) →
      ∀ E : ℝ, 0 ≤ E → (∀ es, es.length ≤ n+4 → (∫ x in Q, (U es x)^2) ≤ E) →
      ∀ v : Jets.Coord → ℝ, ContDiff ℝ ∞ v → HasCompactSupport v →
        v =ᵐ[volume] (fun x ↦ eta x*U [] x) →
        ∀ ds, ds.length ≤ n → ∀ x, (partialJet v ds x)^2 ≤ C*E := by
  obtain ⟨A,hA,ha⟩ := real_cutoff_weak_jet_square_bound hQ eta he (hs.trans interior_subset) (n+4)
  obtain ⟨B,hB,hb⟩ := real_global_jet_common_bound n
  refine ⟨B*A,mul_pos hB hA,fun U hU hw E hE hUE v hv hvc hve ds hd x ↦ ?_⟩
  let V := realWeakJetExpansion eta U []
  have hV := real_cutoff_finite_weak_jet hQ eta he hc hs U (n+4) hU hw
  have hz : v =ᵐ[volume] V [] := by
    change v =ᵐ[volume] (fun x ↦ realWeakJetExpansion eta U [] [] x)
    simpa only [V,realWeakJetExpansion,realJetErrorTerms,realWeakJetProductSum,
      List.append_nil,List.map_nil,List.sum_nil,add_zero] using hve
  have heq (es : List (Fin 4)) (hh : es.length ≤ n+4) : partialJet v es =ᵐ[volume] V es :=
    real_smooth_weak_jet_ae V (n+4)
      (fun es hh ↦ ⟨(hV.1 es hh).1,hc.of_isClosed_subset (isClosed_tsupport _) (hV.1 es hh).2⟩)
      (fun es hh i psi hp hc ↦ (hV.2 es hh i psi hp hc).2.2) v hv hz es hh
  have hbound (es : List (Fin 4)) (hh : es.length ≤ n+4) :
      (∫ x, (partialJet v es x)^2) ≤ A*E := by
    have hid := integral_congr_ae ((heq es hh).fun_comp (fun t : ℝ ↦ t^2))
    dsimp only [Function.comp_def] at hid
    rw [hid]
    exact ha U (fun es hh ↦ hU es (by omega)) E hE hUE es hh
  simpa only [mul_assoc] using hb v hv hvc (A*E) (mul_nonneg hA.le hE) hbound ds hd x

end
end Yau

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_RealCompactInteriorPointwise
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open MeasureTheory Set Filter Yau.Analysis
open scoped ContDiff Topology
noncomputable section

theorem real_compact_interior_pointwise_oai {K Q : Set Yau.Jets.Coord}
    (hK : IsCompact K) (hQ : IsCompact Q) (hKQ : K ⊆ interior Q) (n : ℕ) :
    ∃ A > 0, ∀ W : Yau.Jets.Coord → ℝ, ContDiff ℝ ∞ W →
      ∀ ds : List (Fin 4), ds.length ≤ n → ∀ x ∈ K,
        (partialJet W ds x)^2 ≤ A*(∫ y in Q, realFiniteJetSquare W (n+5) y) := by
  obtain ⟨eta,he,hc,hs,hr,hone⟩ := compact_smooth_cutoff hK isOpen_interior hKQ
  obtain ⟨A,hA,ha⟩ := Yau.real_smooth_cutoff_jet_bound hQ eta he hc hs n
  refine ⟨A,hA,fun W hW ds hds x hx ↦ ?_⟩
  let U := partialJet W
  have hU (es : List (Fin 4)) : MemLp (U es) 2 (volume.restrict Q) :=
    Yau.real_continuous_memLp_compact hQ _ (partialJet_smooth W hW es).continuous
  have hw : ∀ es : List (Fin 4), es.length ≤ n+4 → ∀ i psi,
      ContDiff ℝ ∞ psi → HasCompactSupport psi → tsupport psi ⊆ Q →
      (∫ y in Q, U es y*Yau.coordPartial psi y i) = -(∫ y in Q, U (i::es) y*psi y) := by
    intro es _ i psi hp hpc hps
    have hh := (Yau.real_compact_test_derivative (U es) psi
      (partialJet_smooth W hW es) hp hpc i Q hps).2.2
    simpa only [U,partialJet,Yau.coordPartial,neg_neg] using congrArg Neg.neg hh.symm
  have hi : IntegrableOn (realFiniteJetSquare W (n+5)) Q :=
    (realFiniteJetSquare_smooth W hW (n+5)).continuous.continuousOn.integrableOn_compact hQ
  have hE : 0 ≤ ∫ y in Q, realFiniteJetSquare W (n+5) y :=
    integral_nonneg (fun y ↦ realFiniteJetSquare_nonneg W (n+5) y)
  have hbound (es : List (Fin 4)) (hes : es.length ≤ n+4) :
      (∫ y in Q, (U es y)^2) ≤ ∫ y in Q, realFiniteJetSquare W (n+5) y := by
    exact integral_mono (hU es).integrable_sq hi
      (fun y ↦ partialJet_sq_le_realFiniteJetSquare W (n+5) es (by omega) y)
  let v := fun y ↦ eta y*W y
  have hv : ContDiff ℝ ∞ v := he.mul hW
  have hvc : HasCompactSupport v := hc.mul_right
  have hvW : v =ᶠ[𝓝 x] W := by
    filter_upwards [hone x hx] with y hy
    simp [v,hy]
  have h := ha U (fun es _ ↦ hU es) hw _ hE hbound v hv hvc
    (Filter.Eventually.of_forall (fun _ ↦ rfl)) ds hds x
  rw [partialJet_germ_eq v W x hvW ds] at h
  exact h

end
end Yau.Geometry

end OAI
end

theorem solution : type_of% @OAI.Yau.Geometry.real_compact_interior_pointwise_oai := @OAI.Yau.Geometry.real_compact_interior_pointwise_oai
