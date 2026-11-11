-- Prove2me | solution 1 for OAI.Yau.Target.sphere_eigen_global_representative
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T00:34:15.131422+00:00
-- url     : https://prove2.me/submissions/1699e13f-85b3-4eb7-9378-3c065b465ab3

import Mathlib
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.ContDiff.RestrictScalars
import Mathlib.Analysis.Calculus.Deriv.Abs
import Mathlib.Analysis.Calculus.Deriv.Pi
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Pi
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.Calculus.TaylorIntegral
import Mathlib.Analysis.Calculus.UniformLimitsDeriv
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.Completion
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.Normed.Lp.SmoothApprox
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Module.WeakDual
import Mathlib.Analysis.Normed.Operator.Compact.Basic
import Mathlib.Analysis.Normed.Operator.ContinuousLinearMap
import Mathlib.Analysis.Normed.Operator.Extend
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Finsupp.Weight
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Int.Interval
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.OfFn
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.ColumnRowPartitioned
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Geometry.Manifold.Algebra.LieGroup
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.Geometry.Manifold.Riemannian.Basic
import Mathlib.Geometry.Manifold.SmoothApprox
import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection
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
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousCompMeasurePreserving
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.ContDiff
import Mathlib.MeasureTheory.Integral.IntervalIntegral.DistLEIntegral
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.Algebra.Support
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Compactness.LocallyCompact
import Mathlib.Topology.ContinuousMap.Bounded.ArzelaAscoli
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Sequences
import Mathlib.Topology.UniformSpace.UniformApproximation
import Mathlib.Topology.UniformSpace.UniformConvergence
import Definitions.Def_YauCounterexample
import Definitions.Def_OAIQ237Ny004
import Theorems.Thm_OAI_Yau_Target_sphere_eigen_all_finite_weak_jets

section
-- module Solutions.OAIQ237_NY.NodalSets_Charts_ManifoldCompactExtension
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Set Filter Manifold
open scoped ContDiff Topology
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [NormalSpace M] [SigmaCompactSpace M] [LocallyCompactSpace M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

lemma manifold_compact_smooth_cutoff {K U : Set M} (hK : IsCompact K)
    (hU : IsOpen U) (hKU : K ⊆ U) :
    ∃ b : M → ℝ, ContMDiff I 𝓘(ℝ) ∞ b ∧ HasCompactSupport b ∧
      tsupport b ⊆ U ∧ (∀ x, 0 ≤ b x ∧ b x ≤ 1) ∧
      ∀ x ∈ K, b =ᶠ[𝓝 x] (fun _ ↦ 1) := by
  obtain ⟨L,hL,hKL,hLU⟩ := exists_compact_between hK hU hKU
  obtain ⟨b,hb1,hb0,hb⟩ := exists_contMDiffMap_one_nhds_of_subset_interior
    I hK.isClosed hKL (n := (⊤ : ℕ∞))
  have hsupp : tsupport (b : M → ℝ) ⊆ L := by
    apply closure_minimal _ hL.isClosed
    intro x hx
    by_contra h
    exact hx (hb0 x h)
  refine ⟨b,b.contMDiff,hL.of_isClosed_subset isClosed_closure hsupp,
    hsupp.trans hLU,hb,?_⟩
  intro x hx
  exact Filter.Eventually.filter_mono (nhds_le_nhdsSet hx) hb1

end
end Yau.Geometry

end OAI
end

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
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_RealCoordinateEllipticLemmas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Yau
open scoped ContDiff
variable {n : ℕ}

lemma real_coordPartial_sum (f : Fin n → Coord n → ℝ)
    (hf : ∀ j, ContDiff ℝ ∞ (f j)) (x : Coord n) (i : Fin n) :
    coordPartial (fun y ↦ ∑ j, f j y) x i = ∑ j, coordPartial (f j) x i := by
  unfold coordPartial
  rw [fderiv_fun_sum (fun j _ ↦ (hf j).differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) x)]
  simp

end Yau

end

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_IntrinsicRealCoordinates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Manifold Matrix Yau.Geometry
open scoped ContDiff
noncomputable section

lemma intrinsicRealPrincipal_symmetric (A : IntrinsicTensor)
    (hs : ∀ p v w, A p v w = A p w v) (p : Base) (x : Yau.Jets.Coord) (i j : Fin 4) :
    intrinsicRealPrincipal A p x i j = intrinsicRealPrincipal A p x j i :=
  hs _ _ _

end
end Yau.Target

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

lemma partialJet_eq_iterated (f : (ι → ℝ) → ℝ) (hf : ContDiff ℝ ∞ f)
    (ds : List ι) (x : ι → ℝ) :
    partialJet f ds x = iteratedFDeriv ℝ ds.length f x (partialDirs ds) := by
  induction ds generalizing x with
  | nil => simp [partialJet,partialDirs,iteratedFDeriv_zero_apply]
  | cons i ds ih =>
    have hh : partialJet f ds = fun x ↦ iteratedFDeriv ℝ ds.length f x (partialDirs ds) :=
      funext ih
    change fderiv ℝ (partialJet f ds) x (Pi.single i 1) = _
    rw [hh]
    symm
    have hdiff := hf.differentiable_iteratedFDeriv (m := ds.length)
      (by exact_mod_cast (show (ds.length:ℕ∞) < ⊤ from WithTop.coe_lt_top _))
    simpa only [List.length_cons,partialDirs,Fin.cons_zero,Fin.tail_cons] using
      (hdiff x).iteratedFDeriv_succ_apply_left' (m := Fin.cons (Pi.single i 1) (partialDirs ds))

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
-- module Solutions.OAIQ237_NY.NodalSets_Charts_SphereChartScalarExtension
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Manifold Yau.Geometry Yau.Jets Set Filter
open scoped ContDiff Topology
noncomputable section
variable (center : Base)

lemma sphereChartToCoord_from (x : Yau.Jets.Coord) :
    sphereChartToCoord center (sphereChartCoordMap center x) = x := by
  unfold sphereChartToCoord sphereChartCoordMap
  rw [(extChartAt (𝓡 4) center).right_inv (by rw [centeredSphereChart_target]; trivial)]
  exact seedCoordEquiv.symm_apply_apply x

lemma sphereChartCoordMap_to {p : Base} (hp : p ∈ (extChartAt (𝓡 4) center).source) :
    sphereChartCoordMap center (sphereChartToCoord center p) = p := by
  unfold sphereChartToCoord sphereChartCoordMap
  rw [seedCoordEquiv.apply_symm_apply,(extChartAt (𝓡 4) center).left_inv hp]

theorem sphere_chart_scalar_extension (v : Yau.Jets.Coord → ℝ) (hv : ContDiff ℝ ∞ v)
    (hc : HasCompactSupport v) :
    ∃ F : Base → ℝ, ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ F ∧
      tsupport F ⊆ sphereChartCoordMap center '' tsupport v ∧
      ∀ x, F (sphereChartCoordMap center x) = v x := by
  let K := sphereChartCoordMap center '' tsupport v
  have hK : IsCompact K := hc.image (sphereChartCoordMap_smooth center).continuous
  have hKU : K ⊆ (extChartAt (𝓡 4) center).source := by
    rintro p ⟨x,hx,rfl⟩
    exact sphereChartCoordMap_source center x
  have hU : IsOpen (extChartAt (𝓡 4) center).source := isOpen_extChartAt_source center
  obtain ⟨b,hb,hbc,hbs,hbr,hb1⟩ := manifold_compact_smooth_cutoff (I := 𝓡 4) hK hU hKU
  let F : Base → ℝ := fun p ↦ b p*v (sphereChartToCoord center p)
  have hF : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ F := by
    intro p
    by_cases hp : p ∈ tsupport b
    · have hcoord : ContMDiffAt (𝓡 4) 𝓘(ℝ,Yau.Jets.Coord) ∞ (sphereChartToCoord center) p :=
        seedCoordEquiv.symm.contDiff.contMDiff.contMDiffAt.comp p
          (contMDiffAt_extChartAt' (by simpa using hbs hp))
      exact (hb p).mul (hv.contMDiff.contMDiffAt.comp p hcoord)
    · apply (contMDiffAt_const (c := (0:ℝ))).congr_of_eventuallyEq
      filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hp] with z hz
      simp [F,hz]
  have hs : tsupport F ⊆ K := by
    apply closure_minimal _ hK.isClosed
    intro p hp
    have hbne : b p ≠ 0 := fun h ↦ hp (by simp [F,h])
    have hvne : v (sphereChartToCoord center p) ≠ 0 := fun h ↦ hp (by simp [F,h])
    exact ⟨sphereChartToCoord center p,subset_closure hvne,
      sphereChartCoordMap_to center (hbs (subset_closure hbne))⟩
  refine ⟨F,hF,hs,?_⟩
  intro x
  dsimp [F]
  rw [sphereChartToCoord_from]
  by_cases hx : v x = 0
  · simp [hx]
  · have h := (hb1 (sphereChartCoordMap center x) ⟨x,subset_closure hx,rfl⟩).eq_of_nhds
    rw [h,one_mul]

end
end Yau.Target

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
-- module Solutions.OAIQ237_NY.NodalSets_Charts_SphereChartDivergenceData
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open MeasureTheory Yau.Geometry Set
open scoped ContDiff
noncomputable section

local instance sphereChartDivergenceDataMeasurable_rd94634_1 : MeasurableSpace Base := borel Base
local instance sphereChartDivergenceDataBorel_rd94634_1 : BorelSpace Base := ⟨rfl⟩
theorem sphereChartPrincipalDensity_smooth (d : SphereEnergyData) (p : Base) (i j : Fin 4) :
    ContDiff ℝ ∞ (fun x ↦ sphereChartPrincipalDensity d p x i j) :=
  roundCoordDensity_smooth.mul (intrinsicRealPrincipal_smooth d.tensor d.smooth d.symm d.pos p i j)

theorem sphereChartPrincipalDensity_symmetric (d : SphereEnergyData) (p : Base)
    (x : Yau.Jets.Coord) (i j : Fin 4) :
    sphereChartPrincipalDensity d p x i j=sphereChartPrincipalDensity d p x j i := by
  unfold sphereChartPrincipalDensity
  rw [intrinsicRealPrincipal_symmetric d.tensor d.symm]

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Charts_SphereSmallChartPartition
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Manifold Yau.Geometry Set Metric
open scoped Topology ContDiff
noncomputable section

theorem finite_sphere_coordinate_cover_radius (r : ℝ) (hr : 0 < r) :
    ∃ P : Finset Base, ∀ x : Base, ∃ p ∈ P, ∃ z ∈ ball (0 : Yau.Jets.Coord) r,
      sphereChartCoordMap p z = x := by
  have hcover : (univ : Set Base) ⊆ ⋃ p : Base, sphereChartCoordMap p '' ball (0 : Yau.Jets.Coord) r := by
    intro x _
    exact mem_iUnion.mpr ⟨x,0,mem_ball_self hr,sphereChartCoordMap_zero x⟩
  obtain ⟨P,hP⟩ := isCompact_univ.elim_finite_subcover
    (fun p : Base ↦ sphereChartCoordMap p '' ball (0 : Yau.Jets.Coord) r)
    (fun p ↦ sphereChartCoordMap_isOpenMap p _ isOpen_ball) hcover
  refine ⟨P,?_⟩
  intro x
  obtain ⟨p,hp,z,hz,hzx⟩ := mem_iUnion₂.mp (hP (mem_univ x))
  exact ⟨p,hp,z,hz,hzx⟩

theorem sphere_finite_smooth_partition_radius (r : ℝ) (hr : 0 < r) :
    ∃ (P : Finset Base) (theta : {p // p ∈ P} → Base → ℝ),
      (∀ p, ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ (theta p)) ∧
      (∀ p x, 0 ≤ theta p x) ∧ (∀ x, ∑ p, theta p x=1) ∧
      (∀ p, tsupport (theta p) ⊆ sphereChartCoordMap p.val '' ball (0 : Yau.Jets.Coord) r) ∧
      (∀ p, tsupport (theta p ∘ sphereChartCoordMap p.val) ⊆ closedBall (0 : Yau.Jets.Coord) r) ∧
      (∀ p, HasCompactSupport (theta p ∘ sphereChartCoordMap p.val)) := by
  classical
  obtain ⟨P,hP⟩ := finite_sphere_coordinate_cover_radius r hr
  let U : {p // p ∈ P} → Set Base := fun p ↦ sphereChartCoordMap p.val '' ball (0 : Yau.Jets.Coord) r
  have hcover : (univ : Set Base) ⊆ ⋃ p, U p := by
    intro x _
    obtain ⟨p,hp,z,hz,hzx⟩ := hP x
    exact mem_iUnion.mpr ⟨⟨p,hp⟩,z,hz,hzx⟩
  obtain ⟨theta,hsub⟩ := SmoothPartitionOfUnity.exists_isSubordinate (𝓡 4) isClosed_univ U
    (fun p ↦ sphereChartCoordMap_isOpenMap p.val _ isOpen_ball) hcover
  have hs (p : {p // p ∈ P}) :
      tsupport (theta p ∘ sphereChartCoordMap p.val) ⊆ closedBall (0 : Yau.Jets.Coord) r := by
    apply closure_minimal _ isClosed_closedBall
    intro x hx
    obtain ⟨y,hy,he⟩ := hsub p (subset_closure hx)
    have hxy : y=x := sphereChartCoordMap_injective p.val he
    exact hxy ▸ ball_subset_closedBall hy
  refine ⟨P,(fun p ↦ theta p),(fun p ↦ (theta p).contMDiff),theta.nonneg,?_,hsub,hs,?_⟩
  · intro x
    have h := theta.sum_eq_one (mem_univ x)
    rw [finsum_eq_sum_of_support_subset _ (s := Finset.univ) (by simp)] at h
    exact h
  · intro p
    exact (isCompact_closedBall (0 : Yau.Jets.Coord) r).of_isClosed_subset isClosed_closure (hs p)

end
end Yau.Target

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

theorem realL2Translate_norm {n : ℕ} (v : Fin n → ℝ) (f : RealEuclideanL2 n) :
    ‖realL2Translate v f‖=‖f‖ := Lp.norm_compMeasurePreserving f _

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
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_RealDifferenceQuotientTest
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau
open MeasureTheory Set
open scoped ContDiff
noncomputable section

theorem realCenteredCube_isCompact (n : ℕ) (r : ℝ) : IsCompact (realCenteredCube n r) :=
  isCompact_univ_pi (fun _ ↦ isCompact_Icc)

end
end Yau

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

theorem realMollifierBump_radius_le {n : ℕ} (r : ℝ) (hr : 0 < r) (m : ℕ) :
    (realMollifierBump (n := n) r hr m).rOut ≤ r := by
  change r*(1/((m:ℝ)+1)) ≤ r
  have h : 1/((m:ℝ)+1) ≤ 1 := (div_le_one (by positivity)).mpr (by linarith [Nat.cast_nonneg (α := ℝ) m])
  nlinarith

theorem real_convolution_support_in_thickening {n : ℕ} {K : Set (Coord n)}
    (u k : Coord n → ℝ) (r : ℝ) (hu : tsupport u ⊆ K)
    (hk : tsupport k ⊆ closedBall 0 r) :
    tsupport (u ⋆ k) ⊆ cthickening r K := by
  apply closure_minimal _ isClosed_cthickening
  intro x hx
  obtain ⟨a,ha,b,hb,rfl⟩ := support_convolution_subset (lsmul ℝ ℝ) hx
  apply mem_cthickening_of_dist_le (a+b) a r K (hu (subset_tsupport u ha))
  have ht := hk (subset_tsupport k hb)
  simpa only [mem_closedBall, dist_eq_norm, add_sub_cancel_left, sub_zero] using ht

theorem real_compact_mollifier_support {n : ℕ} {K L : Set (Coord n)}
    (hK : IsCompact K) (hKL : K ⊆ interior L) :
    ∃ (r : ℝ) (hr : 0 < r), ∀ (u : Coord n → ℝ), tsupport u ⊆ K → ∀ m : ℕ,
      tsupport (u ⋆ (realMollifierBump r hr m).normed volume) ⊆ L := by
  obtain ⟨r,hr,hs⟩ := hK.exists_cthickening_subset_open isOpen_interior hKL
  refine ⟨r,hr,?_⟩
  intro u hu m
  apply (real_convolution_support_in_thickening u _ r hu ?_).trans
    (hs.trans interior_subset)
  rw [(realMollifierBump (n := n) r hr m).tsupport_normed_eq]
  exact closedBall_subset_closedBall (realMollifierBump_radius_le r hr m)

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
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_RealConvolutionContraction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau
open MeasureTheory Set ContinuousLinearMap
open scoped ContDiff Convolution
noncomputable section

theorem realL2Convolution_normed_norm_le {n : ℕ}
    (b : ContDiffBump (0 : Coord n)) (U : RealEuclideanL2 n) :
    ‖realL2Convolution (b.normed volume) U‖ ≤ ‖U‖ := by
  calc
    _ ≤ ∫ t, ‖b.normed volume t • realL2Translate (-t) U‖ :=
      norm_integral_le_integral_norm _
    _ = ∫ t, b.normed volume t * ‖U‖ := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun t ↦ by
        dsimp only
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (b.nonneg_normed t),
          realL2Translate_norm])
    _ = ‖U‖ := by rw [integral_mul_const, b.integral_normed, one_mul]

theorem real_normed_convolution_square_le {n : ℕ} (u : Coord n → ℝ)
    (hu : MemLp u 2 volume) (hc : HasCompactSupport u)
    (b : ContDiffBump (0 : Coord n)) :
    (∫ x, ((u ⋆ b.normed volume) x)^2) ≤ ∫ x, (u x)^2 := by
  have hv : ContDiff ℝ ∞ (u ⋆ b.normed volume) := (b.hasCompactSupport_normed (μ := volume)).contDiff_convolution_right
    (lsmul ℝ ℝ) (hu.locallyIntegrable (by norm_num)) b.contDiff_normed
  have hs : HasCompactSupport (u ⋆ b.normed volume) := hc.convolution (lsmul ℝ ℝ) (b.hasCompactSupport_normed (μ := volume))
  have hm := real_compact_continuous_memLp _ hv.continuous hs
  rw [← real_toLp_norm_sq _ hm, ← real_toLp_norm_sq u hu,
    ← realL2Convolution_eq_toLp u _ (real_compact_memLp_integrable u hu hc)
      hu b.contDiff_normed b.hasCompactSupport_normed hm]
  exact pow_le_pow_left₀ (norm_nonneg _) (realL2Convolution_normed_norm_le b _) 2

end
end Yau

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
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_RealInteriorWeakUniqueness
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau
open MeasureTheory Set
open scoped ContDiff
noncomputable section

theorem real_interior_L2_eq_of_test_pairings {n : ℕ} {K : Set (Coord n)} (hK : IsCompact K)
    (u v : Coord n → ℝ) (hu : MemLp u 2 (volume.restrict K))
    (hv : MemLp v 2 (volume.restrict K))
    (hpair : ∀ psi : Coord n → ℝ, ContDiff ℝ ∞ psi → HasCompactSupport psi → tsupport psi ⊆ K →
      (∫ x in K, u x*psi x)=(∫ x in K, v x*psi x)) :
    u =ᵐ[volume.restrict (interior K)] v := by
  let : IsFiniteMeasure (volume.restrict K) := isFiniteMeasure_restrict.mpr hK.measure_ne_top
  have hI : IntegrableOn (fun x ↦ u x-v x) K := (hu.sub hv).integrable (by norm_num)
  have he := isOpen_interior.ae_eq_zero_of_integral_contDiff_smul_eq_zero
    (hI.locallyIntegrableOn.mono_set interior_subset)
  have hz : ∀ᵐ x ∂volume, x ∈ interior K → u x-v x=0 := by
    apply he
    intro psi hp hc hs
    have hsame : (∫ x, psi x • (u x-v x)) = ∫ x in K, psi x*(u x-v x) := by
      symm
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro x hx
      rw [image_eq_zero_of_notMem_tsupport (fun ht ↦ hx (interior_subset (hs ht))),zero_mul]
    rw [hsame]
    have hpsi := real_continuous_memLp_compact hK psi hp.continuous
    have hiu : IntegrableOn (fun x ↦ u x*psi x) K := hu.integrable_mul hpsi
    have hiv : IntegrableOn (fun x ↦ v x*psi x) K := hv.integrable_mul hpsi
    have hid : (fun x ↦ psi x*(u x-v x)) = fun x ↦ u x*psi x-v x*psi x := by funext x; ring
    rw [hid,integral_sub hiu hiv,hpair psi hp hc (hs.trans interior_subset),sub_self]
  apply (ae_restrict_iff' isOpen_interior.measurableSet).mpr
  filter_upwards [hz] with x hx hmem
  exact sub_eq_zero.mp (hx hmem)

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
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_RealCoordinateDerivativeNorm
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

lemma real_coordinate_multilinear_norm (n : ℕ)
    (M : ContinuousMultilinearMap ℝ (fun _ : Fin n ↦ Yau.Jets.Coord) ℝ)
    (B : ℝ) (hB : 0 ≤ B)
    (hb : ∀ w : Fin n → Fin 4, ‖M (fun j ↦ Pi.single (w j) 1)‖ ≤ B) :
    ‖M‖ ≤ 4^n * B := by
  apply ContinuousMultilinearMap.opNorm_le_bound (by positivity)
  intro v
  have he : v = fun j ↦ ∑ i : Fin 4, v j i • (Pi.single i 1 : Yau.Jets.Coord) := by
    ext j i
    simp [Pi.single_apply,Finset.sum_apply]
  calc
    ‖M v‖ = ‖∑ w : Fin n → Fin 4, M (fun j ↦ v j (w j) • Pi.single (w j) 1)‖ := by
      conv_lhs => rw [he,M.map_sum]
    _ ≤ ∑ w : Fin n → Fin 4, B * ∏ j, ‖v j‖ := by
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro w _
      rw [M.map_smul_univ,norm_smul,Real.norm_eq_abs,Finset.abs_prod]
      have hp : (∏ j : Fin n, |v j (w j)|) ≤ ∏ j, ‖v j‖ :=
        Finset.prod_le_prod (fun _ _ ↦ abs_nonneg _) (fun j _ ↦ norm_le_pi_norm (v j) (w j))
      exact (mul_le_mul hp (hb w) (norm_nonneg _) (Finset.prod_nonneg (fun _ _ ↦ norm_nonneg _))).trans_eq
        (mul_comm _ _)
    _ = (4^n*B) * ∏ j, ‖v j‖ := by simp [mul_assoc]

lemma partialDirs_eq_get (ds : List (Fin 4)) :
    partialDirs ds = fun j ↦ (Pi.single (ds.get j) 1 : Yau.Jets.Coord) := by
  induction ds with
  | nil => ext j; exact Fin.elim0 j
  | cons i ds ih =>
    funext j
    refine Fin.cases ?_ (fun k ↦ ?_) j
    · rfl
    · simpa only [partialDirs,Fin.cons_succ,Fin.val_succ,List.get_eq_getElem,List.getElem_cons_succ] using congrFun ih k

theorem iteratedFDeriv_norm_le_coordinate_bound (W : Yau.Jets.Coord → ℝ)
    (hW : ContDiff ℝ ∞ W) (n : ℕ) (x : Yau.Jets.Coord) (B : ℝ) (hB : 0 ≤ B)
    (hb : ∀ ds : List (Fin 4), ds.length=n → |partialJet W ds x| ≤ B) :
    ‖iteratedFDeriv ℝ n W x‖ ≤ 4^n * B := by
  apply real_coordinate_multilinear_norm n _ B hB
  intro w
  have he := partialJet_eq_iterated W hW (List.ofFn w) x
  simp only [partialDirs_eq_get,List.get_eq_getElem,List.getElem_ofFn] at he
  have he' : partialJet W (List.ofFn w) x =
      iteratedFDeriv ℝ n W x (fun j ↦ Pi.single (w j) 1) := by
    have aux (m : ℕ) (hm : m=n) :
        iteratedFDeriv ℝ m W x (fun j ↦ Pi.single (w (Fin.cast hm j)) 1) =
          iteratedFDeriv ℝ n W x (fun j ↦ Pi.single (w j) 1) := by
      subst m
      rfl
    exact he.trans (aux _ List.length_ofFn)
  rw [← he',Real.norm_eq_abs]
  exact hb _ List.length_ofFn

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_RealPartialJetLipschitz
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Yau.Analysis Metric
open scoped ContDiff NNReal
noncomputable section

theorem real_partialJet_lipschitz (W : Yau.Jets.Coord → ℝ) (hW : ContDiff ℝ ∞ W)
    (ds : List (Fin 4)) (y : Yau.Jets.Coord) (r : ℝ) (B : ℝ≥0)
    (hb : ∀ i : Fin 4, ∀ x ∈ closedBall y r, |partialJet W (i::ds) x| ≤ B) :
    LipschitzOnWith (4*B) (partialJet W ds) (closedBall y r) := by
  apply (convex_closedBall y r).lipschitzOnWith_of_nnnorm_fderiv_le
    (fun x _ ↦ (partialJet_smooth W hW ds).differentiable (by simp) x)
  intro x hx
  have h := iteratedFDeriv_norm_le_coordinate_bound (partialJet W ds)
    (partialJet_smooth W hW ds) 1 x B B.coe_nonneg (by
      intro es hes
      obtain ⟨i,rfl⟩ := List.length_eq_one_iff.mp hes
      exact hb i x hx)
  rw [pow_one,norm_iteratedFDeriv_one] at h
  exact_mod_cast h

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_RealCoordinateDual
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Yau.Analysis Set Metric Filter
open scoped Topology ContDiff
noncomputable section

lemma realCoordinateDual_apply (a v : Yau.Jets.Coord) :
    realCoordinateDual a v = ∑ i, a i*v i := by
  simp [realCoordinateDual]

lemma realCoordinateDual_single (a : Yau.Jets.Coord) (i : Fin 4) :
    realCoordinateDual a (Pi.single i 1) = a i := by
  simp [realCoordinateDual_apply,Pi.single_apply]

lemma real_fderiv_coordinateDual (F : Yau.Jets.Coord → ℝ) (x : Yau.Jets.Coord) :
    fderiv ℝ F x = realCoordinateDual (fun i ↦ fderiv ℝ F x (Pi.single i 1)) := by
  ext v
  have he : v = ∑ i : Fin 4, v i • (Pi.single i 1 : Yau.Jets.Coord) := by
    ext i
    simp [Finset.sum_apply,Pi.single_apply]
  conv_lhs => rw [he]
  simp [realCoordinateDual_apply,mul_comm]

theorem real_uniform_coordinate_dual {F : Fin 4 → ℕ → Yau.Jets.Coord → ℝ}
    {g : Fin 4 → Yau.Jets.Coord → ℝ} {Q : Set Yau.Jets.Coord}
    (h : ∀ i, TendstoUniformlyOn (F i) (g i) atTop Q) :
    TendstoUniformlyOn (fun j x ↦ realCoordinateDual (fun i ↦ F i j x))
      (fun x ↦ realCoordinateDual (fun i ↦ g i x)) atTop Q := by
  apply realCoordinateDual.uniformContinuous.comp_tendstoUniformlyOn
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  have hh (i : Fin 4) := Metric.tendstoUniformlyOn_iff.mp (h i) ε hε
  filter_upwards [Filter.eventually_all.mpr hh] with j hj x hx
  exact (dist_pi_lt_iff hε).mpr (fun i ↦ hj i x hx)

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_RealJetLimitDerivative
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Yau.Analysis Set Metric Filter
open scoped Topology ContDiff
noncomputable section

theorem real_jet_limit_hasFDerivAt (W : ℕ → Yau.Jets.Coord → ℝ)
    (hW : ∀ j, ContDiff ℝ ∞ (W j)) (g : List (Fin 4) → Yau.Jets.Coord → ℝ)
    (ht : ∀ ds (Q : Set Yau.Jets.Coord), IsCompact Q →
      TendstoUniformlyOn (fun j ↦ partialJet (W j) ds) (g ds) atTop Q)
    (ds : List (Fin 4)) (x : Yau.Jets.Coord) :
    HasFDerivAt (g ds) (realCoordinateDual (fun i ↦ g (i::ds) x)) x := by
  have hu := real_uniform_coordinate_dual (fun i ↦ ht (i::ds) (closedBall x 1) (isCompact_closedBall x 1))
  apply hasFDerivAt_of_tendstoUniformlyOn isOpen_ball (hu.mono ball_subset_closedBall)
    (f := fun j ↦ partialJet (W j) ds)
  · intro j y _
    change HasFDerivAt (partialJet (W j) ds)
      (realCoordinateDual (fun i ↦ fderiv ℝ (partialJet (W j) ds) y (Pi.single i 1))) y
    rw [← real_fderiv_coordinateDual]
    exact ((partialJet_smooth _ (hW j) ds).differentiable (by simp) y).hasFDerivAt
  · intro y _
    exact (ht ds {y} isCompact_singleton).tendsto_at (mem_singleton y)
  · exact mem_ball_self (by norm_num)

theorem real_jet_limit_smooth (g : List (Fin 4) → Yau.Jets.Coord → ℝ)
    (hc : ∀ ds, Continuous (g ds))
    (hd : ∀ ds x, HasFDerivAt (g ds) (realCoordinateDual (fun i ↦ g (i::ds) x)) x) :
    ∀ ds, ContDiff ℝ ∞ (g ds) := by
  have hn (n : ℕ) : ∀ ds, ContDiff ℝ n (g ds) := by
    induction n with
    | zero => intro ds; exact contDiff_zero.mpr (hc ds)
    | succ n ih =>
      intro ds
      rw [show ((n+1:ℕ) : ℕ∞ω) = (n:ℕ∞ω)+1 by simp,contDiff_succ_iff_fderiv]
      refine ⟨fun x ↦ (hd ds x).differentiableAt,by simp,?_⟩
      have he : fderiv ℝ (g ds) = fun x ↦ realCoordinateDual (fun i ↦ g (i::ds) x) :=
        funext (fun x ↦ (hd ds x).fderiv)
      rw [he]
      exact realCoordinateDual.contDiff.comp (contDiff_pi.mpr (fun i ↦ ih (i::ds)))
  intro ds
  exact contDiff_infty.mpr (fun n ↦ hn n ds)

theorem real_jet_limit_identification (g : List (Fin 4) → Yau.Jets.Coord → ℝ)
    (hd : ∀ ds x, HasFDerivAt (g ds) (realCoordinateDual (fun i ↦ g (i::ds) x)) x)
    (ds : List (Fin 4)) : partialJet (g []) ds = g ds := by
  induction ds with
  | nil => rfl
  | cons i ds ih =>
    funext x
    change fderiv ℝ (partialJet (g []) ds) x (Pi.single i 1) = _
    rw [ih,(hd ds x).fderiv,realCoordinateDual_single]

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_RealJetUniformDerivative
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Yau.Analysis Set Metric Filter
open scoped Topology ContDiff
noncomputable section

lemma iteratedFDeriv_coordinate_apply (W : Yau.Jets.Coord → ℝ) (hW : ContDiff ℝ ∞ W)
    (n : ℕ) (w : Fin n → Fin 4) (x : Yau.Jets.Coord) :
    iteratedFDeriv ℝ n W x (fun j ↦ Pi.single (w j) 1) = partialJet W (List.ofFn w) x := by
  have he := partialJet_eq_iterated W hW (List.ofFn w) x
  simp only [partialDirs_eq_get,List.get_eq_getElem,List.getElem_ofFn] at he
  have aux (m : ℕ) (hm : m=n) :
      iteratedFDeriv ℝ m W x (fun j ↦ Pi.single (w (Fin.cast hm j)) 1) =
        iteratedFDeriv ℝ n W x (fun j ↦ Pi.single (w j) 1) := by
    subst m
    rfl
  exact (he.trans (aux _ List.length_ofFn)).symm

theorem real_uniform_iteratedFDeriv (W : ℕ → Yau.Jets.Coord → ℝ) (v : Yau.Jets.Coord → ℝ)
    (hW : ∀ j, ContDiff ℝ ∞ (W j)) (hv : ContDiff ℝ ∞ v) (n : ℕ) (Q : Set Yau.Jets.Coord)
    (ht : ∀ ds : List (Fin 4), ds.length=n →
      TendstoUniformlyOn (fun j ↦ partialJet (W j) ds) (partialJet v ds) atTop Q) :
    TendstoUniformlyOn (fun j ↦ iteratedFDeriv ℝ n (W j)) (iteratedFDeriv ℝ n v) atTop Q := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  let δ := ε/(4^n+1)
  have hp : (0:ℝ) < 4^n+1 := by positivity
  have hδ : 0 < δ := div_pos hε hp
  have hh (w : Fin n → Fin 4) := Metric.tendstoUniformlyOn_iff.mp
    (ht (List.ofFn w) List.length_ofFn) δ hδ
  filter_upwards [Filter.eventually_all.mpr hh] with j hj x hx
  rw [dist_eq_norm]
  have hb : ‖iteratedFDeriv ℝ n v x - iteratedFDeriv ℝ n (W j) x‖ ≤ 4^n*δ := by
    apply real_coordinate_multilinear_norm n _ δ hδ.le
    intro w
    simpa only [sub_apply,iteratedFDeriv_coordinate_apply v hv,
      iteratedFDeriv_coordinate_apply (W j) (hW j),← dist_eq_norm] using (hj w x hx).le
  apply hb.trans_lt
  calc
    4^n*δ < (4^n+1)*δ := mul_lt_mul_of_pos_right (lt_add_one _) hδ
    _ = ε := by dsimp [δ]; field_simp

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_RealCompactLipschitzFamily
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Set Metric Filter BoundedContinuousFunction
open scoped Topology NNReal
noncomputable section
variable {X : Type*} [PseudoMetricSpace X] [CompactSpace X]

theorem real_bounded_lipschitz_compact (F : ℕ → X →ᵇ ℝ) (B : ℝ) (L : ℝ≥0)
    (hb : ∀ j x, |F j x| ≤ B) (hL : ∀ j, LipschitzWith L (F j)) :
    IsCompact (closure (range F)) := by
  apply BoundedContinuousFunction.arzela_ascoli (Icc (-B) B) isCompact_Icc (range F)
  · rintro f x ⟨j,rfl⟩
    exact abs_le.mp (hb j x)
  · intro x
    rw [Metric.equicontinuousAt_iff]
    intro ε hε
    refine ⟨ε/((L:ℝ)+1),div_pos hε (by positivity),?_⟩
    intro y hy f
    rcases f with ⟨_,j,rfl⟩
    have h := (hL j).dist_le_mul x y
    have hd : dist x y < ε/((L:ℝ)+1) := by simpa only [dist_comm] using hy
    have hh := (lt_div_iff₀ (show 0 < (L:ℝ)+1 by positivity)).mp hd
    exact h.trans_lt (by nlinarith [dist_nonneg (x:=x) (y:=y)])

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_RealCountableCompactness
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Set Metric Filter BoundedContinuousFunction
open scoped Topology NNReal
noncomputable section
variable {I : Type*} [Countable I] {X : I → Type*}
  [∀ i, PseudoMetricSpace (X i)] [∀ i, CompactSpace (X i)]

theorem real_countable_uniform_subsequence (F : ∀ i, ℕ → X i → ℝ)
    (B : I → ℝ) (L : I → ℝ≥0)
    (hb : ∀ i j x, |F i j x| ≤ B i) (hL : ∀ i j, LipschitzWith (L i) (F i j)) :
    ∃ f : ∀ i, X i → ℝ, (∀ i, Continuous (f i)) ∧
      ∃ nu : ℕ → ℕ, StrictMono nu ∧ ∀ i,
        TendstoUniformly (fun j ↦ F i (nu j)) (f i) atTop := by
  let G : ∀ i, ℕ → X i →ᵇ ℝ := fun i j ↦
    BoundedContinuousFunction.mkOfCompact ⟨F i j,(hL i j).continuous⟩
  let S (i : I) := closure (range (G i))
  have hc (i : I) : IsCompact (S i) := real_bounded_lipschitz_compact (G i) (B i) (L i) (hb i) (hL i)
  let (i : I) : CompactSpace (S i) := isCompact_iff_compactSpace.mp (hc i)
  let seq : ℕ → ∀ i, S i := fun j i ↦ ⟨G i j,subset_closure (mem_range_self j)⟩
  obtain ⟨f,_,nu,hnu,ht⟩ := (isCompact_univ : IsCompact (univ : Set (∀ i, S i))).tendsto_subseq
    (fun _ ↦ mem_univ _ : ∀ j, seq j ∈ univ)
  refine ⟨fun i ↦ (f i).val,fun i ↦ (f i).val.continuous,nu,hnu,?_⟩
  intro i
  have hi := ((continuous_subtype_val.comp (continuous_apply i)).tendsto f).comp ht
  exact BoundedContinuousFunction.tendsto_iff_tendstoUniformly.mp hi

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_RealFiniteBallJetSubsequenceLemmas
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Yau.Geometry

open Yau.Analysis Set Metric Filter
open scoped Topology NNReal ContDiff

theorem real_jet_ball_subsequence (W : ℕ → Yau.Jets.Coord → ℝ)
    (hW : ∀ j, ContDiff ℝ ∞ (W j))
    (hb : ∀ R n : ℕ, ∃ B ≥ 0, ∀ j (ds : List (Fin 4)), ds.length ≤ n →
      ∀ x ∈ closedBall (0 : Yau.Jets.Coord) (R:ℝ), |partialJet (W j) ds x| ≤ B) :
    ∃ f : ∀ R : ℕ, List (Fin 4) → closedBall (0 : Yau.Jets.Coord) (R:ℝ) → ℝ,
      (∀ R ds, Continuous (f R ds)) ∧ ∃ nu : ℕ → ℕ, StrictMono nu ∧ ∀ (R : ℕ) (ds : List (Fin 4)),
        TendstoUniformly (fun j (x : closedBall (0 : Yau.Jets.Coord) (R:ℝ)) ↦
          partialJet (W (nu j)) ds x) (f R ds) atTop := by
  choose B hB hbound using hb
  let X (i : ℕ × List (Fin 4)) := closedBall (0 : Yau.Jets.Coord) (i.1:ℝ)
  let F (i : ℕ × List (Fin 4)) (j : ℕ) (x : X i) := partialJet (W j) i.2 x
  let C (i : ℕ × List (Fin 4)) : ℝ≥0 := ⟨B i.1 (i.2.length+1),hB _ _⟩
  have hval (i : ℕ × List (Fin 4)) (j : ℕ) (x : X i) : |F i j x| ≤ (C i:ℝ) :=
    hbound _ _ j _ (by omega) x x.property
  have hLip (i : ℕ × List (Fin 4)) (j : ℕ) : LipschitzWith (4*C i) (F i j) := by
    apply LipschitzOnWith.to_restrict
    apply real_partialJet_lipschitz (W j) (hW j) i.2 0 (i.1:ℝ) (C i)
    intro k x hx
    exact hbound _ _ j _ (by simp) x hx
  obtain ⟨f,hf,nu,hnu,ht⟩ := real_countable_uniform_subsequence F (fun i ↦ (C i:ℝ))
    (fun i ↦ 4*C i) hval hLip
  exact ⟨fun R ds ↦ f (R,ds),fun R ds ↦ hf (R,ds),nu,hnu,fun R ds ↦ ht (R,ds)⟩

end Yau.Geometry

end

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_RealCompatibleBallLimits
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Set Metric Filter
open scoped Topology
noncomputable section

theorem real_compatible_ball_limits (W : ℕ → Yau.Jets.Coord → ℝ)
    (hW : ∀ j, Continuous (W j))
    (f : ∀ R : ℕ, closedBall (0 : Yau.Jets.Coord) (R:ℝ) → ℝ)
    (ht : ∀ R : ℕ, TendstoUniformly (fun j (x : closedBall (0 : Yau.Jets.Coord) (R:ℝ)) ↦ W j x)
      (f R) atTop) :
    ∃ g : Yau.Jets.Coord → ℝ, Continuous g ∧
      ∀ Q : Set Yau.Jets.Coord, IsCompact Q → TendstoUniformlyOn W g atTop Q := by
  choose R hR using (fun x : Yau.Jets.Coord ↦ exists_nat_gt ‖x‖)
  have hx (x : Yau.Jets.Coord) : x ∈ closedBall (0 : Yau.Jets.Coord) (R x:ℝ) := by
    simpa only [mem_closedBall,dist_zero_right] using (hR x).le
  let g (x : Yau.Jets.Coord) : ℝ := f (R x) ⟨x,hx x⟩
  have he (n : ℕ) (x : closedBall (0 : Yau.Jets.Coord) (n:ℝ)) : f n x = g x :=
    tendsto_nhds_unique ((ht n).tendsto_at x) ((ht (R x)).tendsto_at ⟨x,hx x⟩)
  have hu (n : ℕ) : TendstoUniformlyOn W g atTop (closedBall (0 : Yau.Jets.Coord) (n:ℝ)) := by
    rw [tendstoUniformlyOn_iff_restrict]
    have heq : f n = fun x : closedBall (0 : Yau.Jets.Coord) (n:ℝ) ↦ g x := funext (he n)
    change TendstoUniformly (fun j (x : closedBall (0 : Yau.Jets.Coord) (n:ℝ)) ↦ W j x)
      (fun x ↦ g x) atTop
    rw [← heq]
    exact ht n
  have hc : Continuous g := by
    rw [continuous_iff_continuousAt]
    intro x
    have hcont := (hu (R x)).continuousOn (Filter.Eventually.frequently (Filter.Eventually.of_forall (fun j ↦ (hW j).continuousOn)))
    exact hcont.continuousAt (closedBall_mem_nhds_of_mem (by
      simpa only [mem_ball,dist_zero_right] using hR x))
  refine ⟨g,hc,?_⟩
  intro Q hQ
  obtain ⟨r,hr⟩ := hQ.isBounded.subset_closedBall (0 : Yau.Jets.Coord)
  obtain ⟨n,hn⟩ := exists_nat_gt r
  exact (hu n).mono (hr.trans (closedBall_subset_closedBall hn.le))

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_RealLocalJetLimits
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Yau.Analysis Set Metric Filter
open scoped Topology ContDiff
noncomputable section

theorem real_local_jet_limits (W : ℕ → Yau.Jets.Coord → ℝ)
    (hW : ∀ j, ContDiff ℝ ∞ (W j))
    (hb : ∀ R n : ℕ, ∃ B ≥ 0, ∀ j (ds : List (Fin 4)), ds.length ≤ n →
      ∀ x ∈ closedBall (0 : Yau.Jets.Coord) (R:ℝ), |partialJet (W j) ds x| ≤ B) :
    ∃ g : List (Fin 4) → Yau.Jets.Coord → ℝ, (∀ ds, Continuous (g ds)) ∧
      ∃ nu : ℕ → ℕ, StrictMono nu ∧ ∀ ds (Q : Set Yau.Jets.Coord), IsCompact Q →
        TendstoUniformlyOn (fun j ↦ partialJet (W (nu j)) ds) (g ds) atTop Q := by
  obtain ⟨f,_,nu,hnu,ht⟩ := real_jet_ball_subsequence W hW hb
  have hh (ds : List (Fin 4)) := real_compatible_ball_limits
    (fun j ↦ partialJet (W (nu j)) ds) (fun j ↦ (partialJet_smooth _ (hW _) ds).continuous)
    (fun R ↦ f R ds) (fun R ↦ ht R ds)
  choose g hg hconv using hh
  exact ⟨g,hg,nu,hnu,hconv⟩

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_RealSmoothLocalCompactness
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Yau.Analysis Set Metric Filter
open scoped Topology ContDiff
noncomputable section

theorem real_smooth_local_subsequence (W : ℕ → Yau.Jets.Coord → ℝ)
    (hW : ∀ j, ContDiff ℝ ∞ (W j))
    (hb : ∀ R n : ℕ, ∃ B ≥ 0, ∀ j (ds : List (Fin 4)), ds.length ≤ n →
      ∀ x ∈ closedBall (0 : Yau.Jets.Coord) (R:ℝ), |partialJet (W j) ds x| ≤ B) :
    ∃ v : Yau.Jets.Coord → ℝ, ContDiff ℝ ∞ v ∧ ∃ nu : ℕ → ℕ, StrictMono nu ∧
      (∀ ds (Q : Set Yau.Jets.Coord), IsCompact Q →
        TendstoUniformlyOn (fun j ↦ partialJet (W (nu j)) ds) (partialJet v ds) atTop Q) ∧
      (∀ n (Q : Set Yau.Jets.Coord), IsCompact Q →
        TendstoUniformlyOn (fun j ↦ iteratedFDeriv ℝ n (W (nu j)))
          (iteratedFDeriv ℝ n v) atTop Q) := by
  obtain ⟨g,hg,nu,hnu,ht⟩ := real_local_jet_limits W hW hb
  have hd := real_jet_limit_hasFDerivAt (fun j ↦ W (nu j)) (fun j ↦ hW (nu j)) g ht
  have hs := real_jet_limit_smooth g hg hd
  have hi := real_jet_limit_identification g hd
  have hu (ds : List (Fin 4)) (Q : Set Yau.Jets.Coord) (hQ : IsCompact Q) :
      TendstoUniformlyOn (fun j ↦ partialJet (W (nu j)) ds) (partialJet (g []) ds) atTop Q := by
    rw [hi ds]
    exact ht ds Q hQ
  refine ⟨g [],hs [],nu,hnu,hu,?_⟩
  intro n Q hQ
  exact real_uniform_iteratedFDeriv (fun j ↦ W (nu j)) (g []) (fun j ↦ hW (nu j)) (hs []) n Q
    (fun ds _ ↦ hu ds Q hQ)

end
end Yau.Geometry

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
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_RealAllWeakJetsSmooth
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau
open MeasureTheory Set Filter Metric Yau.Analysis Yau.Geometry
open scoped ContDiff Convolution Topology
noncomputable section

theorem real_all_weak_jets_smooth {K L : Set Jets.Coord}
    (hK : IsCompact K) (hL : IsCompact L) (hKL : K ⊆ interior L)
    (u : Jets.Coord → ℝ)
    (hall : ∀ N : ℕ, ∃ U : List (Fin 4) → Jets.Coord → ℝ,
      U []=u ∧
      (∀ es, es.length ≤ N → MemLp (U es) 2 volume ∧ tsupport (U es) ⊆ K) ∧
      ∀ es, es.length < N → ∀ i psi,
        ContDiff ℝ ∞ psi → HasCompactSupport psi →
        (∫ x, U es x*coordPartial psi x i)=-(∫ x, U (i::es) x*psi x)) :
    ∃ v : Jets.Coord → ℝ, ContDiff ℝ ∞ v ∧ tsupport v ⊆ L ∧ v =ᵐ[volume] u := by
  obtain ⟨U₀,hzero₀,hU₀,_⟩ := hall 0
  have hu : MemLp u 2 volume := hzero₀ ▸ (hU₀ [] (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).1
  have hsu : tsupport u ⊆ K := hzero₀ ▸ (hU₀ [] (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).2
  have hcu : HasCompactSupport u := hK.of_isClosed_subset (isClosed_tsupport _) hsu
  obtain ⟨r,hr,hsupport⟩ := real_compact_mollifier_support hK hKL
  let b : ℕ → ContDiffBump (0 : Jets.Coord) := realMollifierBump r hr
  let w : ℕ → Jets.Coord → ℝ := fun j ↦ u ⋆ (b j).normed volume
  have hw (j : ℕ) : ContDiff ℝ ∞ (w j) :=
    (b j).hasCompactSupport_normed.contDiff_convolution_right
      (ContinuousLinearMap.lsmul ℝ ℝ) (hu.locallyIntegrable (by norm_num)) (b j).contDiff_normed
  have hc (j : ℕ) : HasCompactSupport (w j) :=
    hcu.convolution (ContinuousLinearMap.lsmul ℝ ℝ) (b j).hasCompactSupport_normed
  have hs (j : ℕ) : tsupport (w j) ⊆ L := hsupport u hsu j
  have hb : ∀ R n : ℕ, ∃ B ≥ 0, ∀ j (ds : List (Fin 4)), ds.length ≤ n →
      ∀ x ∈ closedBall (0 : Jets.Coord) (R:ℝ), |partialJet (w j) ds x| ≤ B := by
    intro R n
    obtain ⟨U,hzero,hU,hweak⟩ := hall (n+4)
    let E : List (Fin 4) → ℝ := fun es ↦ ∫ x, (U es x)^2
    let D : ℝ := 256 * ∑ k ∈ Finset.range (n+5), ∑ a : Fin k → Fin 4, E (List.ofFn a)
    have hD : 0 ≤ D := mul_nonneg (by norm_num)
      (Finset.sum_nonneg (fun _ _ ↦ Finset.sum_nonneg (fun _ _ ↦ integral_nonneg (fun _ ↦ sq_nonneg _))))
    refine ⟨Real.sqrt D,Real.sqrt_nonneg D,fun j ds hd x _ ↦ ?_⟩
    have hj (es : List (Fin 4)) (he : es.length ≤ n+4) :
        (∫ x, (partialJet (w j) es x)^2) ≤ E es := by
      have hid := real_weak_jet_convolution U (n+4)
        (fun es he ↦ (hU es he).1.locallyIntegrable (by norm_num)) hweak
        ((b j).normed volume) (b j).contDiff_normed (b j).hasCompactSupport_normed es he
      rw [hzero] at hid
      change (∫ x, (partialJet (u ⋆ (b j).normed volume) es x)^2) ≤ E es
      rw [hid]
      exact real_normed_convolution_square_le (U es) (hU es he).1
        (hK.of_isClosed_subset (isClosed_tsupport _) (hU es he).2) (b j)
    have hbound := real_global_jet_l2_embedding (w j) (hw j) (hc j) n E hj ds hd x
    change (partialJet (w j) ds x)^2 ≤ D at hbound
    nlinarith [Real.sq_sqrt hD, abs_nonneg (partialJet (w j) ds x),
      sq_abs (partialJet (w j) ds x), Real.sqrt_nonneg D]
  obtain ⟨v,hv,nu,hnu,ht,_⟩ := real_smooth_local_subsequence w hw hb
  have hp (x : Jets.Coord) : Tendsto (fun j ↦ w (nu j) x) atTop (𝓝 (v x)) :=
    (ht [] {x} (isCompact_singleton)).tendsto_at (mem_singleton x)
  have hsv : tsupport v ⊆ L := by
    apply closure_minimal _ hL.isClosed
    intro x hx
    by_contra hn
    have hz (j : ℕ) : w (nu j) x=0 := image_eq_zero_of_notMem_tsupport (fun hh ↦ hn (hs (nu j) hh))
    have he : v x=0 := tendsto_nhds_unique (hp x) (by simpa only [hz] using tendsto_const_nhds)
    exact hx he
  have hl := (real_compact_convolution_L2_tendsto u hu hcu b
    (realMollifierBump_radius_tendsto r hr)).comp hnu.tendsto_atTop
  refine ⟨v,hv,hsv,?_⟩
  exact real_L2_pointwise_limit_ae (fun j ↦ w (nu j))
    (fun j ↦ real_compact_continuous_memLp _ (hw (nu j)).continuous (hc (nu j))) u v hu hl hp

end
end Yau

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_RealBallCubeContainmentLemmas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Yau

open Set Metric

open Filter
open scoped Topology

open MeasureTheory Set
open scoped ContDiff

theorem realCenteredCube_subset_interior {n : ℕ} {r R : ℝ} (hr : r < R) :
    realCenteredCube n r ⊆ interior (realCenteredCube n R) := by
  let U : Set (Coord n) := univ.pi (fun _ ↦ Ioo (-R) R)
  have ho : IsOpen U := isOpen_set_pi finite_univ (fun _ _ ↦ isOpen_Ioo)
  have hi : U ⊆ realCenteredCube n R := by
    intro x hx j hj
    exact ⟨(hx j hj).1.le,(hx j hj).2.le⟩
  intro x hx
  apply (interior_maximal hi ho)
  intro j hj
  exact ⟨lt_of_lt_of_le (neg_lt_neg hr) (hx j hj).1,lt_of_le_of_lt (hx j hj).2 hr⟩

end Yau

end

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_RealCubeCutoffs
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau
open Set Filter
open scoped ContDiff Topology
noncomputable section

theorem real_cube_smooth_cutoff (r R : ℝ) (h : r < R) :
    ∃ eta : Jets.Coord → ℝ, ContDiff ℝ ∞ eta ∧ HasCompactSupport eta ∧
      tsupport eta ⊆ realCenteredCube 4 R ∧ (∀ x, 0 ≤ eta x ∧ eta x ≤ 1) ∧
      ∀ x ∈ realCenteredCube 4 r, eta =ᶠ[𝓝 x] (fun _ ↦ 1) := by
  let U : Set Jets.Coord := univ.pi (fun _ ↦ Ioo (-R) R)
  have ho : IsOpen U := isOpen_set_pi finite_univ (fun _ _ ↦ isOpen_Ioo)
  have hi : realCenteredCube 4 r ⊆ U := by
    intro x hx j hj
    have ha := hx j hj
    exact ⟨lt_of_lt_of_le (neg_lt_neg h) ha.1,lt_of_le_of_lt ha.2 h⟩
  obtain ⟨eta,he,hc,hs,hb,h1⟩ := Yau.Geometry.compact_smooth_cutoff (realCenteredCube_isCompact 4 r) ho hi
  refine ⟨eta,he,hc,hs.trans ?_,hb,h1⟩
  intro x hx j hj
  exact ⟨(hx j hj).1.le,(hx j hj).2.le⟩

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
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_RealInteriorWeakRestrictionLemmas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Yau

open MeasureTheory Set
open scoped ContDiff

theorem real_interior_weak_restrict {n : ℕ} {K L : Set (Coord n)}
    (hK : IsCompact K) (hL : MeasurableSet L) (hsub : K ⊆ L)
    (u g : Coord n → ℝ) (hu : MemLp u 2 (volume.restrict L))
    (hg : MemLp g 2 (volume.restrict L)) (i : Fin n)
    (hweak : ∀ psi : Coord n → ℝ, ContDiff ℝ ∞ psi → HasCompactSupport psi → tsupport psi ⊆ L →
      (∫ x in L, u x*coordPartial psi x i)=-(∫ x in L, g x*psi x)) :
    MemLp u 2 (volume.restrict K) ∧ MemLp g 2 (volume.restrict K) ∧
    ∀ psi : Coord n → ℝ, ContDiff ℝ ∞ psi → HasCompactSupport psi → tsupport psi ⊆ K →
      IntegrableOn (fun x ↦ u x*coordPartial psi x i) K ∧
      IntegrableOn (fun x ↦ g x*psi x) K ∧
      (∫ x in K, u x*coordPartial psi x i)=-(∫ x in K, g x*psi x) := by
  have huK := hu.mono_measure (Measure.restrict_mono hsub le_rfl)
  have hgK := hg.mono_measure (Measure.restrict_mono hsub le_rfl)
  refine ⟨huK,hgK,fun psi hp hc hs ↦ ?_⟩
  have ht := real_continuous_memLp_compact hK psi hp.continuous
  have hdt := real_continuous_memLp_compact hK _ (real_coordPartial_smooth psi hp i).continuous
  have h := hweak psi hp hc (hs.trans hsub)
  have he1 : (∫ x in L, u x*coordPartial psi x i)=∫ x in K, u x*coordPartial psi x i := by
    apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hL hsub
    intro x hx
    rw [image_eq_zero_of_notMem_tsupport (f := fun y ↦ coordPartial psi y i)
      (fun ht ↦ hx.2 (hs (tsupport_fderiv_apply_subset ℝ (Pi.single i 1) ht))),mul_zero]
  have he2 : (∫ x in L, g x*psi x)=∫ x in K, g x*psi x := by
    apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hL hsub
    intro x hx
    rw [image_eq_zero_of_notMem_tsupport (fun ht ↦ hx.2 (hs ht)),mul_zero]
  rw [he1,he2] at h
  exact ⟨huK.integrable_mul hdt,hgK.integrable_mul ht,h⟩

end Yau

end

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
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_RealLocalSmoothDerivativeLemmas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Yau

open MeasureTheory Set
open scoped ContDiff

theorem real_local_smooth_derivative_ae {n : ℕ} {Q : Set (Coord n)} (hQ : IsCompact Q)
    (u g v : Coord n → ℝ) (_ : MemLp u 2 (volume.restrict Q))
    (hg : MemLp g 2 (volume.restrict Q)) (hv : ContDiff ℝ ∞ v)
    (ha : v =ᵐ[volume.restrict Q] u) (i : Fin n)
    (hw : ∀ psi : Coord n → ℝ, ContDiff ℝ ∞ psi → HasCompactSupport psi → tsupport psi ⊆ Q →
      (∫ x in Q, u x*coordPartial psi x i)=-(∫ x in Q, g x*psi x)) :
    (fun x ↦ coordPartial v x i) =ᵐ[volume.restrict (interior Q)] g := by
  apply real_interior_L2_eq_of_test_pairings hQ _ g
    (real_continuous_memLp_compact hQ _ (real_coordPartial_smooth v hv i).continuous) hg
  intro psi hp hc hs
  rw [(real_compact_test_derivative v psi hv hp hc i Q hs).2.2]
  have he : (∫ x in Q, v x*coordPartial psi x i)=(∫ x in Q, u x*coordPartial psi x i) :=
    integral_congr_ae (ha.mul Filter.EventuallyEq.rfl)
  rw [he,hw psi hp hc hs,neg_neg]

theorem real_smooth_divergence_equation {n : ℕ} {Q : Set (Coord n)} (hQ : IsCompact Q)
    (G : Fin n → Fin n → Coord n → ℝ) (hG : ∀ a j, ContDiff ℝ ∞ (G a j))
    (F : Coord n → ℝ) (hF : ContDiff ℝ ∞ F)
    (hw : ∀ psi : Coord n → ℝ, ContDiff ℝ ∞ psi → HasCompactSupport psi → tsupport psi ⊆ Q →
      (∑ a, ∑ j, ∫ x in Q, G a j x*coordPartial psi x j)=∫ x in Q, F x*psi x) :
    ∀ x ∈ interior Q, -(∑ a, ∑ j, coordPartial (G a j) x j)=F x := by
  let D : Coord n → ℝ := fun x ↦ -(∑ a, ∑ j, coordPartial (G a j) x j)
  have hD : ContDiff ℝ ∞ D :=
    (ContDiff.sum (fun a _ ↦ ContDiff.sum (fun j _ ↦ real_coordPartial_smooth _ (hG a j) j))).neg
  have ha : D =ᵐ[volume.restrict (interior Q)] F := by
    apply real_interior_L2_eq_of_test_pairings hQ D F
      (real_continuous_memLp_compact hQ D hD.continuous)
      (real_continuous_memLp_compact hQ F hF.continuous)
    intro psi hp hc hs
    have hi (a j : Fin n) : IntegrableOn (fun x ↦ coordPartial (G a j) x j*psi x) Q :=
      (real_compact_test_derivative (G a j) psi (hG a j) hp hc j Q hs).1.integrableOn
    have hid : (fun x ↦ D x*psi x)=fun x ↦ -(∑ a, ∑ j, coordPartial (G a j) x j*psi x) := by
      funext x
      simp only [D,neg_mul,Finset.sum_mul]
    rw [hid,integral_neg,integral_finsetSum _ (fun a _ ↦ integrable_finsetSum _ (fun j _ ↦ hi a j))]
    simp_rw [integral_finsetSum _ (fun j _ ↦ hi _ j)]
    simp_rw [(real_compact_test_derivative _ psi (hG _ _) hp hc _ Q hs).2.2]
    simp only [Finset.sum_neg_distrib,neg_neg]
    exact hw psi hp hc hs
  exact Measure.eqOn_open_of_ae_eq ha isOpen_interior hD.continuous.continuousOn hF.continuous.continuousOn

end Yau

end

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_RealLocalWeakJetsSmooth
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

theorem real_local_weak_jets_smooth {Q L : Set Jets.Coord}
    (hQ : IsCompact Q) (hL : IsCompact L)
    (eta : Jets.Coord → ℝ) (he : ContDiff ℝ ∞ eta) (hc : HasCompactSupport eta)
    (hs : tsupport eta ⊆ interior Q) (hLeta : tsupport eta ⊆ interior L)
    (u : Jets.Coord → ℝ)
    (hall : ∀ N : ℕ, ∃ U : List (Fin 4) → Jets.Coord → ℝ,
      U []=u ∧
      (∀ es, es.length ≤ N+1 → MemLp (U es) 2 (volume.restrict Q)) ∧
      ∀ es, es.length ≤ N → ∀ i psi,
        ContDiff ℝ ∞ psi → HasCompactSupport psi → tsupport psi ⊆ Q →
        (∫ x in Q, U es x*coordPartial psi x i)=-(∫ x in Q, U (i::es) x*psi x)) :
    ∃ v : Jets.Coord → ℝ, ContDiff ℝ ∞ v ∧ tsupport v ⊆ L ∧
      v =ᵐ[volume] (fun x ↦ eta x*u x) := by
  apply real_all_weak_jets_smooth hc hL hLeta
  intro N
  obtain ⟨U,hzero,hU,hw⟩ := hall N
  have h := real_cutoff_finite_weak_jet hQ eta he hc hs U N hU hw
  refine ⟨realWeakJetExpansion eta U [],?_,h.1,?_⟩
  · funext x
    simp only [realWeakJetExpansion,realJetErrorTerms,realWeakJetProductSum,
      List.append_nil,List.map_nil,List.sum_nil,add_zero,hzero]
  · intro es hh i psi hp hc
    exact (h.2 es hh i psi hp hc).2.2

end
end Yau

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_RealWeakEquationRestriction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau
open MeasureTheory Set
open scoped ContDiff
noncomputable section

theorem real_weak_equation_restrict {n : ℕ} {Q L : Set (Coord n)}
    (hL : MeasurableSet L) (hsub : Q ⊆ L)
    (C : Coord n → Fin n → Fin n → ℝ) (U : Fin n → Coord n → ℝ) (F : Coord n → ℝ)
    (heq : ∀ psi, ContDiff ℝ ∞ psi → HasCompactSupport psi → tsupport psi ⊆ L →
      (∑ a, ∑ j, ∫ x in L, C x a j*U a x*coordPartial psi x j)=∫ x in L, F x*psi x)
    (psi : Coord n → ℝ) (hp : ContDiff ℝ ∞ psi)
    (hc : HasCompactSupport psi) (hs : tsupport psi ⊆ Q) :
    (∑ a, ∑ j, ∫ x in Q, C x a j*U a x*coordPartial psi x j)=∫ x in Q, F x*psi x := by
  have h := heq psi hp hc (hs.trans hsub)
  have hflux (a j : Fin n) : (∫ x in L, C x a j*U a x*coordPartial psi x j)=
      ∫ x in Q, C x a j*U a x*coordPartial psi x j := by
    apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hL hsub
    intro x hx
    rw [image_eq_zero_of_notMem_tsupport (f := fun y ↦ coordPartial psi y j)
      (fun ht ↦ hx.2 (hs (tsupport_fderiv_apply_subset ℝ (Pi.single j 1) ht))),mul_zero]
  have hscalar : (∫ x in L, F x*psi x)=∫ x in Q, F x*psi x := by
    apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hL hsub
    intro x hx
    rw [image_eq_zero_of_notMem_tsupport (fun ht ↦ hx.2 (hs ht)),mul_zero]
  simpa only [hflux,hscalar] using h

end
end Yau

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Spectral_SphereEigenSmoothRepresentative
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open MeasureTheory Set Yau.Geometry
open scoped ContDiff Topology
noncomputable section

theorem sphere_eigen_cutoff_smooth (d : SphereEnergyData) (p : Base)
    (hrho : ContDiff ℝ ∞ (fun x ↦ d.density (sphereChartCoordMap p x)))
    (mu : ℝ) (hmu : mu ≠ 0)
    (eta : Yau.Jets.Coord → ℝ) (he : ContDiff ℝ ∞ eta) (hc : HasCompactSupport eta)
    (hs : tsupport eta ⊆ interior (Yau.realCenteredCube 4 (1/16)))
    (f : SphereWeightedL2 d) (heigen : sphereL2Resolvent d f=mu • f) :
    ∃ v : Yau.Jets.Coord → ℝ, ContDiff ℝ ∞ v ∧
      tsupport v ⊆ Yau.realCenteredCube 4 (1/8) ∧
      v =ᵐ[volume] (fun x ↦ eta x*(sphereL2Resolvent d f) (sphereChartCoordMap p x)) := by
  apply Yau.real_local_weak_jets_smooth
    (Yau.realCenteredCube_isCompact 4 (1/16)) (Yau.realCenteredCube_isCompact 4 (1/8))
    eta he hc hs (hs.trans (interior_subset.trans (Yau.realCenteredCube_subset_interior (by norm_num))))
  intro N
  obtain ⟨K,hK,h⟩ := sphere_eigen_all_finite_weak_jets d p hrho mu hmu N
  obtain ⟨U,hzero,hone,hU,hw,hpde⟩ := h f heigen
  refine ⟨U,hzero,fun es hh ↦ (hU es (by omega)).1,?_⟩
  intro es hh i psi hp hc hs
  exact (hw es (by omega) i psi hp hc hs).2.2

theorem sphere_eigen_smooth_representative (d : SphereEnergyData) (p : Base)
    (hrho : ContDiff ℝ ∞ (fun x ↦ d.density (sphereChartCoordMap p x)))
    (mu : ℝ) (hmu : mu ≠ 0)
    (f : SphereWeightedL2 d) (heigen : sphereL2Resolvent d f=mu • f) :
    ∃ v : Yau.Jets.Coord → ℝ, ContDiff ℝ ∞ v ∧
      tsupport v ⊆ Yau.realCenteredCube 4 (1/8) ∧
      v =ᵐ[volume.restrict (Yau.realCenteredCube 4 (1/32))]
        (fun x ↦ (sphereL2Resolvent d f) (sphereChartCoordMap p x)) := by
  obtain ⟨eta,he,hc,hs,hb,h1⟩ := Yau.real_cube_smooth_cutoff (1/32) (3/64) (by norm_num)
  obtain ⟨v,hv,hsv,ha⟩ := sphere_eigen_cutoff_smooth d p hrho mu hmu eta he hc
    (hs.trans (Yau.realCenteredCube_subset_interior (by norm_num))) f heigen
  refine ⟨v,hv,hsv,?_⟩
  filter_upwards [ae_restrict_of_ae ha,
    self_mem_ae_restrict (Yau.realCenteredCube_isCompact 4 (1/32)).measurableSet] with x hx hxQ
  rw [hx,(h1 x hxQ).eq_of_nhds,one_mul]

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Spectral_SphereEigenClassicalEquation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open MeasureTheory Set Yau.Geometry Yau.Analysis
open scoped ContDiff
noncomputable section

theorem sphere_eigen_smooth_gradient (d : SphereEnergyData) (p : Base)
    (hrho : ContDiff ℝ ∞ (fun x ↦ d.density (sphereChartCoordMap p x)))
    (mu : ℝ) (hmu : mu ≠ 0)
    (f : SphereWeightedL2 d) (heigen : sphereL2Resolvent d f=mu • f)
    (v : Yau.Jets.Coord → ℝ) (hv : ContDiff ℝ ∞ v)
    (ha : v =ᵐ[volume.restrict (Yau.realCenteredCube 4 (1/32))]
      (fun x ↦ (sphereL2Resolvent d f) (sphereChartCoordMap p x))) (i : Fin 4) :
    (fun x ↦ Yau.coordPartial v x i) =ᵐ[volume.restrict (Yau.realCenteredCube 4 (1/64))]
      (sphereChartDerivativeMap d p i (sphereWeakSolution d f) : Yau.Jets.Coord → ℝ) := by
  obtain ⟨K,hK,hjet⟩ := sphere_eigen_all_finite_weak_jets d p hrho mu hmu 0
  obtain ⟨U,hzero,hone,hU,hw,hpde⟩ := hjet f heigen
  have h := Yau.real_interior_weak_restrict
    (Yau.realCenteredCube_isCompact 4 (1/32))
    (Yau.realCenteredCube_isCompact 4 (1/16)).measurableSet
    (Yau.realCenteredCube_mono (by norm_num))
    (U []) (U [i]) (hU [] (by simp)).1 (hU [i] (by simp)).1 i
    (fun psi hp hc hs ↦ (hw [] (by simp) i psi hp hc hs).2.2)
  have haU : v =ᵐ[volume.restrict (Yau.realCenteredCube 4 (1/32))] U [] := by rw [hzero]; exact ha
  have hid := Yau.real_local_smooth_derivative_ae
    (Yau.realCenteredCube_isCompact 4 (1/32)) (U []) (U [i]) v h.1 h.2.1 hv haU i
    (fun psi hp hc hs ↦ (h.2.2 psi hp hc hs).2.2)
  rw [hone i] at hid
  exact ae_mono (Measure.restrict_mono (Yau.realCenteredCube_subset_interior (by norm_num)) le_rfl) hid

theorem sphere_eigen_classical_equation (d : SphereEnergyData) (p : Base)
    (hrho : ContDiff ℝ ∞ (fun x ↦ d.density (sphereChartCoordMap p x)))
    (mu : ℝ) (hmu : mu ≠ 0)
    (f : SphereWeightedL2 d) (heigen : sphereL2Resolvent d f=mu • f)
    (v : Yau.Jets.Coord → ℝ) (hv : ContDiff ℝ ∞ v)
    (ha : v =ᵐ[volume.restrict (Yau.realCenteredCube 4 (1/32))]
      (fun x ↦ (sphereL2Resolvent d f) (sphereChartCoordMap p x))) :
    ∀ x ∈ interior (Yau.realCenteredCube 4 (1/64)),
      -(∑ a, ∑ j, Yau.coordPartial
        (fun y ↦ sphereChartPrincipalDensity d p y a j*Yau.coordPartial v y a) x j)=
        sphereEigenForcingCoefficient d p mu x*v x := by
  obtain ⟨K,hK,hjet⟩ := sphere_eigen_all_finite_weak_jets d p hrho mu hmu 0
  obtain ⟨U,hzero,hone,hU,hw,hpde⟩ := hjet f heigen
  let Q := Yau.realCenteredCube 4 (1/64)
  have hgrad (a : Fin 4) : (fun x ↦ Yau.coordPartial v x a) =ᵐ[volume.restrict Q] U [a] := by
    rw [hone a]
    exact sphere_eigen_smooth_gradient d p hrho mu hmu f heigen v hv ha a
  have hvalue : v =ᵐ[volume.restrict Q] U [] := by
    rw [hzero]
    exact ae_mono (Measure.restrict_mono (Yau.realCenteredCube_mono (by norm_num)) le_rfl) ha
  have hB : ContDiff ℝ ∞ (sphereEigenForcingCoefficient d p mu) :=
    contDiff_const.mul (roundCoordDensity_smooth.mul hrho)
  apply Yau.real_smooth_divergence_equation (Yau.realCenteredCube_isCompact 4 (1/64))
    (fun a j y ↦ sphereChartPrincipalDensity d p y a j*Yau.coordPartial v y a)
    (fun a j ↦ (sphereChartPrincipalDensity_smooth d p a j).mul (Yau.real_coordPartial_smooth v hv a))
    (fun x ↦ sphereEigenForcingCoefficient d p mu x*v x) (hB.mul hv)
  intro psi hp hc hs
  have heq := Yau.real_weak_equation_restrict
    (Yau.realCenteredCube_isCompact 4 (1/16)).measurableSet
    (show Q ⊆ Yau.realCenteredCube 4 (1/16) from Yau.realCenteredCube_mono (by norm_num))
    (sphereChartPrincipalDensity d p) (fun a ↦ U [a])
    (fun x ↦ sphereEigenForcingCoefficient d p mu x*U [] x) hpde psi hp hc hs
  calc
    _ = ∑ a, ∑ j, ∫ x in Q,
        sphereChartPrincipalDensity d p x a j*U [a] x*Yau.coordPartial psi x j := by
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro j _
      apply integral_congr_ae
      filter_upwards [hgrad a] with x hx
      rw [hx]
    _ = ∫ x in Q, sphereEigenForcingCoefficient d p mu x*U [] x*psi x := heq
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [hvalue] with x hx
      rw [hx]

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Spectral_SphereEigenMatrixEquation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open MeasureTheory Set Yau.Geometry
open scoped ContDiff
noncomputable section

theorem sphere_eigen_matrix_equation (d : SphereEnergyData) (p : Base)
    (hrho : ContDiff ℝ ∞ (fun x ↦ d.density (sphereChartCoordMap p x)))
    (mu : ℝ) (hmu : mu ≠ 0)
    (f : SphereWeightedL2 d) (heigen : sphereL2Resolvent d f=mu • f)
    (v : Yau.Jets.Coord → ℝ) (hv : ContDiff ℝ ∞ v)
    (ha : v =ᵐ[volume.restrict (Yau.realCenteredCube 4 (1/32))]
      (fun x ↦ (sphereL2Resolvent d f) (sphereChartCoordMap p x))) :
    ∀ x ∈ interior (Yau.realCenteredCube 4 (1/64)),
      Yau.coordDiv (realMatrixFlux (sphereChartPrincipalDensity d p) v) x+
        sphereEigenForcingCoefficient d p mu x*v x=0 := by
  intro x hx
  have he := sphere_eigen_classical_equation d p hrho mu hmu f heigen v hv ha x hx
  have hid : Yau.coordDiv (realMatrixFlux (sphereChartPrincipalDensity d p) v) x =
      ∑ a, ∑ j, Yau.coordPartial
        (fun y ↦ sphereChartPrincipalDensity d p y a j*Yau.coordPartial v y a) x j := by
    unfold Yau.coordDiv realMatrixFlux
    simp_rw [Yau.real_coordPartial_sum _ (fun a ↦
      (sphereChartPrincipalDensity_smooth d p _ a).mul (Yau.real_coordPartial_smooth v hv a))]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro j _
    congr 1
    funext y
    rw [sphereChartPrincipalDensity_symmetric d p y j a]
  rw [hid]
  linarith only [he]

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Spectral_SphereEigenDirectRepresentative
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open MeasureTheory Set Yau.Geometry
open scoped ContDiff
noncomputable section

theorem sphere_eigen_rescaled_input (d : SphereEnergyData) (mu : ℝ) (hmu : mu ≠ 0)
    (f : SphereWeightedL2 d) (heigen : sphereL2Resolvent d f=mu • f) :
    sphereL2Resolvent d (mu⁻¹ • f)=f ∧
      sphereL2Resolvent d (mu⁻¹ • f)=mu • (mu⁻¹ • f) := by
  have hr : sphereL2Resolvent d (mu⁻¹ • f)=f := by
    rw [map_smul,heigen,smul_smul,inv_mul_cancel₀ hmu,one_smul]
  refine ⟨hr,?_⟩
  rw [hr,smul_smul,mul_inv_cancel₀ hmu,one_smul]

theorem sphere_eigen_direct_matrix_equation (d : SphereEnergyData) (p : Base)
    (hrho : ContDiff ℝ ∞ (fun x ↦ d.density (sphereChartCoordMap p x)))
    (mu : ℝ) (hmu : mu ≠ 0)
    (f : SphereWeightedL2 d) (heigen : sphereL2Resolvent d f=mu • f)
    (v : Yau.Jets.Coord → ℝ) (hv : ContDiff ℝ ∞ v)
    (ha : v =ᵐ[volume.restrict (Yau.realCenteredCube 4 (1/32))]
      (fun x ↦ f (sphereChartCoordMap p x))) :
    ∀ x ∈ interior (Yau.realCenteredCube 4 (1/64)),
      Yau.coordDiv (realMatrixFlux (sphereChartPrincipalDensity d p) v) x+
        sphereEigenForcingCoefficient d p mu x*v x=0 := by
  obtain ⟨hr,he⟩ := sphere_eigen_rescaled_input d mu hmu f heigen
  apply sphere_eigen_matrix_equation d p hrho mu hmu (mu⁻¹ • f) he v hv
  simpa only [hr] using ha

theorem sphere_eigen_direct_representative (d : SphereEnergyData) (p : Base)
    (hrho : ContDiff ℝ ∞ (fun x ↦ d.density (sphereChartCoordMap p x)))
    (mu : ℝ) (hmu : mu ≠ 0)
    (f : SphereWeightedL2 d) (heigen : sphereL2Resolvent d f=mu • f) :
    ∃ v : Yau.Jets.Coord → ℝ, ContDiff ℝ ∞ v ∧
      tsupport v ⊆ Yau.realCenteredCube 4 (1/8) ∧
      v =ᵐ[volume.restrict (Yau.realCenteredCube 4 (1/32))]
        (fun x ↦ f (sphereChartCoordMap p x)) ∧
      ∀ x ∈ interior (Yau.realCenteredCube 4 (1/64)),
        Yau.coordDiv (realMatrixFlux (sphereChartPrincipalDensity d p) v) x+
          sphereEigenForcingCoefficient d p mu x*v x=0 := by
  obtain ⟨hr,he⟩ := sphere_eigen_rescaled_input d mu hmu f heigen
  obtain ⟨v,hv,hs,ha⟩ := sphere_eigen_smooth_representative d p hrho mu hmu (mu⁻¹ • f) he
  rw [hr] at ha
  exact ⟨v,hv,hs,ha,sphere_eigen_direct_matrix_equation d p hrho mu hmu f heigen v hv ha⟩

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Spectral_SphereEigenGlobalRepresentative
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open MeasureTheory Manifold Set Metric Filter Yau.Geometry
open scoped ContDiff Topology
noncomputable section

attribute [local instance] OAI.Yau.Target.sphereGlobalRepresentativeMeasurable
attribute [local instance] OAI.Yau.Target.sphereGlobalRepresentativeBorel
theorem sphere_eigen_global_representative_oai (d : SphereEnergyData)
    (hrho : ∀ p : Base, ContDiff ℝ ∞ (fun x ↦ d.density (sphereChartCoordMap p x)))
    (mu : ℝ) (hmu : mu ≠ 0) (f : SphereWeightedL2 d)
    (heigen : sphereL2Resolvent d f=mu • f) :
    ∃ u : Base → ℝ, ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ u ∧
      u =ᵐ[sphereWeightedMeasure d.density] (f : Base → ℝ) ∧
      ∀ p x, x ∈ interior (Yau.realCenteredCube 4 (1/64)) →
        Yau.coordDiv (realMatrixFlux (sphereChartPrincipalDensity d p) (u ∘ sphereChartCoordMap p)) x+
          sphereEigenForcingCoefficient d p mu x*u (sphereChartCoordMap p x)=0 := by
  classical
  obtain ⟨P,theta,htheta,hpos,hsum,hsupp,hpull,hcompact⟩ :=
    sphere_finite_smooth_partition_radius (1/128) (by norm_num)
  choose W hW hsW haW heW using (fun p : {p // p ∈ P} ↦
    sphere_eigen_direct_representative d p.val (hrho p.val) mu hmu f heigen)
  have hWcompact (p : {p // p ∈ P}) : HasCompactSupport (W p) :=
    (Yau.realCenteredCube_isCompact 4 (1/8)).of_isClosed_subset (isClosed_tsupport _) (hsW p)
  choose F hF hsF hFW using (fun p : {p // p ∈ P} ↦
    sphere_chart_scalar_extension p.val (W p) (hW p) (hWcompact p))
  let u : Base → ℝ := fun x ↦ ∑ p, theta p x*F p x
  have hu : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ u :=
    ContMDiff.sum (fun p _ ↦ (htheta p).mul (hF p))
  have hlocal (p : {p // p ∈ P}) :
      (fun x ↦ theta p x*F p x) =ᵐ[sphereWeightedMeasure d.density] (fun x ↦ theta p x*f x) := by
    apply (sphereWeightedMeasure_ae_chart_iff d p.val _).mpr
    have he := (ae_restrict_iff' (Yau.realCenteredCube_isCompact 4 (1/32)).measurableSet).mp (haW p)
    filter_upwards [he] with x hx
    by_cases hz : theta p (sphereChartCoordMap p.val x)=0
    · simp only [hz,zero_mul]
    · have hxs : x ∈ ball (0 : Yau.Jets.Coord) (1/128) := by
        obtain ⟨z,hz',hez⟩ := hsupp p (subset_closure hz)
        exact (sphereChartCoordMap_injective p.val hez) ▸ hz'
      have hxQ : x ∈ Yau.realCenteredCube 4 (1/32) := by
        intro i _
        have hi : |x i| < (1/128:ℝ) := by
          have hh := (norm_le_pi_norm x i).trans_lt
            (show ‖x‖ < 1/128 from by simpa only [mem_ball,dist_zero_right] using hxs)
          simpa only [Real.norm_eq_abs] using hh
        constructor <;> linarith [(abs_lt.mp hi).1,(abs_lt.mp hi).2]
      rw [hFW p x,hx hxQ]
  have hua : u =ᵐ[sphereWeightedMeasure d.density] (f : Base → ℝ) := by
    filter_upwards [Filter.eventually_all.mpr hlocal] with x hx
    dsimp only [u]
    simp_rw [hx]
    rw [← Finset.sum_mul,hsum,one_mul]
  refine ⟨u,hu,hua,?_⟩
  intro p
  have huc : ContDiff ℝ ∞ (u ∘ sphereChartCoordMap p) :=
    (hu.comp (sphereChartCoordMap_smooth p)).contDiff
  apply sphere_eigen_direct_matrix_equation d p (hrho p) mu hmu f heigen _ huc
  exact ae_restrict_of_ae ((sphereWeightedMeasure_ae_chart_iff d p _).mp hua)

end
end Yau.Target

end OAI
end

theorem solution : type_of% @OAI.Yau.Target.sphere_eigen_global_representative_oai := @OAI.Yau.Target.sphere_eigen_global_representative_oai
