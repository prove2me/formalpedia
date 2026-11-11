-- Prove2me | solution 1 for OAI.Yau.Target.sphere_finite_weak_jet_iteration
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T00:34:55.759272+00:00
-- url     : https://prove2.me/submissions/733d5c9f-4385-44e2-ae1d-b9310c1391e3

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
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Sequences
import Definitions.Def_YauCounterexample
import Definitions.Def_OAIQ237Ny004
import Theorems.Thm_OAI_Yau_Target_sphere_interior_localized_energy

section
-- module Solutions.OAIQ237_NY.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem ite_eq_left {α : Sort _} {c : Prop} {_ : Decidable c} {a b : α} (h : c) :
    (if c then a else b) = a := if_pos h
end OAICompat434

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

theorem real_Lp_restricted_square_le {X : Type*} [MeasurableSpace X]
    {mu nu : Measure X} (hmeasure : mu ≤ nu) (u : Lp ℝ 2 nu) :
    MemLp (u : X → ℝ) 2 mu ∧ (∫ x, (u x)^2 ∂mu) ≤ ‖u‖^2 := by
  refine ⟨(Lp.memLp u).mono_measure hmeasure,?_⟩
  have hnorm : ‖u‖^2=∫ x, (u x)^2 ∂nu := by
    simpa only [Lp.toLp_coeFn] using real_toLp_norm_sq _ (Lp.memLp u)
  rw [hnorm]
  exact integral_mono_measure hmeasure (Filter.Eventually.of_forall (fun x ↦ sq_nonneg (u x)))
    (Lp.memLp u).integrable_sq

end Yau

end

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

local instance sphereChartDivergenceDataMeasurable_r29f52a_1 : MeasurableSpace Base := borel Base
local instance sphereChartDivergenceDataBorel_r29f52a_1 : BorelSpace Base := ⟨rfl⟩
theorem sphereChartPrincipalDensity_smooth (d : SphereEnergyData) (p : Base) (i j : Fin 4) :
    ContDiff ℝ ∞ (fun x ↦ sphereChartPrincipalDensity d p x i j) :=
  roundCoordDensity_smooth.mul (intrinsicRealPrincipal_smooth d.tensor d.smooth d.symm d.pos p i j)

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

theorem realDifferenceQuotient_memLp {n : ℕ} (i : Fin n) (h : ℝ)
    (u : (Fin n → ℝ) → ℝ) (hu : MemLp u 2 (volume : Measure (Fin n → ℝ))) :
    MemLp (realDifferenceQuotient i h u) 2 (volume : Measure (Fin n → ℝ)) := by
  have hs : MeasurePreserving (fun x : Fin n → ℝ ↦ x+(Pi.single i h : Fin n → ℝ)) volume volume :=
    measurePreserving_add_right (G := Fin n → ℝ) volume ((Pi.single i h : Fin n → ℝ))
  have ht : MemLp (fun x ↦ u (x+(Pi.single i h : Fin n → ℝ))) 2 volume := hu.comp_measurePreserving (f := fun x : Fin n → ℝ ↦ x+(Pi.single i h : Fin n → ℝ)) hs
  exact (ht.sub hu).const_mul h⁻¹

theorem real_integral_translate_pairing {n : ℕ} (v : Fin n → ℝ)
    (u phi : (Fin n → ℝ) → ℝ) :
    (∫ x, u (x+v)*phi x) = ∫ x, u x*phi (x-v) := by
  have h := integral_add_right_eq_self (fun x ↦ u x*phi (x-v)) v (μ := volume)
  simpa only [add_sub_cancel_right] using h

theorem real_differenceQuotient_pairing {n : ℕ} (i : Fin n) (h : ℝ)
    (u phi : (Fin n → ℝ) → ℝ)
    (hu : MemLp u 2 (volume : Measure (Fin n → ℝ)))
    (hp : MemLp phi 2 (volume : Measure (Fin n → ℝ))) :
    Integrable (fun x ↦ realDifferenceQuotient i h u x*phi x) ∧
    Integrable (fun x ↦ u x*realDifferenceQuotient i (-h) phi x) ∧
    (∫ x, realDifferenceQuotient i h u x*phi x) =
      -(∫ x, u x*realDifferenceQuotient i (-h) phi x) := by
  have h1 := (realDifferenceQuotient_memLp i h u hu).integrable_mul hp
  have h2 := hu.integrable_mul (realDifferenceQuotient_memLp i (-h) phi hp)
  have hs : MeasurePreserving (fun x : Fin n → ℝ ↦ x+(Pi.single i h : Fin n → ℝ)) volume volume :=
    measurePreserving_add_right (G := Fin n → ℝ) volume ((Pi.single i h : Fin n → ℝ))
  have hs' : MeasurePreserving (fun x : Fin n → ℝ ↦ x+(Pi.single i (-h) : Fin n → ℝ)) volume volume :=
    measurePreserving_add_right (G := Fin n → ℝ) volume ((Pi.single i (-h) : Fin n → ℝ))
  have hut : MemLp (fun x ↦ u (x+(Pi.single i h : Fin n → ℝ))) 2 volume := hu.comp_measurePreserving (f := fun x : Fin n → ℝ ↦ x+(Pi.single i h : Fin n → ℝ)) hs
  have hpt : MemLp (fun x ↦ phi (x+(Pi.single i (-h) : Fin n → ℝ))) 2 volume := hp.comp_measurePreserving (f := fun x : Fin n → ℝ ↦ x+(Pi.single i (-h) : Fin n → ℝ)) hs'
  have h3 : Integrable (fun x ↦ u (x+(Pi.single i h : Fin n → ℝ))*phi x) := hut.integrable_mul hp
  have h4 : Integrable (fun x ↦ u x*phi x) := hu.integrable_mul hp
  have h5 : Integrable (fun x ↦ u x*phi (x+(Pi.single i (-h) : Fin n → ℝ))) := hu.integrable_mul hpt
  have he1 : (fun x ↦ realDifferenceQuotient i h u x*phi x) =
      fun x ↦ h⁻¹*(u (x+(Pi.single i h : Fin n → ℝ))*phi x-u x*phi x) := by
    funext x
    unfold realDifferenceQuotient
    ring
  have he2 : (fun x ↦ u x*realDifferenceQuotient i (-h) phi x) =
      fun x ↦ -(h⁻¹*(u x*phi (x+(Pi.single i (-h) : Fin n → ℝ))-u x*phi x)) := by
    funext x
    simp only [realDifferenceQuotient,inv_neg]
    ring
  refine ⟨h1,h2,?_⟩
  rw [he1,he2,integral_neg,neg_neg,integral_const_mul,integral_const_mul,
    integral_sub h3 h4,integral_sub h5 h4,real_integral_translate_pairing]
  simp only [Pi.single_neg,sub_eq_add_neg]

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

theorem realDifferenceQuotient_smooth {n : ℕ} (i : Fin n) (h : ℝ)
    (u : Coord n → ℝ) (hu : ContDiff ℝ ∞ u) :
    ContDiff ℝ ∞ (realDifferenceQuotient i h u) :=
  contDiff_const.mul ((hu.comp (contDiff_id.add contDiff_const)).sub hu)

theorem realCenteredCube_isCompact (n : ℕ) (r : ℝ) : IsCompact (realCenteredCube n r) :=
  isCompact_univ_pi (fun _ ↦ isCompact_Icc)

theorem realCenteredCube_shift {n : ℕ} (i : Fin n) {r R h : ℝ}
    (hh : |h| ≤ R-r) {x : Coord n} (hx : x+Pi.single i h ∈ realCenteredCube n r) :
    x ∈ realCenteredCube n R := by
  intro j hj
  have hxj := hx j hj
  have hhr : r ≤ R := by linarith [abs_nonneg h]
  by_cases he : j=i
  · subst j
    simp only [Pi.add_apply,Pi.single_eq_same,mem_Icc] at hxj
    have hh' := abs_le.mp hh
    constructor <;> linarith
  · simp only [Pi.add_apply,Pi.single_eq_of_ne he,add_zero,mem_Icc] at hxj
    exact ⟨(neg_le_neg hhr).trans hxj.1,hxj.2.trans hhr⟩

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
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_RealL2SmoothTesting
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau
open MeasureTheory Set
open scoped ContDiff
noncomputable section

theorem real_L2_norm_le_of_smooth_test_bound {n : ℕ} (u : Coord n → ℝ)
    (hu : MemLp u 2 volume) (C : ℝ) (hC : 0 ≤ C)
    (hb : ∀ phi : Coord n → ℝ, ContDiff ℝ ∞ phi → HasCompactSupport phi →
      |∫ x, u x*phi x| ≤ C*Real.sqrt (∫ x, (phi x)^2)) :
    ‖hu.toLp u‖ ≤ C := by
  let U := hu.toLp u
  have hclosed : IsClosed {v : RealEuclideanL2 n | |inner ℝ U v| ≤ C*‖v‖} :=
    isClosed_le ((continuous_const.inner continuous_id).abs) (continuous_const.mul continuous_norm)
  have hsub : {v : RealEuclideanL2 n | ∃ phi : Coord n → ℝ,
      (v : Coord n → ℝ) =ᵐ[volume] phi ∧ HasCompactSupport phi ∧ ContDiff ℝ ∞ phi} ⊆
      {v : RealEuclideanL2 n | |inner ℝ U v| ≤ C*‖v‖} := by
    rintro v ⟨phi,hv,hc,hp⟩
    have hm := real_compact_continuous_memLp phi hp.continuous hc
    have he : v=hm.toLp phi := Lp.ext (hv.trans hm.coeFn_toLp.symm)
    rw [he]
    change |inner ℝ (hu.toLp u) (hm.toLp phi)| ≤ C*‖hm.toLp phi‖
    rw [real_toLp_inner]
    have hn := real_toLp_norm_sq phi hm
    have hs : Real.sqrt (∫ x, (phi x)^2)=‖hm.toLp phi‖ := by
      rw [← hn,Real.sqrt_sq (norm_nonneg _)]
    simpa only [hs] using hb phi hp hc
  have hall : ∀ v : RealEuclideanL2 n, |inner ℝ U v| ≤ C*‖v‖ := by
    intro v
    apply (closure_minimal hsub hclosed)
    exact (Lp.dense_hasCompactSupport_contDiff (μ := (volume : Measure (Coord n))) (F := ℝ)
      (by norm_num : (2:ENNReal) ≠ ⊤)) v
  have h := hall U
  rw [real_inner_self_eq_norm_sq,abs_of_nonneg (sq_nonneg _)] at h
  change ‖U‖ ≤ C
  nlinarith [norm_nonneg U]

end
end Yau

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_RealSmoothDifferenceLimit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau
open MeasureTheory Set Filter
open scoped ContDiff Topology
noncomputable section

theorem real_smooth_difference_tendsto {n : ℕ} (psi : Coord n → ℝ)
    (hp : ContDiff ℝ ∞ psi) (i : Fin n) (x : Coord n) :
    Tendsto (fun h : ℝ ↦ realDifferenceQuotient i h psi x) (𝓝[≠] (0:ℝ))
      (𝓝 (coordPartial psi x i)) := by
  have hsingle (t : ℝ) : t • (Pi.single i 1 : Coord n)=Pi.single i t := by
    ext j
    by_cases hj : j=i <;> simp [hj]
  have hd : HasFDerivAt psi (fderiv ℝ psi x) (x+(0:ℝ) • (Pi.single i 1 : Coord n)) := by
    simpa only [zero_smul,add_zero] using (hp.differentiable (by simp) x).hasFDerivAt
  have hline : HasDerivAt (fun t : ℝ ↦ x+t • (Pi.single i 1 : Coord n)) (Pi.single i 1) 0 := by
    simpa using ((hasDerivAt_id (0:ℝ)).smul_const (Pi.single i 1 : Coord n)).const_add x
  have hd' : HasDerivAt (fun t : ℝ ↦ psi (x+t • (Pi.single i 1 : Coord n)))
      (coordPartial psi x i) 0 := by
    simpa only [zero_smul,add_zero,Function.comp_def,coordPartial] using
      hd.comp_hasDerivAt 0 hline
  simpa only [realDifferenceQuotient,zero_add,zero_smul,add_zero,hsingle,Pi.single_zero,smul_eq_mul] using
    hd'.tendsto_slope_zero

theorem real_smooth_difference_uniform_bound {n : ℕ} (psi : Coord n → ℝ)
    (hp : ContDiff ℝ ∞ psi) (hc : HasCompactSupport psi) :
    ∃ B > 0, ∀ (i : Fin n) (h : ℝ) (x : Coord n), |realDifferenceQuotient i h psi x| ≤ B := by
  have hd : Continuous (fderiv ℝ psi) := (hp.fderiv_right (m := ∞) (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).continuous
  obtain ⟨B,hB,hb⟩ := ((hc.fderiv ℝ).isCompact_range hd).isBounded.exists_pos_norm_le
  refine ⟨B,hB,fun i h x ↦ ?_⟩
  have hb' (y : Coord n) (_ : y ∈ (Set.univ : Set (Coord n))) : ‖fderiv ℝ psi y‖ ≤ B := hb _ ⟨y,rfl⟩
  have hnorm := (convex_univ : Convex ℝ (Set.univ : Set (Coord n))).norm_image_sub_le_of_norm_fderiv_le
    (fun y _ ↦ hp.differentiable (by simp) y) hb' (Set.mem_univ x) (Set.mem_univ (x+Pi.single i h))
  simp only [add_sub_cancel_left,Pi.norm_single,Real.norm_eq_abs] at hnorm
  by_cases hh : h=0
  · subst h
    simp [realDifferenceQuotient,hB.le]
  · calc
      _ = |h⁻¹| * |psi (x+Pi.single i h)-psi x| := abs_mul _ _
      _ ≤ |h⁻¹| * (B*|h|) := mul_le_mul_of_nonneg_left hnorm (abs_nonneg _)
      _ = B := by rw [abs_inv]; field_simp [abs_ne_zero.mpr hh]

theorem real_smooth_difference_integral_tendsto {n : ℕ} (μ : Measure (Coord n))
    (u psi : Coord n → ℝ) (hu : Integrable u μ)
    (hp : ContDiff ℝ ∞ psi) (hc : HasCompactSupport psi)
    (i : Fin n) (h : ℕ → ℝ) (hh : Tendsto h atTop (𝓝[≠] (0:ℝ))) :
    Tendsto (fun k ↦ ∫ x, u x*realDifferenceQuotient i (h k) psi x ∂μ) atTop
      (𝓝 (∫ x, u x*coordPartial psi x i ∂μ)) := by
  obtain ⟨B,hB,hb⟩ := real_smooth_difference_uniform_bound psi hp hc
  apply tendsto_integral_of_dominated_convergence (fun x ↦ |u x| *B)
  · intro k
    exact hu.aestronglyMeasurable.mul (realDifferenceQuotient_smooth i (h k) psi hp).continuous.aestronglyMeasurable
  · exact hu.norm.mul_const B
  · intro k
    apply Filter.Eventually.of_forall
    intro x
    rw [Real.norm_eq_abs,abs_mul]
    exact mul_le_mul_of_nonneg_left (hb i (h k) x) (abs_nonneg _)
  · exact Filter.Eventually.of_forall (fun x ↦ tendsto_const_nhds.mul
      ((real_smooth_difference_tendsto psi hp i x).comp hh))

end
end Yau

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_RealWeakTranslationPairing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau
open MeasureTheory Set Filter
open scoped ContDiff Topology
noncomputable section

theorem real_smooth_difference_pairing_limit {n : ℕ} (u psi : Coord n → ℝ)
    (hu : Integrable u) (hp : ContDiff ℝ ∞ psi) (hc : HasCompactSupport psi) (i : Fin n) :
    Tendsto (fun h : ℝ ↦ ∫ x, u x*realDifferenceQuotient i h psi x) (𝓝[≠] (0:ℝ))
      (𝓝 (∫ x, u x*coordPartial psi x i)) := by
  obtain ⟨B,hB,hb⟩ := real_smooth_difference_uniform_bound psi hp hc
  apply tendsto_integral_filter_of_dominated_convergence (fun x ↦ |u x| *B)
  · exact Filter.Eventually.of_forall (fun h ↦ hu.aestronglyMeasurable.mul
      (realDifferenceQuotient_smooth i h psi hp).continuous.aestronglyMeasurable)
  · apply Filter.Eventually.of_forall
    intro h
    apply Filter.Eventually.of_forall
    intro x
    rw [Real.norm_eq_abs,abs_mul]
    exact mul_le_mul_of_nonneg_left (hb i h x) (abs_nonneg _)
  · exact hu.norm.mul_const B
  · exact Filter.Eventually.of_forall (fun x ↦ tendsto_const_nhds.mul
      (real_smooth_difference_tendsto psi hp i x))

theorem real_translate_pairing_hasDerivAt {n : ℕ} (u psi : Coord n → ℝ)
    (hu : Integrable u) (hum : MemLp u 2 volume)
    (hp : ContDiff ℝ ∞ psi) (hc : HasCompactSupport psi) (i : Fin n) (t : ℝ) :
    HasDerivAt (fun s : ℝ ↦ ∫ x, u x*psi (x+Pi.single i s))
      (∫ x, u x*coordPartial (fun y ↦ psi (y+Pi.single i t)) x i) t := by
  let phi : Coord n → ℝ := fun x ↦ psi (x+Pi.single i t)
  have hphi : ContDiff ℝ ∞ phi := hp.comp (contDiff_id.add contDiff_const)
  have hphic : HasCompactSupport phi := hc.comp_homeomorph (Homeomorph.addRight (Pi.single i t))
  have ht := real_smooth_difference_pairing_limit u phi hu hphi hphic i
  apply hasDerivAt_iff_tendsto_slope_zero.mpr
  have he (h : ℝ) : h⁻¹ • ((∫ x, u x*psi (x+Pi.single i (t+h)))-
      (∫ x, u x*psi (x+Pi.single i t))) = ∫ x, u x*realDifferenceQuotient i h phi x := by
    have hint (s : ℝ) : Integrable (fun x ↦ u x*psi (x+Pi.single i s)) :=
      hum.integrable_mul ((real_compact_continuous_memLp psi hp.continuous hc).comp_measurePreserving
        (f := fun x : Coord n ↦ x+(Pi.single i s : Coord n))
        (measurePreserving_add_right (G := Coord n) volume (Pi.single i s : Coord n)))
    rw [smul_eq_mul,← integral_sub (hint (t+h)) (hint t),← integral_const_mul]
    apply integral_congr_ae
    apply Filter.Eventually.of_forall
    intro x
    simp only [realDifferenceQuotient,phi,Pi.single_add]
    rw [show x+Pi.single i h+Pi.single i t=x+(Pi.single i t+Pi.single i h) by abel]
    ring
  simpa only [he] using ht

end
end Yau

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_RealWeakDifferenceBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau
open MeasureTheory Set Filter
open scoped ContDiff Topology
noncomputable section

theorem real_weak_difference_test_bound {n : ℕ} (u g : Coord n → ℝ)
    (hu : Integrable u) (hum : MemLp u 2 volume) (hgm : MemLp g 2 volume) (i : Fin n)
    (hweak : ∀ psi : Coord n → ℝ, ContDiff ℝ ∞ psi → HasCompactSupport psi →
      (∫ x, u x*coordPartial psi x i)=-(∫ x, g x*psi x))
    (h : ℝ) (psi : Coord n → ℝ) (hp : ContDiff ℝ ∞ psi) (hc : HasCompactSupport psi) :
    |∫ x, realDifferenceQuotient i h u x*psi x| ≤
      ‖hgm.toLp g‖*Real.sqrt (∫ x, (psi x)^2) := by
  have hpsi := real_compact_continuous_memLp psi hp.continuous hc
  let R : ℝ → ℝ := fun t : ℝ ↦ ∫ x : Coord n, u x*psi (x+Pi.single i t)
  let C : ℝ := ‖hgm.toLp g‖*‖hpsi.toLp psi‖
  have hpt (t : ℝ) : ContDiff ℝ ∞ (fun x : Coord n ↦ psi (x+Pi.single i t)) :=
    hp.comp (contDiff_id.add contDiff_const)
  have hpct (t : ℝ) : HasCompactSupport (fun x : Coord n ↦ psi (x+Pi.single i t)) :=
    hc.comp_homeomorph (Homeomorph.addRight (Pi.single i t : Coord n))
  have hpmt (t : ℝ) : MemLp (fun x : Coord n ↦ psi (x+Pi.single i t)) 2 volume := real_compact_continuous_memLp _ (hpt t).continuous (hpct t)
  have hd (t : ℝ) : HasDerivAt R (-(∫ x, g x*psi (x+Pi.single i t))) t := by
    have ht := real_translate_pairing_hasDerivAt u psi hu hum hp hc i t
    rw [hweak _ (hpt t) (hpct t)] at ht
    exact ht
  have hbound (t : ℝ) : ‖deriv R t‖ ≤ C := by
    have ht : (realL2Translate (Pi.single i t) (hpsi.toLp psi) : Coord n → ℝ) =ᵐ[volume]
        (fun x ↦ psi (x+Pi.single i t)) :=
      (realL2Translate_ae (Pi.single i t) (hpsi.toLp psi)).trans
        ((measurePreserving_add_right (G := Coord n) volume (Pi.single i t)).quasiMeasurePreserving.ae_eq_comp
          hpsi.coeFn_toLp)
    have hi := real_L2_inner_reps (hgm.toLp g) (realL2Translate (Pi.single i t) (hpsi.toLp psi))
      g (fun x ↦ psi (x+Pi.single i t)) hgm.coeFn_toLp ht
    rw [(hd t).deriv,norm_neg,← hi.2]
    have hn := norm_inner_le_norm (𝕜 := ℝ) (hgm.toLp g) (realL2Translate (Pi.single i t) (hpsi.toLp psi))
    simpa only [realL2Translate_norm,C] using hn
  have hosc := Convex.norm_image_sub_le_of_norm_deriv_le
    (fun t (_ : t ∈ (Set.univ : Set ℝ)) ↦ (hd t).differentiableAt) (fun t _ ↦ hbound t)
    (convex_univ : Convex ℝ (Set.univ : Set ℝ)) (Set.mem_univ (0:ℝ)) (Set.mem_univ (-h))
  have hid : (∫ x, u x*realDifferenceQuotient i (-h) psi x) = (-h)⁻¹*(R (-h)-R 0) := by
    have he : (fun x ↦ u x*realDifferenceQuotient i (-h) psi x) =
        fun x ↦ (-h)⁻¹*(u x*psi (x+Pi.single i (-h))-u x*psi x) := by
      funext x; unfold realDifferenceQuotient; ring
    have hi1 : Integrable (fun x ↦ u x*psi (x+Pi.single i (-h))) := hum.integrable_mul (hpmt (-h))
    have hi0 : Integrable (fun x ↦ u x*psi x) := hum.integrable_mul hpsi
    rw [he,integral_const_mul,integral_sub hi1 hi0]
    simp only [R,Pi.single_zero,add_zero]
  have hpair := (real_differenceQuotient_pairing i h u psi hum hpsi).2.2
  have hsqrt : Real.sqrt (∫ x, (psi x)^2)=‖hpsi.toLp psi‖ := by
    rw [← real_toLp_norm_sq psi hpsi,Real.sqrt_sq (norm_nonneg _)]
  rw [hpair,abs_neg,hid,abs_mul,hsqrt]
  change |(-h)⁻¹| *|R (-h)-R 0| ≤ C
  by_cases hh : h=0
  · subst h
    simp only [neg_zero,inv_zero,abs_zero,zero_mul]
    exact mul_nonneg (norm_nonneg _) (norm_nonneg _)
  · have ho : |R (-h)-R 0| ≤ C*|h| := by
      simpa only [sub_zero,Real.norm_eq_abs,abs_neg] using hosc
    calc
      _ ≤ |(-h)⁻¹| *(C*|h|) := mul_le_mul_of_nonneg_left ho (abs_nonneg _)
      _ = C := by rw [abs_inv,abs_neg]; field_simp [abs_ne_zero.mpr hh]

theorem real_weak_derivative_difference_bound {n : ℕ} (u g : Coord n → ℝ)
    (hu : Integrable u) (hum : MemLp u 2 volume) (hgm : MemLp g 2 volume) (i : Fin n)
    (hweak : ∀ psi : Coord n → ℝ, ContDiff ℝ ∞ psi → HasCompactSupport psi →
      (∫ x, u x*coordPartial psi x i)=-(∫ x, g x*psi x)) (h : ℝ) :
    MemLp (realDifferenceQuotient i h u) 2 volume ∧
      (∫ x, (realDifferenceQuotient i h u x)^2) ≤ ∫ x, (g x)^2 := by
  have hm := realDifferenceQuotient_memLp i h u hum
  have hn := real_L2_norm_le_of_smooth_test_bound _ hm ‖hgm.toLp g‖ (norm_nonneg _)
    (fun psi hp hc ↦ real_weak_difference_test_bound u g hu hum hgm i hweak h psi hp hc)
  have hsq : ‖hm.toLp (realDifferenceQuotient i h u)‖^2 ≤ ‖hgm.toLp g‖^2 := by
    nlinarith [norm_nonneg (hm.toLp (realDifferenceQuotient i h u)),norm_nonneg (hgm.toLp g)]
  rw [real_toLp_norm_sq,real_toLp_norm_sq] at hsq
  exact ⟨hm,hsq⟩

end
end Yau

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_RealLocalWeakDifferenceBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau
open MeasureTheory Set
open scoped ContDiff
noncomputable section

theorem real_local_weak_cutoff_difference_bound {n : ℕ} {K : Set (Coord n)} (hK : IsCompact K)
    (u g eta : Coord n → ℝ) (hu : MemLp u 2 (volume.restrict K))
    (hg : MemLp g 2 (volume.restrict K)) (he : ContDiff ℝ ∞ eta)
    (hs : tsupport eta ⊆ K) (i : Fin n)
    (hweak : ∀ phi : Coord n → ℝ, ContDiff ℝ ∞ phi → HasCompactSupport phi → tsupport phi ⊆ K →
      (∫ x in K, u x*coordPartial phi x i)=-(∫ x in K, g x*phi x)) (h : ℝ) :
    MemLp (realDifferenceQuotient i h (fun x ↦ eta x*u x)) 2 volume ∧
      (∫ x, (realDifferenceQuotient i h (fun y ↦ eta y*u y) x)^2) ≤
        ∫ x, (eta x*g x+coordPartial eta x i*u x)^2 := by
  have hloc := real_local_weak_cutoff hK u g eta hu hg he hs i hweak
  let : IsFiniteMeasure (volume.restrict K) := isFiniteMeasure_restrict.mpr hK.measure_ne_top
  have hv : Integrable (fun x ↦ eta x*u x) := by
    apply (integrableOn_iff_integrable_of_support_subset (s := K) ?_).mp
    · exact (hloc.1.mono_measure Measure.restrict_le_self).integrable (by norm_num)
    · intro x hx
      exact hs (subset_tsupport eta (by
        intro hz
        exact hx (by simp only [hz,zero_mul])))
  exact real_weak_derivative_difference_bound _ _ hv hloc.1 hloc.2.1 i
    (fun psi hp hc ↦ (hloc.2.2 psi hp hc).2.2) h

end
end Yau

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_RealLocalizedDifferenceIdentity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau
open Set MeasureTheory
noncomputable section

theorem real_indicator_difference_localize {n : ℕ} (Q : Set (Coord n))
    (u chi : Coord n → ℝ) (i : Fin n) (h : ℝ) (x : Coord n)
    (hx : x ∈ Q) (ht : x+Pi.single i h ∈ Q)
    (hc : chi x=1) (hct : chi (x+Pi.single i h)=1) :
    realDifferenceQuotient i h (Q.indicator u) x =
      realDifferenceQuotient i h (fun y ↦ chi y*u y) x := by
  simp only [realDifferenceQuotient,indicator_of_mem hx,indicator_of_mem ht,hc,hct,one_mul]

theorem real_supported_difference_localize {n : ℕ} (Q : Set (Coord n))
    (u chi eta : Coord n → ℝ) (i : Fin n) (h : ℝ)
    (hend : ∀ x ∈ tsupport eta, x ∈ Q ∧ x+Pi.single i h ∈ Q ∧
      chi x=1 ∧ chi (x+Pi.single i h)=1) :
    (fun x ↦ eta x*realDifferenceQuotient i h (Q.indicator u) x) =
      (fun x ↦ eta x*realDifferenceQuotient i h (fun y ↦ chi y*u y) x) := by
  funext x
  by_cases hx : x ∈ tsupport eta
  · obtain ⟨hxQ,htQ,hc,hct⟩ := hend x hx
    rw [real_indicator_difference_localize Q u chi i h x hxQ htQ hc hct]
  · rw [image_eq_zero_of_notMem_tsupport hx,zero_mul,zero_mul]

end
end Yau

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_RealCompactL2MapLemmas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Yau

open MeasureTheory Set

theorem real_indicator_weighted_bound {n : ℕ} {Q : Set (Fin n → ℝ)} (hQ : IsCompact Q)
    (eta : (Fin n → ℝ) → ℝ) (he : Continuous eta) :
    ∃ C > 0, ∀ u : (Fin n → ℝ) → ℝ, MemLp u 2 (volume.restrict Q) →
      MemLp (fun x ↦ eta x*Q.indicator u x) 2 volume ∧
      (∫ x, (eta x*Q.indicator u x)^2) ≤ C*(∫ x in Q, (u x)^2) := by
  obtain ⟨C,hC,hb⟩ := real_compact_multiplier_bound hQ eta he
  refine ⟨C,hC,fun u hu ↦ ?_⟩
  have hind : (fun x ↦ eta x*Q.indicator u x)=Q.indicator (fun x ↦ eta x*u x) := by
    funext x
    by_cases hx : x ∈ Q
    · simp only [indicator_of_mem hx]
    · simp only [indicator_of_notMem hx,mul_zero]
  have hs : (fun x ↦ (eta x*Q.indicator u x)^2)=Q.indicator (fun x ↦ (eta x*u x)^2) := by
    funext x
    by_cases hx : x ∈ Q
    · simp only [indicator_of_mem hx]
    · simp only [indicator_of_notMem hx,mul_zero,zero_pow (by decide : (2:ℕ)≠0)]
  refine ⟨?_,?_⟩
  · rw [hind]
    exact (memLp_indicator_iff_restrict hQ.measurableSet).mpr (hb u hu).1
  · change (∫ x, (fun y ↦ (eta y*Q.indicator u y)^2) x) ≤ _
    rw [hs,integral_indicator hQ.measurableSet]
    exact (hb u hu).2

end Yau

end

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
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_RealHessianDifferenceCutoffsLemmas
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Yau

open Set Filter
open scoped ContDiff Topology

theorem real_nested_difference_cutoffs (R r : ℝ) (hr : r < R) :
    ∃ eta chi : Jets.Coord → ℝ,
      ContDiff ℝ ∞ eta ∧ ContDiff ℝ ∞ chi ∧ HasCompactSupport eta ∧ HasCompactSupport chi ∧
      tsupport eta ⊆ interior (realCenteredCube 4 ((r+R)/2)) ∧
      tsupport chi ⊆ interior (realCenteredCube 4 R) ∧
      (∀ x, 0 ≤ eta x ∧ eta x ≤ 1) ∧ (∀ x, 0 ≤ chi x ∧ chi x ≤ 1) ∧
      (∀ x ∈ realCenteredCube 4 r, eta =ᶠ[𝓝 x] (fun _ ↦ 1)) ∧
      ∀ (i : Fin 4) (h : ℝ), |h| ≤ (R-r)/8 → ∀ x ∈ tsupport eta,
        x ∈ interior (realCenteredCube 4 R) ∧
        x+Pi.single i h ∈ interior (realCenteredCube 4 R) ∧
        chi =ᶠ[𝓝 x] (fun _ ↦ 1) ∧ chi =ᶠ[𝓝 (x+Pi.single i h)] (fun _ ↦ 1) := by
  obtain ⟨eta,he,hec,hes,heb,he1⟩ := real_cube_smooth_cutoff r ((3*r+R)/4) (by linarith)
  obtain ⟨chi,hc,hcc,hcs,hcb,hc1⟩ := real_cube_smooth_cutoff ((r+3*R)/4) ((r+7*R)/8) (by linarith)
  refine ⟨eta,chi,he,hc,hec,hcc,hes.trans (realCenteredCube_subset_interior (by linarith)),
    hcs.trans (realCenteredCube_subset_interior (by linarith)),heb,hcb,he1,?_⟩
  intro i h hh x hx
  have hxsmall := hes hx
  have hxouter : x ∈ realCenteredCube 4 ((r+3*R)/4) := realCenteredCube_mono (by linarith) hxsmall
  have hxt : x+Pi.single i h ∈ realCenteredCube 4 ((r+3*R)/4) := by
    apply realCenteredCube_shift i (h := -h) (r := (3*r+R)/4)
      (by simpa only [abs_neg] using (show |h| ≤ ((r+3*R)/4)-(3*r+R)/4 by linarith))
    simpa only [Pi.single_neg,add_neg_cancel_right] using hxsmall
  exact ⟨realCenteredCube_subset_interior (by linarith) hxouter,
    realCenteredCube_subset_interior (by linarith) hxt,hc1 x hxouter,hc1 _ hxt⟩

end Yau

end

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_RealLocalWeakDifferenceQuadratic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau
open MeasureTheory Set
open scoped ContDiff
noncomputable section

theorem real_local_weak_difference_quadratic {n : ℕ} {K : Set (Coord n)} (hK : IsCompact K)
    (chi : Coord n → ℝ) (hc : ContDiff ℝ ∞ chi) (hs : tsupport chi ⊆ K)
    (i : Fin n) :
    ∃ C > 0, ∀ (u g : Coord n → ℝ), MemLp u 2 (volume.restrict K) →
      MemLp g 2 (volume.restrict K) →
      (∀ psi : Coord n → ℝ, ContDiff ℝ ∞ psi → HasCompactSupport psi → tsupport psi ⊆ K →
        (∫ x in K, u x*coordPartial psi x i)=-(∫ x in K, g x*psi x)) →
      ∀ h : ℝ, MemLp (realDifferenceQuotient i h (fun x ↦ chi x*u x)) 2 volume ∧
        (∫ x, (realDifferenceQuotient i h (fun y ↦ chi y*u y) x)^2) ≤
          C*((∫ x in K, (u x)^2)+(∫ x in K, (g x)^2)) := by
  obtain ⟨A,hA,hAb⟩ := real_compact_multiplier_bound hK chi hc.continuous
  obtain ⟨B,hB,hBb⟩ := real_compact_multiplier_bound hK (fun x ↦ coordPartial chi x i)
    (real_coordPartial_smooth chi hc i).continuous
  refine ⟨2*(A+B),by positivity,fun u g hu hg hw h ↦ ?_⟩
  have hbase := real_local_weak_cutoff_difference_bound hK u g chi hu hg hc hs i hw h
  refine ⟨hbase.1,hbase.2.trans ?_⟩
  have hdsub : tsupport (fun x ↦ coordPartial chi x i) ⊆ K :=
    (tsupport_fderiv_apply_subset ℝ (Pi.single i 1)).trans hs
  have hsame : (∫ x, (chi x*g x+coordPartial chi x i*u x)^2) =
      ∫ x in K, (chi x*g x+coordPartial chi x i*u x)^2 := by
    symm
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    rw [image_eq_zero_of_notMem_tsupport (fun ht ↦ hx (hs ht)),
      image_eq_zero_of_notMem_tsupport (f := fun y ↦ coordPartial chi y i) (fun ht ↦ hx (hdsub ht))]
    norm_num
  rw [hsame]
  have hga := hAb g hg
  have hub := hBb u hu
  have hsum : (∫ x in K, (chi x*g x+coordPartial chi x i*u x)^2) ≤
      2*(∫ x in K, (chi x*g x)^2)+2*(∫ x in K, (coordPartial chi x i*u x)^2) := by
    rw [← integral_const_mul,← integral_const_mul,
      ← integral_add (hga.1.integrable_sq.const_mul 2) (hub.1.integrable_sq.const_mul 2)]
    apply integral_mono (hga.1.add hub.1).integrable_sq
      ((hga.1.integrable_sq.const_mul 2).add (hub.1.integrable_sq.const_mul 2))
    intro x
    change (chi x*g x+coordPartial chi x i*u x)^2 ≤ 2*(chi x*g x)^2+2*(coordPartial chi x i*u x)^2
    nlinarith [sq_nonneg (chi x*g x-coordPartial chi x i*u x)]
  have h0u : 0 ≤ ∫ x in K, (u x)^2 := integral_nonneg (fun x ↦ sq_nonneg _)
  have h0g : 0 ≤ ∫ x in K, (g x)^2 := integral_nonneg (fun x ↦ sq_nonneg _)
  nlinarith [hga.2,hub.2,mul_nonneg hA.le h0u,mul_nonneg hB.le h0g]

end
end Yau

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_RealLocalizedDerivativeQuadratic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau
open MeasureTheory Set
open scoped ContDiff
noncomputable section

theorem real_localized_derivative_quadratic {n : ℕ} {K : Set (Coord n)} (hK : IsCompact K)
    (chi : Coord n → ℝ) (hc : ContDiff ℝ ∞ chi) (hs : tsupport chi ⊆ K)
    (i : Fin n) :
    ∃ C > 0, ∀ (u g : Coord n → ℝ), MemLp u 2 (volume.restrict K) →
      MemLp g 2 (volume.restrict K) →
      MemLp (fun x ↦ chi x*g x+coordPartial chi x i*u x) 2 volume ∧
        (∫ x, (chi x*g x+coordPartial chi x i*u x)^2) ≤
          C*((∫ x in K, (u x)^2)+(∫ x in K, (g x)^2)) := by
  obtain ⟨A,hA,hAb⟩ := real_compact_multiplier_bound hK chi hc.continuous
  obtain ⟨B,hB,hBb⟩ := real_compact_multiplier_bound hK (fun x ↦ coordPartial chi x i)
    (real_coordPartial_smooth chi hc i).continuous
  refine ⟨2*(A+B),by positivity,fun u g hu hg ↦ ?_⟩
  have hga := hAb g hg
  have hub := hBb u hu
  have hglob : MemLp (fun x ↦ chi x*g x+coordPartial chi x i*u x) 2 volume := by
    exact (real_compact_localL2_product hK chi g hc.continuous hs hg).add
      (real_compact_localL2_product hK (fun x ↦ coordPartial chi x i) u
        (real_coordPartial_smooth chi hc i).continuous
        ((tsupport_fderiv_apply_subset ℝ (Pi.single i 1)).trans hs) hu)
  refine ⟨hglob,?_⟩
  have hdsub : tsupport (fun x ↦ coordPartial chi x i) ⊆ K :=
    (tsupport_fderiv_apply_subset ℝ (Pi.single i 1)).trans hs
  have hsame : (∫ x, (chi x*g x+coordPartial chi x i*u x)^2) =
      ∫ x in K, (chi x*g x+coordPartial chi x i*u x)^2 := by
    symm
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    rw [image_eq_zero_of_notMem_tsupport (fun ht ↦ hx (hs ht)),
      image_eq_zero_of_notMem_tsupport (f := fun y ↦ coordPartial chi y i) (fun ht ↦ hx (hdsub ht))]
    norm_num
  rw [hsame]
  have hsum : (∫ x in K, (chi x*g x+coordPartial chi x i*u x)^2) ≤
      2*(∫ x in K, (chi x*g x)^2)+2*(∫ x in K, (coordPartial chi x i*u x)^2) := by
    rw [← integral_const_mul,← integral_const_mul,
      ← integral_add (hga.1.integrable_sq.const_mul 2) (hub.1.integrable_sq.const_mul 2)]
    apply integral_mono (hga.1.add hub.1).integrable_sq
      ((hga.1.integrable_sq.const_mul 2).add (hub.1.integrable_sq.const_mul 2))
    intro x
    change (chi x*g x+coordPartial chi x i*u x)^2 ≤ 2*(chi x*g x)^2+2*(coordPartial chi x i*u x)^2
    nlinarith [sq_nonneg (chi x*g x-coordPartial chi x i*u x)]
  have h0u : 0 ≤ ∫ x in K, (u x)^2 := integral_nonneg (fun x ↦ sq_nonneg _)
  have h0g : 0 ≤ ∫ x in K, (g x)^2 := integral_nonneg (fun x ↦ sq_nonneg _)
  nlinarith [hga.2,hub.2,mul_nonneg hA.le h0u,mul_nonneg hB.le h0g]

end
end Yau

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_RealWeightedLocalDifferenceBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau
open MeasureTheory Set
open scoped ContDiff
noncomputable section

theorem real_compact_global_multiplier_bound {n : ℕ} (eta : Coord n → ℝ)
    (he : Continuous eta) (hc : HasCompactSupport eta) :
    ∃ C > 0, ∀ u : Coord n → ℝ, MemLp u 2 volume →
      MemLp (fun x ↦ eta x*u x) 2 volume ∧
      (∫ x, (eta x*u x)^2) ≤ C*(∫ x, (u x)^2) := by
  obtain ⟨C,hC,hb⟩ := real_compact_multiplier_bound hc eta he
  refine ⟨C,hC,fun u hu ↦ ?_⟩
  refine ⟨real_compact_localL2_product hc eta u he Subset.rfl (hu.restrict _),?_⟩
  have hs : (∫ x, (eta x*u x)^2) = ∫ x in tsupport eta, (eta x*u x)^2 := by
    symm
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    rw [image_eq_zero_of_notMem_tsupport hx,zero_mul,zero_pow (by decide)]
  rw [hs]
  exact (hb u (hu.restrict _)).2.trans (mul_le_mul_of_nonneg_left
    (setIntegral_le_integral hu.integrable_sq (Filter.Eventually.of_forall (fun x ↦ sq_nonneg _))) hC.le)

theorem real_weighted_local_difference_bound {n : ℕ} {Q : Set (Coord n)} (hQ : IsCompact Q)
    (eta chi : Coord n → ℝ) (he : Continuous eta) (hec : HasCompactSupport eta)
    (hc : ContDiff ℝ ∞ chi) (hs : tsupport chi ⊆ Q) (i : Fin n) :
    ∃ C > 0, ∀ (u g : Coord n → ℝ), MemLp u 2 (volume.restrict Q) →
      MemLp g 2 (volume.restrict Q) →
      (∀ psi : Coord n → ℝ, ContDiff ℝ ∞ psi → HasCompactSupport psi → tsupport psi ⊆ Q →
        (∫ x in Q, u x*coordPartial psi x i)=-(∫ x in Q, g x*psi x)) →
      ∀ h : ℝ,
      (∀ x ∈ tsupport eta, x ∈ Q ∧ x+Pi.single i h ∈ Q ∧ chi x=1 ∧ chi (x+Pi.single i h)=1) →
      MemLp (fun x ↦ eta x*realDifferenceQuotient i h (Q.indicator u) x) 2 volume ∧
      (∫ x, (eta x*realDifferenceQuotient i h (Q.indicator u) x)^2) ≤
        C*((∫ x in Q, (u x)^2)+(∫ x in Q, (g x)^2)) := by
  obtain ⟨A,hA,ha⟩ := real_compact_global_multiplier_bound eta he hec
  obtain ⟨B,hB,hb⟩ := real_local_weak_difference_quadratic hQ chi hc hs i
  refine ⟨A*B,by positivity,fun u g hu hg hw h hend ↦ ?_⟩
  have hd := hb u g hu hg hw h
  have hm := ha _ hd.1
  have hid := real_supported_difference_localize Q u chi eta i h hend
  constructor
  · rw [hid]
    exact hm.1
  · change (∫ x, ((fun y ↦ eta y*realDifferenceQuotient i h (Q.indicator u) y) x)^2) ≤ _
    rw [hid]
    have ht := hm.2.trans (mul_le_mul_of_nonneg_left hd.2 hA.le)
    simpa only [← mul_assoc] using ht

end
end Yau

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Charts_SphereInteriorDifferenceBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open MeasureTheory Yau.Geometry Set
open scoped ContDiff
noncomputable section

theorem sphere_interior_difference_bound (d : SphereEnergyData) (p : Base)
    (R0 r : ℝ) (hr : r < R0) (hR : R0 ≤ 1) :
    ∃ C > 0,
      ∀ (u : Yau.Jets.Coord → ℝ) (V0 P0 G : Fin 4 → Yau.Jets.Coord → ℝ)
        (DG : Fin 4 → Fin 4 → Yau.Jets.Coord → ℝ) (F0 : Yau.Jets.Coord → ℝ),
      let Q := Yau.realCenteredCube 4 R0
      MemLp u 2 (volume.restrict Q) →
      (∀ a, MemLp (V0 a) 2 (volume.restrict Q)) →
      (∀ a, MemLp (P0 a) 2 (volume.restrict Q)) →
      (∀ j, MemLp (G j) 2 (volume.restrict Q)) →
      (∀ j i, MemLp (DG j i) 2 (volume.restrict Q)) →
      MemLp F0 2 (volume.restrict Q) →
      (∀ a, P0 a =ᵐ[volume.restrict (interior Q)] V0 a) →
      (∀ j psi, ContDiff ℝ ∞ psi → HasCompactSupport psi → tsupport psi ⊆ Q →
        (∫ x in Q, u x*Yau.coordPartial psi x j)=-(∫ x in Q, V0 j x*psi x)) →
      (∀ j i psi, ContDiff ℝ ∞ psi → HasCompactSupport psi → tsupport psi ⊆ Q →
        (∫ x in Q, G j x*Yau.coordPartial psi x i)=-(∫ x in Q, DG j i x*psi x)) →
      (∀ psi, ContDiff ℝ ∞ psi → HasCompactSupport psi → tsupport psi ⊆ Q →
        (∑ a, ∑ j, ∫ x in Q, sphereChartPrincipalDensity d p x a j*P0 a x*Yau.coordPartial psi x j)=
          (∫ x in Q, F0 x*psi x)-(∑ j, ∫ x in Q, G j x*Yau.coordPartial psi x j)) →
      ∀ E : ℝ, 0 ≤ E →
        (∫ x in Q, (u x)^2) ≤ E →
        (∀ a, (∫ x in Q, (V0 a x)^2) ≤ E) →
        (∫ x in Q, (F0 x)^2) ≤ E →
        (∀ j, (∫ x in Q, (G j x)^2) ≤ E) →
        (∀ j i, (∫ x in Q, (DG j i x)^2) ≤ E) →
        ∀ (i : Fin 4) (h : ℝ), |h| ≤ (R0-r)/8 →
          (∀ a, MemLp (Yau.realDifferenceQuotient i h (V0 a)) 2
            (volume.restrict (Yau.realCenteredCube 4 r))) ∧
          (∑ a, ∫ x in Yau.realCenteredCube 4 r, (Yau.realDifferenceQuotient i h (V0 a) x)^2) ≤ C*E := by
  obtain ⟨m,hm,K,hK,henergy⟩ := sphere_interior_localized_energy d p
  obtain ⟨eta,chi,he,hchi,hec,hchic,hes,hchis,heb,hchib,he1,hend⟩ :=
    Yau.real_nested_difference_cutoffs R0 r hr
  let Q := Yau.realCenteredCube 4 R0
  let Q0 := Yau.realCenteredCube 4 r
  have hQ : IsCompact Q := Yau.realCenteredCube_isCompact 4 R0
  have hQ0 : IsCompact Q0 := Yau.realCenteredCube_isCompact 4 r
  have hcs : tsupport chi ⊆ Q := hchis.trans interior_subset
  have hetab (x : Yau.Jets.Coord) : |eta x| ≤ 1 := by rw [abs_of_nonneg (heb x).1]; exact (heb x).2
  have hends (i : Fin 4) (h : ℝ) (hh : |h| ≤ (R0-r)/8) (x : Yau.Jets.Coord) (hx : x ∈ tsupport eta) :
      x ∈ interior Q ∧ x+Pi.single i h ∈ interior Q ∧ chi x=1 ∧ chi (x+Pi.single i h)=1 := by
    have ht := hend i h hh x hx
    exact ⟨ht.1,ht.2.1,ht.2.2.1.eq_of_nhds,ht.2.2.2.eq_of_nhds⟩
  have hends0 (i : Fin 4) (h : ℝ) (hh : |h| ≤ (R0-r)/8) (x : Yau.Jets.Coord) (hx : x ∈ tsupport eta) :
      x ∈ Q ∧ x+Pi.single i h ∈ Q ∧ chi x=1 ∧ chi (x+Pi.single i h)=1 := by
    have ht := hends i h hh x hx
    exact ⟨interior_subset ht.1,interior_subset ht.2.1,ht.2.2⟩
  obtain ⟨CW,hCW,hWb⟩ := Yau.real_indicator_weighted_bound hQ eta he.continuous
  choose CG hCG hGb using fun i ↦ Yau.real_localized_derivative_quadratic hQ chi hchi hcs i
  obtain ⟨G0,hG0,hGmax⟩ := Yau.real_finite_positive_majorant CG
  choose CR hCR hRb using fun i a ↦ Yau.real_weighted_local_difference_bound hQ
    (fun x ↦ Yau.coordPartial eta x a) chi (Yau.real_coordPartial_smooth eta he a).continuous
    (hec.fderiv_apply ℝ (Pi.single a 1)) hchi hcs i
  obtain ⟨R1,hR1,hRmax⟩ := Yau.real_finite_positive_majorant (fun t : Fin 4 × Fin 4 ↦ CR t.1 t.2)
  let C := (4/m)*((16/m)*(1+8*G0)+K*(4*CW)+(K+m)*(8*R1))
  refine ⟨C,by dsimp [C] <;> positivity,?_⟩
  intro u V0 P0 G DG F0
  dsimp only
  intro hu hv hp hg hd hf hsame hweak hcomm hequation E hE hbu hbv hbf hbg hbd i h hh
  let V := fun a ↦ Q.indicator (V0 a)
  let q := Yau.realDifferenceQuotient i h (Q.indicator u)
  let T := fun a x ↦ eta x*Yau.realDifferenceQuotient i h (V a) x
  let W := fun a x ↦ eta x*V a x
  let R := fun a x ↦ Yau.coordPartial eta x a*q x
  let F := Q.indicator F0
  have hwt := henergy R0 ((r+R0)/2) (by linarith) hR u V0 P0 G DG F0
    hu hv hp hg hd hf hsame hweak hcomm hequation eta chi he hec hetab hes hchi hcs i h
    (by linarith) (hends i h hh)
  have hWone (a : Fin 4) : (∫ x, (W a x)^2) ≤ CW*E :=
    (hWb (V0 a) (hv a)).2.trans (mul_le_mul_of_nonneg_left (hbv a) hCW.le)
  have hWsum : (∑ a, ∫ x, (W a x)^2) ≤ 4*CW*E := by
    have ht := Finset.sum_le_sum (s := Finset.univ) (fun a _ ↦ hWone a)
    simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_ofNat,mul_assoc] using ht
  have hRone (a : Fin 4) : (∫ x, (R a x)^2) ≤ 2*R1*E := by
    have ht := (hRb i a u (V0 i) hu (hv i) (hweak i) h
      (fun x hx ↦ hends0 i h hh x (tsupport_fderiv_apply_subset ℝ (Pi.single a 1) hx))).2
    have hb := mul_le_mul_of_nonneg_left (add_le_add hbu (hbv i)) (hCR i a).le
    have hmax := mul_le_mul_of_nonneg_right (hRmax (i,a)) (show 0 ≤ E+E by positivity)
    exact ht.trans (hb.trans (hmax.trans_eq (by ring)))
  have hRsum : (∑ a, ∫ x, (R a x)^2) ≤ 8*R1*E := by
    have ht := Finset.sum_le_sum (s := Finset.univ) (fun a _ ↦ hRone a)
    norm_num only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_ofNat] at ht
    exact ht.trans_eq (by ring)
  have hGone (j : Fin 4) : (∫ x, (chi x*DG j i x+Yau.coordPartial chi x i*G j x)^2) ≤ 2*G0*E := by
    have ht := (hGb i (G j) (DG j i) (hg j) (hd j i)).2
    have hb := mul_le_mul_of_nonneg_left (add_le_add (hbg j) (hbd j i)) (hCG i).le
    have hmax := mul_le_mul_of_nonneg_right (hGmax i) (show 0 ≤ E+E by positivity)
    exact ht.trans (hb.trans (hmax.trans_eq (by ring)))
  have hGsum : (∑ j, ∫ x, (chi x*DG j i x+Yau.coordPartial chi x i*G j x)^2) ≤ 8*G0*E := by
    have ht := Finset.sum_le_sum (s := Finset.univ) (fun j _ ↦ hGone j)
    norm_num only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_ofNat] at ht
    exact ht.trans_eq (by ring)
  have hFint : (∫ x, (F x)^2) ≤ E := by
    have hind : (fun x ↦ (F x)^2)=Q.indicator (fun x ↦ (F0 x)^2) := by
      funext x
      by_cases hx : x ∈ Q
      · simp only [F,indicator_of_mem hx]
      · simp only [F,indicator_of_notMem hx,zero_pow (by decide : (2:ℕ)≠0)]
    change (∫ x, (fun y ↦ (F y)^2) x) ≤ _
    rw [hind,integral_indicator hQ.measurableSet]
    exact hbf
  have hglobal : (∑ a, ∫ x, (T a x)^2) ≤ C*E := by
    have ht := add_le_add (add_le_add
      (mul_le_mul_of_nonneg_left (add_le_add hFint hGsum) (show 0 ≤ 16/m by positivity))
      (mul_le_mul_of_nonneg_left hWsum hK.le))
      (mul_le_mul_of_nonneg_left hRsum (add_nonneg hK.le hm.le))
    have hb := hwt.2.trans (mul_le_mul_of_nonneg_left ht (show 0 ≤ 4/m by positivity))
    exact hb.trans_eq (by dsimp [C] <;> ring)
  have hident (a : Fin 4) (x : Yau.Jets.Coord) (hx : x ∈ Q0) :
      Yau.realDifferenceQuotient i h (V0 a) x=T a x := by
    have hxQ : x ∈ Q := Yau.realCenteredCube_mono hr.le hx
    have htQ : x+Pi.single i h ∈ Q := by
      apply Yau.realCenteredCube_shift i (h := -h) (r := r)
        (by simpa only [abs_neg] using (show |h| ≤ R0-r by linarith))
      simpa only [Pi.single_neg,add_neg_cancel_right] using hx
    dsimp [T,V]
    rw [(he1 x hx).eq_of_nhds,one_mul]
    simp only [Yau.realDifferenceQuotient,indicator_of_mem hxQ,indicator_of_mem htQ]
  refine ⟨fun a ↦ ?_,?_⟩
  · apply ((hwt.1 a).1.restrict Q0).ae_eq
    filter_upwards [ae_restrict_mem hQ0.measurableSet] with x hx
    exact (hident a x hx).symm
  · apply le_trans (Finset.sum_le_sum (fun a _ ↦ ?_)) hglobal
    have hEq : (∫ x in Q0, (Yau.realDifferenceQuotient i h (V0 a) x)^2)=
        ∫ x in Q0, (T a x)^2 := by
      apply setIntegral_congr_fun hQ0.measurableSet
      intro x hx
      change (Yau.realDifferenceQuotient i h (V0 a) x)^2=(T a x)^2
      rw [hident a x hx]
    rw [hEq]
    exact setIntegral_le_integral (hwt.1 a).1.integrable_sq
      (Filter.Eventually.of_forall (fun x ↦ sq_nonneg _))

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_RealHilbertWeakLimit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau
open Filter Set
open scoped Topology
noncomputable section

theorem real_hilbert_bounded_pairing_limit {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] (u : ℕ → E) (C : ℝ)
    (hu : ∀ n, ‖u n‖ ≤ C) :
    ∃ v : E, ‖v‖ ≤ C ∧ ∀ (w : E) (a : ℝ),
      Tendsto (fun n ↦ inner ℝ (u n) w) atTop (𝓝 a) → inner ℝ v w=a := by
  let f : ℕ → WeakDual ℝ E := fun n ↦ (InnerProductSpace.toDual ℝ E (u n)).toWeakDual
  have hmem : ∀ n, f n ∈ WeakDual.toStrongDual ⁻¹' Metric.closedBall (0 : StrongDual ℝ E) C := by
    intro n
    simpa only [f,Set.mem_preimage,Metric.mem_closedBall,dist_zero_right,
      StrongDual.toStrongDual_toWeakDual,LinearIsometryEquiv.norm_map] using hu n
  obtain ⟨g,hg,hcluster⟩ := (WeakDual.isCompact_closedBall (0 : StrongDual ℝ E) C).exists_mapClusterPt (f := atTop) (u := f)
    (Filter.tendsto_principal.mpr (Filter.Eventually.of_forall hmem))
  let v := (InnerProductSpace.toDual ℝ E).symm g.toStrongDual
  refine ⟨v,?_,fun w a ha ↦ ?_⟩
  · change ‖(InnerProductSpace.toDual ℝ E).symm g.toStrongDual‖ ≤ C
    simpa only [LinearIsometryEquiv.norm_map,Set.mem_preimage,Metric.mem_closedBall,dist_zero_right] using hg
  · have hc := hcluster.continuousAt_comp (WeakDual.eval_continuous w).continuousAt
    have hc' : MapClusterPt (inner ℝ v w) atTop (fun n ↦ inner ℝ (u n) w) := by
      simpa only [Function.comp_def,v,f,InnerProductSpace.toDual_symm_apply,WeakDual.toStrongDual_apply,
        StrongDual.toWeakDual_apply,InnerProductSpace.toDual_apply_apply] using hc
    exact eq_of_nhds_neBot (hc'.clusterPt.mono ha).neBot

end
end Yau

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_RealInteriorDifferencePairingLemmas
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Yau

open MeasureTheory Yau.Geometry Set Filter
open scoped ContDiff Topology

theorem real_nested_difference_pairing (R r e : ℝ) (hr : r ≤ R) (he : e ≤ R-r) (u psi : Jets.Coord → ℝ)
    (hu : MemLp u 2 (volume.restrict (realCenteredCube 4 R)))
    (hp : ContDiff ℝ ∞ psi) (hc : HasCompactSupport psi)
    (hs : tsupport psi ⊆ realCenteredCube 4 r)
    (i : Fin 4) (h : ℝ) (hh : |h| ≤ e) :
    (∫ x in realCenteredCube 4 r, realDifferenceQuotient i h u x*psi x) =
      -(∫ x in realCenteredCube 4 R, u x*realDifferenceQuotient i (-h) psi x) := by
  let U := (realCenteredCube 4 R).indicator u
  have hU : MemLp U 2 volume := (memLp_indicator_iff_restrict (realCenteredCube_isCompact 4 R).measurableSet).mpr hu
  have hpsi := real_compact_continuous_memLp psi hp.continuous hc
  have heq := (real_differenceQuotient_pairing i h U psi hU hpsi).2.2
  have hz (x : Jets.Coord) (hx : x ∉ realCenteredCube 4 r) : psi x=0 :=
    image_eq_zero_of_notMem_tsupport (fun ht ↦ hx (hs ht))
  have hleft : (∫ x, realDifferenceQuotient i h U x*psi x) =
      ∫ x in realCenteredCube 4 r, realDifferenceQuotient i h u x*psi x := by
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := realCenteredCube 4 r)
      (fun x hx ↦ by rw [hz x hx,mul_zero])]
    apply setIntegral_congr_fun (realCenteredCube_isCompact 4 r).measurableSet
    intro x hx
    have hx0 : x ∈ realCenteredCube 4 R := realCenteredCube_mono hr hx
    have hxt : x+Pi.single i h ∈ realCenteredCube 4 R := by
      apply realCenteredCube_shift i (h := -h) (r := r)
        (by simpa only [abs_neg] using (show |h| ≤ R-r by linarith))
      simpa only [Pi.single_neg,add_neg_cancel_right] using hx
    simp only [realDifferenceQuotient,U,indicator_of_mem hx0,indicator_of_mem hxt]
  have hright : (∫ x, U x*realDifferenceQuotient i (-h) psi x) =
      ∫ x in realCenteredCube 4 R, u x*realDifferenceQuotient i (-h) psi x := by
    change (∫ x, ((realCenteredCube 4 R).indicator u) x*realDifferenceQuotient i (-h) psi x) = _
    simp only [← Set.indicator_mul_left]
    exact integral_indicator (show MeasurableSet (realCenteredCube 4 R) from
      (realCenteredCube_isCompact 4 R).measurableSet)
  rw [hleft,hright] at heq
  exact heq

theorem real_nested_difference_pairing_tendsto (R r e : ℝ) (hr : r ≤ R) (he : e ≤ R-r) (u psi : Jets.Coord → ℝ)
    (hu : MemLp u 2 (volume.restrict (realCenteredCube 4 R)))
    (hp : ContDiff ℝ ∞ psi) (hc : HasCompactSupport psi)
    (hs : tsupport psi ⊆ realCenteredCube 4 r)
    (i : Fin 4) (h : ℕ → ℝ) (hh : ∀ k, |h k| ≤ e)
    (hlim : Tendsto (fun k ↦ -h k) atTop (𝓝[≠] (0:ℝ))) :
    Tendsto (fun k ↦ ∫ x in realCenteredCube 4 r, realDifferenceQuotient i (h k) u x*psi x) atTop
      (𝓝 (-(∫ x in realCenteredCube 4 r, u x*coordPartial psi x i))) := by
  let : IsFiniteMeasure (volume.restrict (realCenteredCube 4 R)) :=
    isFiniteMeasure_restrict.mpr (realCenteredCube_isCompact 4 R).measure_ne_top
  have hI : Integrable u (volume.restrict (realCenteredCube 4 R)) := hu.integrable (by norm_num)
  have ht := (real_smooth_difference_integral_tendsto (volume.restrict (realCenteredCube 4 R))
    u psi hI hp hc i (fun k ↦ -h k) hlim).neg
  have hd : tsupport (fun x ↦ coordPartial psi x i) ⊆ realCenteredCube 4 r :=
    (tsupport_fderiv_apply_subset ℝ (Pi.single i 1)).trans hs
  have hz (x : Jets.Coord) (hx : x ∉ realCenteredCube 4 r) : u x*coordPartial psi x i=0 := by
    rw [image_eq_zero_of_notMem_tsupport (f := fun y ↦ coordPartial psi y i)
      (fun ht ↦ hx (hd ht)),mul_zero]
  have hsame : (∫ x in realCenteredCube 4 R, u x*coordPartial psi x i) =
      ∫ x in realCenteredCube 4 r, u x*coordPartial psi x i := by
    have hlarge : (∫ x in realCenteredCube 4 R, u x*coordPartial psi x i) =
        ∫ x, u x*coordPartial psi x i :=
      setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx ↦ hz x
        (fun hm ↦ hx (realCenteredCube_mono hr hm)))
    have hsmall : (∫ x in realCenteredCube 4 r, u x*coordPartial psi x i) =
        ∫ x, u x*coordPartial psi x i := setIntegral_eq_integral_of_forall_compl_eq_zero hz
    exact hlarge.trans hsmall.symm
  rw [hsame] at ht
  convert ht using 1
  all_goals try with_reducible_and_instances rfl
  funext k
  exact real_nested_difference_pairing R r e hr he u psi hu hp hc hs i (h k) (hh k)

end Yau

end

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_RealNestedWeakDerivative
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau
open MeasureTheory Yau.Geometry Set Filter
open scoped ContDiff Topology
noncomputable section

theorem real_nested_weak_derivative_of_difference_bound
    (R r e : ℝ) (hr : r ≤ R) (he : 0 < e) (hem : e ≤ R-r)
    (u : Jets.Coord → ℝ) (hu : MemLp u 2 (volume.restrict (realCenteredCube 4 R)))
    (i : Fin 4) (C : ℝ) (hC : 0 ≤ C)
    (hM : ∀ h : ℝ, |h| ≤ e → MemLp (realDifferenceQuotient i h u) 2
      (volume.restrict (realCenteredCube 4 r)))
    (hb : ∀ h : ℝ, |h| ≤ e →
      (∫ x in realCenteredCube 4 r, (realDifferenceQuotient i h u x)^2) ≤ C) :
    ∃ H : Lp ℝ 2 (volume.restrict (realCenteredCube 4 r)), ‖H‖^2 ≤ C ∧
      ∀ psi : Jets.Coord → ℝ, ContDiff ℝ ∞ psi → HasCompactSupport psi →
        tsupport psi ⊆ realCenteredCube 4 r →
        IntegrableOn (fun x ↦ u x*coordPartial psi x i) (realCenteredCube 4 r) ∧
        IntegrableOn (fun x ↦ H x*psi x) (realCenteredCube 4 r) ∧
        (∫ x in realCenteredCube 4 r, u x*coordPartial psi x i) =
          -(∫ x in realCenteredCube 4 r, H x*psi x) := by
  let h : ℕ → ℝ := fun n ↦ (e)*(1/((n:ℝ)+1))
  have hpos (n : ℕ) : 0 < h n := by dsimp [h] <;> positivity
  have hh (n : ℕ) : |h n| ≤ e := by
    rw [abs_of_pos (hpos n)]
    dsimp [h]
    have hn : 1/((n:ℝ)+1) ≤ 1 := (div_le_one (by positivity)).mpr (by linarith [Nat.cast_nonneg (α := ℝ) n])
    nlinarith
  have ht : Tendsto h atTop (𝓝 (0:ℝ)) := by
    simpa only [mul_zero] using tendsto_one_div_add_atTop_nhds_zero_nat.const_mul (e:ℝ)
  have hneg : Tendsto (fun n ↦ -h n) atTop (𝓝[≠] (0:ℝ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨by simpa only [neg_zero] using ht.neg,Filter.Eventually.of_forall (fun n ↦ ?_)⟩
    simpa using (neg_ne_zero.mpr (hpos n).ne')
  let W (n : ℕ) : Lp ℝ 2 (volume.restrict (realCenteredCube 4 r)) :=
    (hM (h n) (hh n)).toLp (realDifferenceQuotient i (h n) u)
  have hW (n : ℕ) : ‖W n‖ ≤ Real.sqrt C := by
    have hnorm : ‖W n‖^2 = ∫ x in realCenteredCube 4 r, (realDifferenceQuotient i (h n) u x)^2 :=
      real_toLp_norm_sq _ (hM (h n) (hh n))
    have hsq := hb (h n) (hh n)
    rw [← hnorm] at hsq
    nlinarith [Real.sq_sqrt hC,Real.sqrt_nonneg C,norm_nonneg (W n)]
  obtain ⟨H,hH,hpair⟩ := real_hilbert_bounded_pairing_limit W (Real.sqrt C) hW
  refine ⟨H,by nlinarith [Real.sq_sqrt hC,norm_nonneg H],?_⟩
  intro psi hp hc hs
  have hpsi : MemLp psi 2 (volume.restrict (realCenteredCube 4 r)) :=
    (real_compact_continuous_memLp psi hp.continuous hc).mono_measure Measure.restrict_le_self
  let test := hpsi.toLp psi
  have hlim := real_nested_difference_pairing_tendsto R r e hr hem u psi hu hp hc hs i h hh hneg
  have hinner (n : ℕ) : inner ℝ (W n) test =
      ∫ x in realCenteredCube 4 r, realDifferenceQuotient i (h n) u x*psi x := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [(hM (h n) (hh n)).coeFn_toLp,hpsi.coeFn_toLp] with x hx hy
    change test x*W n x=_
    rw [hx,hy,mul_comm]
  have hid := hpair test (-(∫ x in realCenteredCube 4 r, u x*coordPartial psi x i))
    (by simpa only [hinner] using hlim)
  have hHrep : inner ℝ H test = ∫ x in realCenteredCube 4 r, H x*psi x := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hpsi.coeFn_toLp] with x hx
    change test x*H x=_
    rw [hx,mul_comm]
  rw [hHrep] at hid
  have hu' : MemLp u 2 (volume.restrict (realCenteredCube 4 r)) :=
    hu.mono_measure (Measure.restrict_mono (realCenteredCube_mono hr) le_rfl)
  have hdpsi : MemLp (fun x ↦ coordPartial psi x i) 2 (volume.restrict (realCenteredCube 4 r)) :=
    (real_compact_continuous_memLp _ (real_coordPartial_smooth psi hp i).continuous
      (hc.fderiv_apply ℝ (Pi.single i 1))).mono_measure Measure.restrict_le_self
  exact ⟨hu'.integrable_mul hdpsi,(Lp.memLp H).integrable_mul hpsi,by linarith only [hid]⟩

end
end Yau

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Charts_SphereInteriorWeakDerivativeGain
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open MeasureTheory Yau.Geometry Set
open scoped ContDiff
noncomputable section

theorem sphere_interior_weak_derivative_gain (d : SphereEnergyData) (p : Base)
    (R0 r : ℝ) (hr : r < R0) (hR : R0 ≤ 1) :
    ∃ C > 0,
      ∀ (u : Yau.Jets.Coord → ℝ) (V0 P0 G : Fin 4 → Yau.Jets.Coord → ℝ)
        (DG : Fin 4 → Fin 4 → Yau.Jets.Coord → ℝ) (F0 : Yau.Jets.Coord → ℝ),
      let Q := Yau.realCenteredCube 4 R0
      MemLp u 2 (volume.restrict Q) →
      (∀ a, MemLp (V0 a) 2 (volume.restrict Q)) →
      (∀ a, MemLp (P0 a) 2 (volume.restrict Q)) →
      (∀ j, MemLp (G j) 2 (volume.restrict Q)) →
      (∀ j i, MemLp (DG j i) 2 (volume.restrict Q)) →
      MemLp F0 2 (volume.restrict Q) →
      (∀ a, P0 a =ᵐ[volume.restrict (interior Q)] V0 a) →
      (∀ j psi, ContDiff ℝ ∞ psi → HasCompactSupport psi → tsupport psi ⊆ Q →
        (∫ x in Q, u x*Yau.coordPartial psi x j)=-(∫ x in Q, V0 j x*psi x)) →
      (∀ j i psi, ContDiff ℝ ∞ psi → HasCompactSupport psi → tsupport psi ⊆ Q →
        (∫ x in Q, G j x*Yau.coordPartial psi x i)=-(∫ x in Q, DG j i x*psi x)) →
      (∀ psi, ContDiff ℝ ∞ psi → HasCompactSupport psi → tsupport psi ⊆ Q →
        (∑ a, ∑ j, ∫ x in Q, sphereChartPrincipalDensity d p x a j*P0 a x*Yau.coordPartial psi x j)=
          (∫ x in Q, F0 x*psi x)-(∑ j, ∫ x in Q, G j x*Yau.coordPartial psi x j)) →
      ∀ E : ℝ, 0 ≤ E →
        (∫ x in Q, (u x)^2) ≤ E →
        (∀ a, (∫ x in Q, (V0 a x)^2) ≤ E) →
        (∫ x in Q, (F0 x)^2) ≤ E →
        (∀ j, (∫ x in Q, (G j x)^2) ≤ E) →
        (∀ j i, (∫ x in Q, (DG j i x)^2) ≤ E) →
        ∃ H : Fin 4 → Fin 4 → Lp ℝ 2 (volume.restrict (Yau.realCenteredCube 4 r)),
          (∑ a, ∑ i, ‖H a i‖^2) ≤ C*E ∧
          ∀ a i psi, ContDiff ℝ ∞ psi → HasCompactSupport psi →
            tsupport psi ⊆ Yau.realCenteredCube 4 r →
            IntegrableOn (fun x ↦ V0 a x*Yau.coordPartial psi x i) (Yau.realCenteredCube 4 r) ∧
            IntegrableOn (fun x ↦ H a i x*psi x) (Yau.realCenteredCube 4 r) ∧
            (∫ x in Yau.realCenteredCube 4 r, V0 a x*Yau.coordPartial psi x i)=
              -(∫ x in Yau.realCenteredCube 4 r, H a i x*psi x) := by
  obtain ⟨B,hB,hgain⟩ := sphere_interior_difference_bound d p R0 r hr hR
  refine ⟨16*B,by positivity,?_⟩
  intro u V0 P0 G DG F0
  dsimp only
  intro hu hv hp hg hd hf hsame hweak hcomm hequation E hE hbu hbv hbf hbg hbd
  have hdiff := hgain u V0 P0 G DG F0 hu hv hp hg hd hf hsame hweak hcomm hequation
    E hE hbu hbv hbf hbg hbd
  have hder (a i : Fin 4) :
      ∃ H : Lp ℝ 2 (volume.restrict (Yau.realCenteredCube 4 r)), ‖H‖^2 ≤ B*E ∧
        ∀ psi : Yau.Jets.Coord → ℝ, ContDiff ℝ ∞ psi → HasCompactSupport psi →
          tsupport psi ⊆ Yau.realCenteredCube 4 r →
          IntegrableOn (fun x ↦ V0 a x*Yau.coordPartial psi x i) (Yau.realCenteredCube 4 r) ∧
          IntegrableOn (fun x ↦ H x*psi x) (Yau.realCenteredCube 4 r) ∧
          (∫ x in Yau.realCenteredCube 4 r, V0 a x*Yau.coordPartial psi x i)=
            -(∫ x in Yau.realCenteredCube 4 r, H x*psi x) := by
    apply Yau.real_nested_weak_derivative_of_difference_bound R0 r ((R0-r)/8)
      hr.le (by linarith) (by linarith) (V0 a) (hv a) i (B*E) (mul_nonneg hB.le hE)
      (fun h hh ↦ (hdiff i h hh).1 a)
    intro h hh
    exact (Finset.single_le_sum (f := fun b ↦ ∫ x in Yau.realCenteredCube 4 r,
      (Yau.realDifferenceQuotient i h (V0 b) x)^2)
      (fun b _ ↦ integral_nonneg (fun x ↦ sq_nonneg _)) (Finset.mem_univ a)).trans (hdiff i h hh).2
  choose H hH hpair using hder
  refine ⟨H,?_,hpair⟩
  have ht := Finset.sum_le_sum (s := Finset.univ) (fun a _ ↦
    Finset.sum_le_sum (s := Finset.univ) (fun i _ ↦ hH a i))
  norm_num only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_ofNat] at ht
  exact ht.trans_eq (by ring)

end
end Yau.Target

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

theorem real_interior_weak_sum {n : ℕ} {I : Type*} [Fintype I]
    {K : Set (Coord n)} (hK : IsCompact K) (u g : I → Coord n → ℝ)
    (hu : ∀ a, MemLp (u a) 2 (volume.restrict K))
    (hg : ∀ a, MemLp (g a) 2 (volume.restrict K)) (i : Fin n)
    (hweak : ∀ a psi, ContDiff ℝ ∞ psi → HasCompactSupport psi → tsupport psi ⊆ K →
      (∫ x in K, u a x*coordPartial psi x i)=-(∫ x in K, g a x*psi x)) :
    MemLp (fun x ↦ ∑ a, u a x) 2 (volume.restrict K) ∧
    MemLp (fun x ↦ ∑ a, g a x) 2 (volume.restrict K) ∧
    ∀ psi : Coord n → ℝ, ContDiff ℝ ∞ psi → HasCompactSupport psi → tsupport psi ⊆ K →
      IntegrableOn (fun x ↦ (∑ a, u a x)*coordPartial psi x i) K ∧
      IntegrableOn (fun x ↦ (∑ a, g a x)*psi x) K ∧
      (∫ x in K, (∑ a, u a x)*coordPartial psi x i)=-(∫ x in K, (∑ a, g a x)*psi x) := by
  have hsu : MemLp (fun x ↦ ∑ a, u a x) 2 (volume.restrict K) := memLp_finsetSum _ (fun a _ ↦ hu a)
  have hsg : MemLp (fun x ↦ ∑ a, g a x) 2 (volume.restrict K) := memLp_finsetSum _ (fun a _ ↦ hg a)
  refine ⟨hsu,hsg,fun psi hp hc hs ↦ ?_⟩
  have ht := real_continuous_memLp_compact hK psi hp.continuous
  have hdt := real_continuous_memLp_compact hK _ (real_coordPartial_smooth psi hp i).continuous
  refine ⟨hsu.integrable_mul hdt,hsg.integrable_mul ht,?_⟩
  have hiu (a : I) : IntegrableOn (fun x ↦ u a x*coordPartial psi x i) K := (hu a).integrable_mul hdt
  have hig (a : I) : IntegrableOn (fun x ↦ g a x*psi x) K := (hg a).integrable_mul ht
  simp_rw [Finset.sum_mul]
  rw [integral_finsetSum Finset.univ (fun a _ ↦ hiu a),
    integral_finsetSum Finset.univ (fun a _ ↦ hig a)]
  simp only [hweak _ psi hp hc hs,Finset.sum_neg_distrib]

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

theorem real_weak_jet_leibniz_pairing {Q : Set Jets.Coord} (hQ : IsCompact Q)
    (A : Jets.Coord → ℝ) (hA : ContDiff ℝ ∞ A)
    (U : List (Fin 4) → Jets.Coord → ℝ) (N : ℕ)
    (hU : ∀ es, es.length ≤ N+1 → MemLp (U es) 2 (volume.restrict Q))
    (hweak : ∀ es, es.length ≤ N → ∀ i psi,
      ContDiff ℝ ∞ psi → HasCompactSupport psi → tsupport psi ⊆ Q →
      (∫ x in Q, U es x*coordPartial psi x i)=-(∫ x in Q, U (i::es) x*psi x))
    (extra ds : List (Fin 4)) (he : extra.length ≤ 1) (hd : ds.length ≤ N)
    (psi : Jets.Coord → ℝ) (hp : ContDiff ℝ ∞ psi)
    (hc : HasCompactSupport psi) (hs : tsupport psi ⊆ Q) :
    (∫ x in Q, realWeakJetExpansion A U extra ds x*psi x) =
      (-1:ℝ)^ds.length * (∫ x in Q, A x*U extra x*partialJet psi ds.reverse x) := by
  have h := real_weak_jet_test_reversal (realWeakJetExpansion A U extra) N
    (fun es hh i psi hp hc hs ↦
      ((real_weak_jet_expansion_derivative hQ A hA U N hU hweak extra es he hh i).2.2
        psi hp hc hs).2.2) ds hd psi hp hc hs
  simpa only [realWeakJetExpansion,realJetErrorTerms,realWeakJetProductSum,List.append_nil,
    List.map_nil,List.sum_nil,add_zero] using h

end
end Yau

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_RealWeakJetEquation
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

lemma partialJet_coordPartial_word {n : ℕ} (f : Coord n → ℝ) (hf : ContDiff ℝ ∞ f)
    (ds : List (Fin n)) (j : Fin n) :
    partialJet (fun x ↦ coordPartial f x j) ds = fun x ↦ coordPartial (partialJet f ds) x j := by
  change partialJet (partialJet f [j]) ds = partialJet f (j::ds)
  rw [← partialJet_append_word]
  exact partialJet_perm_word f hf (List.perm_append_singleton j ds)

theorem real_finite_weak_jet_equation {Q : Set Jets.Coord} (hQ : IsCompact Q)
    (C : Jets.Coord → Fin 4 → Fin 4 → ℝ) (B : Jets.Coord → ℝ)
    (hC : ∀ a j, ContDiff ℝ ∞ (fun x ↦ C x a j)) (hB : ContDiff ℝ ∞ B)
    (U : List (Fin 4) → Jets.Coord → ℝ) (N : ℕ)
    (hU : ∀ es, es.length ≤ N+1 → MemLp (U es) 2 (volume.restrict Q))
    (hweak : ∀ es, es.length ≤ N → ∀ i psi,
      ContDiff ℝ ∞ psi → HasCompactSupport psi → tsupport psi ⊆ Q →
      (∫ x in Q, U es x*coordPartial psi x i)=-(∫ x in Q, U (i::es) x*psi x))
    (heq : ∀ psi, ContDiff ℝ ∞ psi → HasCompactSupport psi → tsupport psi ⊆ Q →
      (∑ a, ∑ j, ∫ x in Q, C x a j*U [a] x*coordPartial psi x j) =
        ∫ x in Q, B x*U [] x*psi x)
    (ds : List (Fin 4)) (hd : ds.length ≤ N) :
    let F := fun x ↦ B x*U ds x+realWeakJetProductSum B U (realJetErrorTerms [] ds) x
    let G := fun j x ↦ ∑ a, realWeakJetProductSum (fun y ↦ C y a j) U (realJetErrorTerms [a] ds) x
    MemLp F 2 (volume.restrict Q) ∧ (∀ j, MemLp (G j) 2 (volume.restrict Q)) ∧
    ∀ psi : Jets.Coord → ℝ, ContDiff ℝ ∞ psi → HasCompactSupport psi → tsupport psi ⊆ Q →
      (∀ a j, IntegrableOn (fun x ↦ C x a j*U (a::ds) x*coordPartial psi x j) Q) ∧
      IntegrableOn (fun x ↦ F x*psi x) Q ∧
      (∀ j, IntegrableOn (fun x ↦ G j x*coordPartial psi x j) Q) ∧
      (∑ a, ∑ j, ∫ x in Q, C x a j*U (a::ds) x*coordPartial psi x j) =
        (∫ x in Q, F x*psi x)-∑ j, ∫ x in Q, G j x*coordPartial psi x j := by
  let err (a j : Fin 4) := realWeakJetProductSum (fun y ↦ C y a j) U (realJetErrorTerms [a] ds)
  have hm (a j : Fin 4) : MemLp (fun x ↦ C x a j*U (a::ds) x) 2 (volume.restrict Q) := by
    obtain ⟨_,_,hb⟩ := real_compact_multiplier_bound hQ _ (hC a j).continuous
    exact (hb _ (hU _ (by simp only [List.length_cons]; omega))).1
  have herr (a j : Fin 4) : MemLp (err a j) 2 (volume.restrict Q) :=
    real_weak_jet_product_memLp hQ _ (hC a j) U _ (fun t ht ↦ hU _ (by
      have ht' := (realJetErrorTerms_orders [a] ds (by simp) t ht).2; omega))
  have hg (j : Fin 4) : MemLp (fun x ↦ ∑ a, err a j x) 2 (volume.restrict Q) :=
    memLp_finsetSum _ (fun a _ ↦ herr a j)
  have hf := real_weak_jet_expansion_memLp hQ B hB U N hU [] ds (by simp) hd
  refine ⟨hf,hg,?_⟩
  intro psi hp hc hs
  have hdt (j : Fin 4) := real_continuous_memLp_compact hQ _ (real_coordPartial_smooth psi hp j).continuous
  have hi (a j : Fin 4) := (hm a j).integrable_mul (hdt j)
  have hei (a j : Fin 4) := (herr a j).integrable_mul (hdt j)
  refine ⟨hi,hf.integrable_mul (real_continuous_memLp_compact hQ psi hp.continuous),
    fun j ↦ (hg j).integrable_mul (hdt j),?_⟩
  have hflux (a j : Fin 4) := real_weak_jet_leibniz_pairing hQ (fun x ↦ C x a j) (hC a j)
    U N hU hweak [a] ds (by simp) hd (fun x ↦ coordPartial psi x j)
    (real_coordPartial_smooth psi hp j) (hc.fderiv_apply ℝ (Pi.single j 1))
    ((tsupport_fderiv_apply_subset ℝ (Pi.single j 1)).trans hs)
  have hscalar := real_weak_jet_leibniz_pairing hQ B hB U N hU hweak [] ds (by simp) hd psi hp hc hs
  have htotal : (∑ a, ∑ j, ∫ x in Q,
      realWeakJetExpansion (fun y ↦ C y a j) U [a] ds x*coordPartial psi x j) =
      ∫ x in Q, realWeakJetExpansion B U [] ds x*psi x := by
    simp_rw [hflux,partialJet_coordPartial_word psi hp]
    simp_rw [← Finset.mul_sum]
    rw [heq _ (partialJet_smooth psi hp ds.reverse) (partialJet_compactSupport psi hc ds.reverse)
      ((partialJet_tsupport_subset psi ds.reverse).trans hs)]
    exact hscalar.symm
  have hsplit (a j : Fin 4) : (∫ x in Q,
      realWeakJetExpansion (fun y ↦ C y a j) U [a] ds x*coordPartial psi x j) =
      (∫ x in Q, C x a j*U (a::ds) x*coordPartial psi x j)+
        ∫ x in Q, err a j x*coordPartial psi x j := by
    simp only [realWeakJetExpansion,List.cons_append,List.nil_append,add_mul]
    exact integral_add (hi a j) (hei a j)
  have hgsplit (j : Fin 4) : (∫ x in Q, (∑ a, err a j x)*coordPartial psi x j) =
      ∑ a, ∫ x in Q, err a j x*coordPartial psi x j := by
    simp_rw [Finset.sum_mul]
    exact integral_finsetSum Finset.univ (fun a _ ↦ hei a j)
  simp_rw [hsplit,Finset.sum_add_distrib] at htotal
  change _ = _ - ∑ j, ∫ x in Q, (∑ a, err a j x)*coordPartial psi x j
  simp_rw [hgsplit]
  rw [Finset.sum_comm (f := fun j a ↦ ∫ x in Q, err a j x*coordPartial psi x j)]
  exact eq_sub_iff_add_eq.mpr htotal

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
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_RealWeakJetErrorBounds
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

theorem real_weak_jet_error_H1_bound {Q : Set Jets.Coord} (hQ : IsCompact Q)
    (A : Jets.Coord → ℝ) (hA : ContDiff ℝ ∞ A)
    (N : ℕ) (extra ds : List (Fin 4)) (he : extra.length ≤ 1) (hs : ds.length ≤ N)
    (i : Fin 4) :
    ∃ C > 0, ∀ U : List (Fin 4) → Jets.Coord → ℝ,
      (∀ es, es.length ≤ N+1 → MemLp (U es) 2 (volume.restrict Q)) →
      (∀ es, es.length ≤ N → ∀ psi : Jets.Coord → ℝ,
        ContDiff ℝ ∞ psi → HasCompactSupport psi → tsupport psi ⊆ Q →
        (∫ x in Q, U es x*coordPartial psi x i)=-(∫ x in Q, U (i::es) x*psi x)) →
      ∀ E : ℝ, 0 ≤ E → (∀ es, es.length ≤ N+1 → (∫ x in Q, (U es x)^2) ≤ E) →
      let ts := realJetErrorTerms extra ds
      let V := realWeakJetProductSum A U ts
      let D := realWeakJetProductSum A U
        (ts.map (fun t ↦ (i::t.1,t.2)) ++ ts.map (fun t ↦ (t.1,i::t.2)))
      (MemLp V 2 (volume.restrict Q) ∧ (∫ x in Q, (V x)^2) ≤ C*E) ∧
      (MemLp D 2 (volume.restrict Q) ∧ (∫ x in Q, (D x)^2) ≤ C*E) ∧
      ∀ psi : Jets.Coord → ℝ, ContDiff ℝ ∞ psi → HasCompactSupport psi → tsupport psi ⊆ Q →
        IntegrableOn (fun x ↦ V x*coordPartial psi x i) Q ∧
        IntegrableOn (fun x ↦ D x*psi x) Q ∧
        (∫ x in Q, V x*coordPartial psi x i)=-(∫ x in Q, D x*psi x) := by
  let ts := realJetErrorTerms extra ds
  let ss := ts.map (fun t ↦ (i::t.1,t.2)) ++ ts.map (fun t ↦ (t.1,i::t.2))
  have hord (t : List (Fin 4) × List (Fin 4)) (ht : t ∈ ts) : t.2.length ≤ N :=
    ((realJetErrorTerms_orders extra ds he t ht).2).trans hs
  have hdord (t : List (Fin 4) × List (Fin 4)) (ht : t ∈ ss) : t.2.length ≤ N+1 := by
    simp only [ss,List.mem_append,List.mem_map] at ht
    rcases ht with ⟨s,hmem,rfl⟩ | ⟨s,hmem,rfl⟩
    · exact (hord s hmem).trans (Nat.le_succ N)
    · simpa only [List.length_cons] using Nat.succ_le_succ (hord s hmem)
  obtain ⟨B,hB,hb⟩ := real_weak_jet_product_bound hQ A hA ts
  obtain ⟨D,hD,hd⟩ := real_weak_jet_product_bound hQ A hA ss
  refine ⟨B+D,by positivity,fun U hU hweak E hE hUE ↦ ?_⟩
  dsimp only
  have hts (t : List (Fin 4) × List (Fin 4)) (ht : t ∈ ts) : t.2.length ≤ N+1 :=
    (hord t ht).trans (Nat.le_succ N)
  have hv := hb U (fun t ht ↦ hU _ (hts t ht)) E hE (fun t ht ↦ hUE _ (hts t ht))
  have hdv := hd U (fun t ht ↦ hU _ (hdord t ht)) E hE (fun t ht ↦ hUE _ (hdord t ht))
  have hw := real_weak_jet_product_derivative hQ A hA U ts i
    (fun t ht ↦ hU _ (hts t ht))
    (fun t ht ↦ hU _ (by simpa only [List.length_cons] using Nat.succ_le_succ (hord t ht)))
    (fun t ht ↦ hweak _ (hord t ht))
  exact ⟨⟨hv.1,hv.2.trans (mul_le_mul_of_nonneg_right (by linarith) hE)⟩,
    ⟨hdv.1,hdv.2.trans (mul_le_mul_of_nonneg_right (by linarith) hE)⟩,hw.2.2⟩

end
end Yau

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_RealWeakJetForcingBounds
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

theorem real_weak_jet_expansion_bound {Q : Set Jets.Coord} (hQ : IsCompact Q)
    (A : Jets.Coord → ℝ) (hA : ContDiff ℝ ∞ A)
    (N : ℕ) (extra ds : List (Fin 4)) (he : extra.length ≤ 1) (hd : ds.length ≤ N) :
    ∃ C > 0, ∀ U : List (Fin 4) → Jets.Coord → ℝ,
      (∀ es, es.length ≤ N+1 → MemLp (U es) 2 (volume.restrict Q)) →
      ∀ E : ℝ, 0 ≤ E → (∀ es, es.length ≤ N+1 → (∫ x in Q, (U es x)^2) ≤ E) →
      MemLp (realWeakJetExpansion A U extra ds) 2 (volume.restrict Q) ∧
      (∫ x in Q, (realWeakJetExpansion A U extra ds x)^2) ≤ C*E := by
  let ts := ([],extra++ds)::realJetErrorTerms extra ds
  have hord (t : List (Fin 4) × List (Fin 4)) (ht : t ∈ ts) : t.2.length ≤ N+1 := by
    rcases List.mem_cons.mp ht with rfl | ht
    · simp only [List.length_append]; omega
    · have h := (realJetErrorTerms_orders extra ds he t ht).2; omega
  obtain ⟨C,hC,hb⟩ := real_weak_jet_product_bound hQ A hA ts
  refine ⟨C,hC,fun U hU E hE hUE ↦ ?_⟩
  exact hb U (fun t ht ↦ hU _ (hord t ht)) E hE (fun t ht ↦ hUE _ (hord t ht))

theorem real_weak_jet_forcing_H1_bound {Q : Set Jets.Coord} (hQ : IsCompact Q)
    (C : Jets.Coord → Fin 4 → Fin 4 → ℝ) (B : Jets.Coord → ℝ)
    (hC : ∀ a j, ContDiff ℝ ∞ (fun x ↦ C x a j)) (hB : ContDiff ℝ ∞ B)
    (N : ℕ) (ds : List (Fin 4)) (hd : ds.length ≤ N) :
    ∃ K > 0, ∀ U : List (Fin 4) → Jets.Coord → ℝ,
      (∀ es, es.length ≤ N+1 → MemLp (U es) 2 (volume.restrict Q)) →
      (∀ es, es.length ≤ N → ∀ i psi,
        ContDiff ℝ ∞ psi → HasCompactSupport psi → tsupport psi ⊆ Q →
        (∫ x in Q, U es x*coordPartial psi x i)=-(∫ x in Q, U (i::es) x*psi x)) →
      ∀ E : ℝ, 0 ≤ E → (∀ es, es.length ≤ N+1 → (∫ x in Q, (U es x)^2) ≤ E) →
      (MemLp (realWeakJetExpansion B U [] ds) 2 (volume.restrict Q) ∧
        (∫ x in Q, (realWeakJetExpansion B U [] ds x)^2) ≤ K*E) ∧
      ∀ j i,
        (MemLp (realWeakJetFluxError C U ds j) 2 (volume.restrict Q) ∧
          (∫ x in Q, (realWeakJetFluxError C U ds j x)^2) ≤ K*E) ∧
        (MemLp (realWeakJetFluxErrorDerivative C U ds j i) 2 (volume.restrict Q) ∧
          (∫ x in Q, (realWeakJetFluxErrorDerivative C U ds j i x)^2) ≤ K*E) ∧
        ∀ psi, ContDiff ℝ ∞ psi → HasCompactSupport psi → tsupport psi ⊆ Q →
          IntegrableOn (fun x ↦ realWeakJetFluxError C U ds j x*coordPartial psi x i) Q ∧
          IntegrableOn (fun x ↦ realWeakJetFluxErrorDerivative C U ds j i x*psi x) Q ∧
          (∫ x in Q, realWeakJetFluxError C U ds j x*coordPartial psi x i) =
            -(∫ x in Q, realWeakJetFluxErrorDerivative C U ds j i x*psi x) := by
  obtain ⟨S,hS,hs⟩ := real_weak_jet_expansion_bound hQ B hB N [] ds (by simp) hd
  have hex (a j i : Fin 4) := real_weak_jet_error_H1_bound hQ (fun x ↦ C x a j) (hC a j)
    N [a] ds (by simp) hd i
  choose T hT ht using hex
  obtain ⟨M,hM,hm⟩ := real_finite_positive_majorant (fun t : Fin 4 × Fin 4 × Fin 4 ↦ T t.1 t.2.1 t.2.2)
  obtain ⟨D,hD,hdb⟩ := real_compact_fintype_coefficient_common_bound hQ
    (fun (_ : Jets.Coord) (_ : Fin 4) ↦ (1:ℝ)) (fun _ ↦ continuous_const)
  refine ⟨S+D*M,by positivity,fun U hU hw E hE hUE ↦ ?_⟩
  have hscalar := hs U hU E hE hUE
  refine ⟨⟨hscalar.1,hscalar.2.trans
    (mul_le_mul_of_nonneg_right (by nlinarith only [mul_pos hD hM]) hE)⟩,?_⟩
  intro j i
  have hall (a : Fin 4) := ht a j i U hU (fun es he ↦ hw es he i) E hE hUE
  have hsum := real_interior_weak_sum hQ _ _ (fun a ↦ (hall a).1.1)
    (fun a ↦ (hall a).2.1.1) i (fun a psi hp hc hs ↦ ((hall a).2.2 psi hp hc hs).2.2)
  have hb1 := hdb (fun a ↦ realWeakJetProductSum (fun y ↦ C y a j) U (realJetErrorTerms [a] ds))
    (fun a ↦ (hall a).1.1) (M*E) (mul_nonneg hM.le hE)
    (fun a ↦ ((hall a).1.2).trans (mul_le_mul_of_nonneg_right (hm ⟨a,j,i⟩) hE))
  have hb2 := hdb (fun a ↦ realWeakJetProductSum (fun y ↦ C y a j) U
      ((realJetErrorTerms [a] ds).map (fun t ↦ (i::t.1,t.2)) ++
        (realJetErrorTerms [a] ds).map (fun t ↦ (t.1,i::t.2))))
    (fun a ↦ (hall a).2.1.1) (M*E) (mul_nonneg hM.le hE)
    (fun a ↦ ((hall a).2.1.2).trans (mul_le_mul_of_nonneg_right (hm ⟨a,j,i⟩) hE))
  simp only [one_mul] at hb1 hb2
  have hbound : D*(M*E) ≤ (S+D*M)*E := by nlinarith only [mul_nonneg hS.le hE]
  exact ⟨⟨hsum.1,hb1.2.trans hbound⟩,⟨hsum.2.1,hb2.2.trans hbound⟩,hsum.2.2⟩

end
end Yau

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Charts_SphereFiniteWeakJetGain
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open MeasureTheory Set Yau.Geometry
open scoped ContDiff
noncomputable section

theorem sphere_finite_weak_jet_gain (d : SphereEnergyData) (p : Base)
    (B : Yau.Jets.Coord → ℝ) (hB : ContDiff ℝ ∞ B)
    (R r : ℝ) (hr : r < R) (hR : R ≤ 1)
    (N : ℕ) (ds : List (Fin 4)) (hd : ds.length ≤ N) :
    ∃ K > 0, ∀ U : List (Fin 4) → Yau.Jets.Coord → ℝ,
      let Q := Yau.realCenteredCube 4 R
      (∀ es, es.length ≤ N+1 → MemLp (U es) 2 (volume.restrict Q)) →
      (∀ es, es.length ≤ N → ∀ i psi,
        ContDiff ℝ ∞ psi → HasCompactSupport psi → tsupport psi ⊆ Q →
        (∫ x in Q, U es x*Yau.coordPartial psi x i)=-(∫ x in Q, U (i::es) x*psi x)) →
      (∀ psi, ContDiff ℝ ∞ psi → HasCompactSupport psi → tsupport psi ⊆ Q →
        (∑ a, ∑ j, ∫ x in Q, sphereChartPrincipalDensity d p x a j*U [a] x*Yau.coordPartial psi x j) =
          ∫ x in Q, B x*U [] x*psi x) →
      ∀ E : ℝ, 0 ≤ E → (∀ es, es.length ≤ N+1 → (∫ x in Q, (U es x)^2) ≤ E) →
      ∃ H : Fin 4 → Fin 4 → Lp ℝ 2 (volume.restrict (Yau.realCenteredCube 4 r)),
        (∑ a, ∑ i, ‖H a i‖^2) ≤ K*E ∧
        ∀ a i psi, ContDiff ℝ ∞ psi → HasCompactSupport psi →
          tsupport psi ⊆ Yau.realCenteredCube 4 r →
          IntegrableOn (fun x ↦ U (a::ds) x*Yau.coordPartial psi x i) (Yau.realCenteredCube 4 r) ∧
          IntegrableOn (fun x ↦ H a i x*psi x) (Yau.realCenteredCube 4 r) ∧
          (∫ x in Yau.realCenteredCube 4 r, U (a::ds) x*Yau.coordPartial psi x i) =
            -(∫ x in Yau.realCenteredCube 4 r, H a i x*psi x) := by
  let Q := Yau.realCenteredCube 4 R
  have hQ : IsCompact Q := Yau.realCenteredCube_isCompact 4 R
  obtain ⟨F,hF,hforcing⟩ := Yau.real_weak_jet_forcing_H1_bound hQ (sphereChartPrincipalDensity d p)
    B (sphereChartPrincipalDensity_smooth d p) hB N ds hd
  obtain ⟨C,hC,hgain⟩ := sphere_interior_weak_derivative_gain d p R r hr hR
  refine ⟨C*(F+1),by positivity,?_⟩
  intro U
  dsimp only
  intro hU hw he E hE hUE
  have hf := hforcing U hU hw E hE hUE
  have heq := Yau.real_finite_weak_jet_equation hQ (sphereChartPrincipalDensity d p) B
    (sphereChartPrincipalDensity_smooth d p) hB U N hU hw he ds hd
  have hsmall : E ≤ (F+1)*E := by nlinarith only [mul_nonneg hF.le hE]
  have hlarge : F*E ≤ (F+1)*E := by nlinarith only [hE]
  have h := hgain (U ds) (fun a ↦ U (a::ds)) (fun a ↦ U (a::ds))
    (Yau.realWeakJetFluxError (sphereChartPrincipalDensity d p) U ds)
    (Yau.realWeakJetFluxErrorDerivative (sphereChartPrincipalDensity d p) U ds)
    (Yau.realWeakJetExpansion B U [] ds)
    (hU ds (by omega)) (fun a ↦ hU _ (by simp only [List.length_cons]; omega))
    (fun a ↦ hU _ (by simp only [List.length_cons]; omega))
    (fun j ↦ (hf.2 j 0).1.1) (fun j i ↦ (hf.2 j i).2.1.1) hf.1.1
    (fun _ ↦ Filter.EventuallyEq.rfl) (hw ds hd)
    (fun j i psi hp hc hs ↦ ((hf.2 j i).2.2 psi hp hc hs).2.2)
    (fun psi hp hc hs ↦ (heq.2.2 psi hp hc hs).2.2.2)
    ((F+1)*E) (mul_nonneg (by positivity) hE)
    ((hUE ds (by omega)).trans hsmall)
    (fun a ↦ (hUE _ (by simp only [List.length_cons]; omega)).trans hsmall)
    (hf.1.2.trans hlarge) (fun j ↦ (hf.2 j 0).1.2.trans hlarge)
    (fun j i ↦ (hf.2 j i).2.1.2.trans hlarge)
  simpa only [mul_assoc] using h

end
end Yau.Target

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
-- module Solutions.OAIQ237_NY.NodalSets_Charts_SphereUniformWeakJetGain
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open MeasureTheory Set Yau.Geometry
open scoped ContDiff
noncomputable section

theorem sphere_uniform_weak_jet_gain (d : SphereEnergyData) (p : Base)
    (B : Yau.Jets.Coord → ℝ) (hB : ContDiff ℝ ∞ B)
    (R r : ℝ) (hr : r < R) (hR : R ≤ 1) (N : ℕ) :
    ∃ K > 0, ∀ U : List (Fin 4) → Yau.Jets.Coord → ℝ,
      let Q := Yau.realCenteredCube 4 R
      (∀ es, es.length ≤ N+1 → MemLp (U es) 2 (volume.restrict Q)) →
      (∀ es, es.length ≤ N → ∀ i psi,
        ContDiff ℝ ∞ psi → HasCompactSupport psi → tsupport psi ⊆ Q →
        (∫ x in Q, U es x*Yau.coordPartial psi x i)=-(∫ x in Q, U (i::es) x*psi x)) →
      (∀ psi, ContDiff ℝ ∞ psi → HasCompactSupport psi → tsupport psi ⊆ Q →
        (∑ a, ∑ j, ∫ x in Q, sphereChartPrincipalDensity d p x a j*U [a] x*Yau.coordPartial psi x j) =
          ∫ x in Q, B x*U [] x*psi x) →
      ∀ E : ℝ, 0 ≤ E → (∀ es, es.length ≤ N+1 → (∫ x in Q, (U es x)^2) ≤ E) →
      ∀ ds, ds.length ≤ N →
      ∃ H : Fin 4 → Fin 4 → Lp ℝ 2 (volume.restrict (Yau.realCenteredCube 4 r)),
        (∑ a, ∑ i, ‖H a i‖^2) ≤ K*E ∧
        ∀ a i psi, ContDiff ℝ ∞ psi → HasCompactSupport psi →
          tsupport psi ⊆ Yau.realCenteredCube 4 r →
          IntegrableOn (fun x ↦ U (a::ds) x*Yau.coordPartial psi x i) (Yau.realCenteredCube 4 r) ∧
          IntegrableOn (fun x ↦ H a i x*psi x) (Yau.realCenteredCube 4 r) ∧
          (∫ x in Yau.realCenteredCube 4 r, U (a::ds) x*Yau.coordPartial psi x i) =
            -(∫ x in Yau.realCenteredCube 4 r, H a i x*psi x) := by
  have hex (ds : List (Fin 4)) := sphere_finite_weak_jet_gain d p B hB R r hr hR ds.length ds le_rfl
  choose C hC hc using hex
  obtain ⟨K,hK,hk⟩ := Yau.real_finite_word_positive_majorant 4 N C
  refine ⟨K,hK,?_⟩
  intro U
  dsimp only
  intro hU hw he E hE hUE ds hd
  obtain ⟨H,hH,hpair⟩ := hc ds U (fun es hh ↦ hU es (by omega))
    (fun es hh ↦ hw es (by omega)) he E hE (fun es hh ↦ hUE es (by omega))
  exact ⟨H,hH.trans (mul_le_mul_of_nonneg_right (hk ds hd) hE),hpair⟩

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_RealFiniteWeakJetExtension
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau
open MeasureTheory Set
open scoped ContDiff
noncomputable section

lemma realWeakJetSuccessor_lower (U : List (Fin 4) → Coord 4 → ℝ)
    (H : List (Fin 4) → Fin 4 → Fin 4 → Coord 4 → ℝ) (N : ℕ)
    (es : List (Fin 4)) (hh : es.length ≤ N+1) : realWeakJetSuccessor U H N es=U es := by
  cases es with
  | nil => rfl
  | cons i es =>
    cases es with
    | nil => rfl
    | cons a ds =>
      have hne : ds.length ≠ N := by simp only [List.length_cons] at hh; omega
      simp only [realWeakJetSuccessor,ite_eq_right hne]

lemma realWeakJetSuccessor_top (U : List (Fin 4) → Coord 4 → ℝ)
    (H : List (Fin 4) → Fin 4 → Fin 4 → Coord 4 → ℝ) (N : ℕ)
    (ds : List (Fin 4)) (hh : ds.length=N) (a i : Fin 4) :
    realWeakJetSuccessor U H N (i::a::ds)=H ds a i := by
  simp only [realWeakJetSuccessor,ite_eq_left hh]

theorem real_finite_weak_jet_extension {Q L : Set (Coord 4)} (hQ : IsCompact Q)
    (hL : MeasurableSet L) (hsub : Q ⊆ L) (N : ℕ)
    (U : List (Fin 4) → Coord 4 → ℝ)
    (hU : ∀ es, es.length ≤ N+1 → MemLp (U es) 2 (volume.restrict L))
    (hweak : ∀ es, es.length ≤ N → ∀ i psi,
      ContDiff ℝ ∞ psi → HasCompactSupport psi → tsupport psi ⊆ L →
      (∫ x in L, U es x*coordPartial psi x i)=-(∫ x in L, U (i::es) x*psi x))
    (E K : ℝ) (hE : 0 ≤ E) (hK : 0 ≤ K)
    (hUE : ∀ es, es.length ≤ N+1 → (∫ x in L, (U es x)^2) ≤ E)
    (H : List (Fin 4) → Fin 4 → Fin 4 → Lp ℝ 2 (volume.restrict Q))
    (hH : ∀ ds, ds.length=N → (∑ a, ∑ i, ‖H ds a i‖^2) ≤ K*E)
    (hpair : ∀ ds, ds.length=N → ∀ a i psi,
      ContDiff ℝ ∞ psi → HasCompactSupport psi → tsupport psi ⊆ Q →
      (∫ x in Q, U (a::ds) x*coordPartial psi x i)=-(∫ x in Q, H ds a i x*psi x)) :
    let V := realWeakJetSuccessor U (fun ds a i ↦ H ds a i) N
    (∀ es, es.length ≤ N+1 → V es=U es) ∧
    (∀ es, es.length ≤ N+2 → MemLp (V es) 2 (volume.restrict Q) ∧
      (∫ x in Q, (V es x)^2) ≤ (K+1)*E) ∧
    ∀ es, es.length ≤ N+1 → ∀ i psi,
      ContDiff ℝ ∞ psi → HasCompactSupport psi → tsupport psi ⊆ Q →
      IntegrableOn (fun x ↦ V es x*coordPartial psi x i) Q ∧
      IntegrableOn (fun x ↦ V (i::es) x*psi x) Q ∧
      (∫ x in Q, V es x*coordPartial psi x i)=-(∫ x in Q, V (i::es) x*psi x) := by
  let V := realWeakJetSuccessor U (fun ds a i ↦ H ds a i) N
  have hlo := realWeakJetSuccessor_lower U (fun ds a i ↦ H ds a i) N
  have htop := realWeakJetSuccessor_top U (fun ds a i ↦ H ds a i) N
  have hsmall : E ≤ (K+1)*E := by nlinarith only [mul_nonneg hK hE]
  have hlarge : K*E ≤ (K+1)*E := by nlinarith only [hE]
  have hbound (es : List (Fin 4)) (he : es.length ≤ N+2) :
      MemLp (V es) 2 (volume.restrict Q) ∧ (∫ x in Q, (V es x)^2) ≤ (K+1)*E := by
    dsimp only [V]
    by_cases hle : es.length ≤ N+1
    · rw [hlo es hle]
      refine ⟨(hU es hle).mono_measure (Measure.restrict_mono hsub le_rfl),?_⟩
      have hm := integral_mono_measure (Measure.restrict_mono hsub le_rfl)
        (Filter.Eventually.of_forall (fun x ↦ sq_nonneg (U es x))) (hU es hle).integrable_sq
      exact hm.trans ((hUE es hle).trans hsmall)
    · cases es with
      | nil => simp at hle
      | cons i es =>
        cases es with
        | nil => simp at hle
        | cons a ds =>
          have hd : ds.length=N := by simp only [List.length_cons] at he hle; omega
          change MemLp (realWeakJetSuccessor U _ N (i::a::ds)) _ _ ∧ _
          rw [htop ds hd a i]
          have hb := real_Lp_restricted_square_le le_rfl (H ds a i)
          have h1 := Finset.single_le_sum (f := fun k ↦ ‖H ds a k‖^2)
            (fun k _ ↦ sq_nonneg _) (Finset.mem_univ i)
          have h2 := Finset.single_le_sum (f := fun b ↦ ∑ k, ‖H ds b k‖^2)
            (fun b _ ↦ Finset.sum_nonneg (fun k _ ↦ sq_nonneg _)) (Finset.mem_univ a)
          exact ⟨hb.1,hb.2.trans (h1.trans (h2.trans ((hH ds hd).trans hlarge)))⟩
  refine ⟨hlo,hbound,?_⟩
  intro es he i psi hp hc hs
  have hes : (i::es).length ≤ N+2 := by simp only [List.length_cons]; omega
  refine ⟨((hbound es (by omega)).1).integrable_mul
      (real_continuous_memLp_compact hQ _ (real_coordPartial_smooth psi hp i).continuous),
    ((hbound (i::es) hes).1).integrable_mul (real_continuous_memLp_compact hQ psi hp.continuous),?_⟩
  by_cases hle : es.length ≤ N
  · rw [hlo es he,hlo (i::es) (by simp only [List.length_cons]; omega)]
    exact ((real_interior_weak_restrict hQ hL hsub (U es) (U (i::es)) (hU es he)
      (hU _ (by simp only [List.length_cons]; omega)) i (hweak es hle i)).2.2 psi hp hc hs).2.2
  · cases es with
    | nil => simp at hle
    | cons a ds =>
      have hd : ds.length=N := by simp only [List.length_cons] at he hle; omega
      change (∫ x in Q, realWeakJetSuccessor U _ N (a::ds) x*coordPartial psi x i)=
        -(∫ x in Q, realWeakJetSuccessor U _ N (i::a::ds) x*psi x)
      rw [hlo (a::ds) he,htop ds hd a i]
      exact hpair ds hd a i psi hp hc hs

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
-- module Solutions.OAIQ237_NY.NodalSets_Charts_SphereWeakJetSuccessor
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open MeasureTheory Set Yau.Geometry
open scoped ContDiff
noncomputable section

theorem sphere_weak_jet_successor (d : SphereEnergyData) (p : Base)
    (B : Yau.Jets.Coord → ℝ) (hB : ContDiff ℝ ∞ B)
    (R r : ℝ) (hr : r < R) (hR : R ≤ 1) (N : ℕ) :
    ∃ K > 0, ∀ U : List (Fin 4) → Yau.Jets.Coord → ℝ,
      let Q := Yau.realCenteredCube 4 R
      (∀ es, es.length ≤ N+1 → MemLp (U es) 2 (volume.restrict Q)) →
      (∀ es, es.length ≤ N → ∀ i psi,
        ContDiff ℝ ∞ psi → HasCompactSupport psi → tsupport psi ⊆ Q →
        (∫ x in Q, U es x*Yau.coordPartial psi x i)=-(∫ x in Q, U (i::es) x*psi x)) →
      (∀ psi, ContDiff ℝ ∞ psi → HasCompactSupport psi → tsupport psi ⊆ Q →
        (∑ a, ∑ j, ∫ x in Q, sphereChartPrincipalDensity d p x a j*U [a] x*Yau.coordPartial psi x j) =
          ∫ x in Q, B x*U [] x*psi x) →
      ∀ E : ℝ, 0 ≤ E → (∀ es, es.length ≤ N+1 → (∫ x in Q, (U es x)^2) ≤ E) →
      ∃ V : List (Fin 4) → Yau.Jets.Coord → ℝ,
        let q := Yau.realCenteredCube 4 r
        (∀ es, es.length ≤ N+1 → V es=U es) ∧
        (∀ es, es.length ≤ N+2 → MemLp (V es) 2 (volume.restrict q) ∧
          (∫ x in q, (V es x)^2) ≤ K*E) ∧
        (∀ es, es.length ≤ N+1 → ∀ i psi,
          ContDiff ℝ ∞ psi → HasCompactSupport psi → tsupport psi ⊆ q →
          IntegrableOn (fun x ↦ V es x*Yau.coordPartial psi x i) q ∧
          IntegrableOn (fun x ↦ V (i::es) x*psi x) q ∧
          (∫ x in q, V es x*Yau.coordPartial psi x i)=-(∫ x in q, V (i::es) x*psi x)) ∧
        ∀ psi, ContDiff ℝ ∞ psi → HasCompactSupport psi → tsupport psi ⊆ q →
          (∑ a, ∑ j, ∫ x in q, sphereChartPrincipalDensity d p x a j*V [a] x*Yau.coordPartial psi x j) =
            ∫ x in q, B x*V [] x*psi x := by
  obtain ⟨C,hC,hgain⟩ := sphere_uniform_weak_jet_gain d p B hB R r hr hR N
  refine ⟨C+1,by positivity,?_⟩
  intro U
  dsimp only
  intro hU hw he E hE hUE
  have hex (ds : List (Fin 4)) :
      ∃ H : Fin 4 → Fin 4 → Lp ℝ 2 (volume.restrict (Yau.realCenteredCube 4 r)),
      ds.length=N → (∑ a, ∑ i, ‖H a i‖^2) ≤ C*E ∧
        ∀ a i psi, ContDiff ℝ ∞ psi → HasCompactSupport psi →
          tsupport psi ⊆ Yau.realCenteredCube 4 r →
          (∫ x in Yau.realCenteredCube 4 r, U (a::ds) x*Yau.coordPartial psi x i) =
            -(∫ x in Yau.realCenteredCube 4 r, H a i x*psi x) := by
    by_cases hd : ds.length=N
    · obtain ⟨H,hH,hpair⟩ := hgain U hU hw he E hE hUE ds hd.le
      exact ⟨H,fun _ ↦ ⟨hH,fun a i psi hp hc hs ↦ (hpair a i psi hp hc hs).2.2⟩⟩
    · exact ⟨fun _ _ ↦ 0,fun h ↦ (hd h).elim⟩
  choose H hH using hex
  let V := Yau.realWeakJetSuccessor U (fun ds a i ↦ H ds a i) N
  have hsub : Yau.realCenteredCube 4 r ⊆ Yau.realCenteredCube 4 R := Yau.realCenteredCube_mono hr.le
  have h := Yau.real_finite_weak_jet_extension (Yau.realCenteredCube_isCompact 4 r)
    (Yau.realCenteredCube_isCompact 4 R).measurableSet hsub N U hU hw E C hE hC.le hUE H
    (fun ds hd ↦ (hH ds hd).1) (fun ds hd ↦ (hH ds hd).2)
  refine ⟨V,h.1,h.2.1,h.2.2,?_⟩
  intro psi hp hc hs
  have hzero : V []=U [] := h.1 [] (by simp)
  have hone (a : Fin 4) : V [a]=U [a] := h.1 [a] (by simp)
  simp_rw [hzero,hone]
  exact Yau.real_weak_equation_restrict (Yau.realCenteredCube_isCompact 4 R).measurableSet hsub
    (sphereChartPrincipalDensity d p) (fun a ↦ U [a]) (fun x ↦ B x*U [] x) he psi hp hc hs

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_RealPositiveNestedRadii
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau
noncomputable section

lemma realWeakJetRadius_zero : realWeakJetRadius 0=1/8 := by norm_num [realWeakJetRadius]

lemma realWeakJetRadius_upper (m : ℕ) : realWeakJetRadius m ≤ (1:ℝ)/8 := by
  have h : (1:ℝ)/(16*((m:ℝ)+1)) ≤ 1/16 := by
    apply one_div_le_one_div_of_le (by norm_num)
    nlinarith only [Nat.cast_nonneg (α := ℝ) m]
  dsimp [realWeakJetRadius]
  linarith only [h]

lemma realWeakJetRadius_succ_lt (m : ℕ) : realWeakJetRadius (m+1) < realWeakJetRadius m := by
  have h : (1:ℝ)/(16*(((m+1:ℕ):ℝ)+1)) < 1/(16*((m:ℝ)+1)) := by
    apply one_div_lt_one_div_of_lt (by positivity)
    push_cast
    linarith
  dsimp only [realWeakJetRadius]
  linarith only [h]

end
end Yau

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_SmoothLimit_SphereFiniteWeakJetIteration
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open MeasureTheory Set Yau.Geometry
open scoped ContDiff
noncomputable section

theorem sphere_finite_weak_jet_iteration_oai (d : SphereEnergyData) (p : Base)
    (B : Yau.Jets.Coord → ℝ) (hB : ContDiff ℝ ∞ B) (m : ℕ) :
    ∃ K > 0, ∀ U : List (Fin 4) → Yau.Jets.Coord → ℝ,
      let Q := Yau.realCenteredCube 4 (1/8)
      (∀ es, es.length ≤ 4 → MemLp (U es) 2 (volume.restrict Q)) →
      (∀ es, es.length ≤ 3 → ∀ i psi,
        ContDiff ℝ ∞ psi → HasCompactSupport psi → tsupport psi ⊆ Q →
        (∫ x in Q, U es x*Yau.coordPartial psi x i)=-(∫ x in Q, U (i::es) x*psi x)) →
      (∀ psi, ContDiff ℝ ∞ psi → HasCompactSupport psi → tsupport psi ⊆ Q →
        (∑ a, ∑ j, ∫ x in Q, sphereChartPrincipalDensity d p x a j*U [a] x*Yau.coordPartial psi x j) =
          ∫ x in Q, B x*U [] x*psi x) →
      ∀ E : ℝ, 0 ≤ E → (∀ es, es.length ≤ 4 → (∫ x in Q, (U es x)^2) ≤ E) →
      ∃ V : List (Fin 4) → Yau.Jets.Coord → ℝ,
        let q := Yau.realCenteredCube 4 (Yau.realWeakJetRadius m)
        (∀ es, es.length ≤ 4 → V es=U es) ∧
        (∀ es, es.length ≤ m+4 → MemLp (V es) 2 (volume.restrict q) ∧
          (∫ x in q, (V es x)^2) ≤ K*E) ∧
        (∀ es, es.length ≤ m+3 → ∀ i psi,
          ContDiff ℝ ∞ psi → HasCompactSupport psi → tsupport psi ⊆ q →
          (∫ x in q, V es x*Yau.coordPartial psi x i)=-(∫ x in q, V (i::es) x*psi x)) ∧
        ∀ psi, ContDiff ℝ ∞ psi → HasCompactSupport psi → tsupport psi ⊆ q →
          (∑ a, ∑ j, ∫ x in q, sphereChartPrincipalDensity d p x a j*V [a] x*Yau.coordPartial psi x j) =
            ∫ x in q, B x*V [] x*psi x := by
  induction m with
  | zero =>
    refine ⟨1,by norm_num,?_⟩
    intro U
    dsimp only
    intro hU hw he E hE hUE
    refine ⟨U,fun _ _ ↦ rfl,?_,?_,?_⟩
    · simpa only [Yau.realWeakJetRadius_zero,Nat.zero_add,one_mul] using
        (show ∀ es, es.length ≤ 4 → MemLp (U es) 2 (volume.restrict (Yau.realCenteredCube 4 (1/8))) ∧
          (∫ x in Yau.realCenteredCube 4 (1/8), (U es x)^2) ≤ E from fun es hh ↦ ⟨hU es hh,hUE es hh⟩)
    · simpa only [Yau.realWeakJetRadius_zero,Nat.zero_add] using hw
    · simpa only [Yau.realWeakJetRadius_zero] using he
  | succ m ih =>
    obtain ⟨C,hC,hbase⟩ := ih
    obtain ⟨D,hD,hstep⟩ := sphere_weak_jet_successor d p B hB
      (Yau.realWeakJetRadius m) (Yau.realWeakJetRadius (m+1)) (Yau.realWeakJetRadius_succ_lt m)
      ((Yau.realWeakJetRadius_upper m).trans (by norm_num)) (m+3)
    refine ⟨D*C,mul_pos hD hC,?_⟩
    intro U
    dsimp only
    intro hU hw he E hE hUE
    obtain ⟨V,hlo,hV,hvw,hve⟩ := hbase U hU hw he E hE hUE
    obtain ⟨W,hWlo,hW,hww,hwe⟩ := hstep V (fun es hh ↦ (hV es (by omega)).1)
      hvw hve (C*E) (mul_nonneg hC.le hE) (fun es hh ↦ (hV es (by omega)).2)
    refine ⟨W,fun es hh ↦ (hWlo es (by omega)).trans (hlo es hh),?_,?_,hwe⟩
    · intro es hh
      have h := hW es (by omega)
      exact ⟨h.1,by simpa only [mul_assoc] using h.2⟩
    · intro es hh i psi hp hc hs
      exact (hww es (by omega) i psi hp hc hs).2.2

end
end Yau.Target

end OAI
end

theorem solution : type_of% @OAI.Yau.Target.sphere_finite_weak_jet_iteration_oai := @OAI.Yau.Target.sphere_finite_weak_jet_iteration_oai
