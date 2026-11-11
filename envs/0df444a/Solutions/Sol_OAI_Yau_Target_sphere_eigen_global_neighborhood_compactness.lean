-- Prove2me | solution 1 for OAI.Yau.Target.sphere_eigen_global_neighborhood_compactness
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T00:34:13.741791+00:00
-- url     : https://prove2.me/submissions/1d1d8e97-8629-4953-8160-f26103bee19b

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
import Mathlib.Data.Finset.Insert
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
import Mathlib.Order.Filter.AtTopBot.CountablyGenerated
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
import Theorems.Thm_OAI_Yau_Geometry_real_compact_interior_pointwise
import Theorems.Thm_OAI_Yau_Target_sphere_eigen_all_finite_weak_jets
import Theorems.Thm_OAI_Yau_Target_sphere_eigen_global_representative

section
-- module Solutions.OAIQ237_NY.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem dite_eq_left {α : Sort _} {c : Prop} {_ : Decidable c} {a : c → α} {b : ¬c → α} (h : c) :
    dite c a b = a h := dif_pos h
end OAICompat434

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
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_FiniteSubsequenceSelection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Analysis

theorem finite_subsequence_selection {I : Type*} (P : Finset I)
    (R : I → (ℕ → ℕ) → Prop)
    (hex : ∀ i nu, StrictMono nu → ∃ mu : ℕ → ℕ, StrictMono mu ∧ R i (nu ∘ mu))
    (hsub : ∀ i nu mu, R i nu → StrictMono mu → R i (nu ∘ mu)) :
    ∃ nu : ℕ → ℕ, StrictMono nu ∧ ∀ i ∈ P, R i nu := by
  classical
  induction P using Finset.induction_on with
  | empty => exact ⟨id,strictMono_id,by simp⟩
  | @insert i P hi ih =>
    obtain ⟨nu,hnu,hR⟩ := ih
    obtain ⟨mu,hmu,hm⟩ := hex i nu hnu
    refine ⟨nu ∘ mu,hnu.comp hmu,?_⟩
    intro j hj
    rcases Finset.mem_insert.mp hj with rfl | hj
    · exact hm
    · exact hsub j nu mu (hR j hj) hmu

end Yau.Analysis

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
-- module Solutions.OAIQ237_NY.NodalSets_Coefficients_CoordinateCorrection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau
noncomputable section
variable {n : ℕ}

theorem coordDiv_mul {u : Coord n → ℝ} {V : Coord n → Coord n} {x : Coord n}
    (hu : DifferentiableAt ℝ u x)
    (hV : ∀ i, DifferentiableAt ℝ (fun y ↦ V y i) x) :
    coordDiv (fun y i ↦ u y * V y i) x =
      u x * coordDiv V x + pairing u V x := by
  unfold coordDiv pairing coordPartial
  simp_rw [fderiv_fun_mul hu (hV _)]
  simp only [add_apply, smul_apply, smul_eq_mul]
  rw [Finset.sum_add_distrib, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem weightedDiv_mul {gamma u : Coord n → ℝ} {V : Coord n → Coord n}
    {x : Coord n} (hg : DifferentiableAt ℝ gamma x) (hgn : gamma x ≠ 0)
    (hu : DifferentiableAt ℝ u x)
    (hV : ∀ i, DifferentiableAt ℝ (fun y ↦ V y i) x) :
    weightedDiv gamma (fun y i ↦ u y * V y i) x =
      u x * weightedDiv gamma V x + pairing u V x := by
  have heq : (fun y i ↦ gamma y * (u y * V y i)) =
      (fun y i ↦ u y * (gamma y * V y i)) := by
    funext y i
    ring
  unfold weightedDiv
  rw [heq, coordDiv_mul (V := fun y i ↦ gamma y * V y i) hu (fun i ↦ hg.mul (hV i))]
  have hp : pairing u (fun y i ↦ gamma y * V y i) x = gamma x * pairing u V x := by
    unfold pairing
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hp]
  field_simp

end
end Yau

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Coefficients_GlobalCorrection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau
noncomputable section
open Function Set
open scoped ContDiff
variable {n : ℕ}

theorem pairing_smooth {u : Coord n → ℝ} {V : Coord n → Coord n}
    (hu : ContDiff ℝ ∞ u) (hV : ∀ i, ContDiff ℝ ∞ (fun x ↦ V x i)) :
    ContDiff ℝ ∞ (pairing u V) := by
  apply ContDiff.sum
  intro i _
  exact ((hu.fderiv_right (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).clm_apply contDiff_const).mul (hV i)

theorem weightedDiv_smooth {gamma : Coord n → ℝ} {V : Coord n → Coord n}
    (hg : ContDiff ℝ ∞ gamma) (hgn : ∀ x, gamma x ≠ 0)
    (hV : ∀ i, ContDiff ℝ ∞ (fun x ↦ V x i)) :
    ContDiff ℝ ∞ (weightedDiv gamma V) := by
  apply (hg.inv hgn).mul
  apply ContDiff.sum
  intro i _
  exact (((hg.mul (hV i)).fderiv_right (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).clm_apply contDiff_const)

end
end Yau

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_CompactWeightedDivergenceIntegral
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau
open Set MeasureTheory
open scoped ContDiff
noncomputable section
variable {d : ℕ}

lemma integral_directional_derivative_compact_zero (g : Coord d → ℝ)
    (hg : ContDiff ℝ ∞ g) (hc : HasCompactSupport g) (v : Coord d) :
    (∫ x, fderiv ℝ g x v) = 0 := by
  have hd : ContDiff ℝ ∞ (fun x ↦ fderiv ℝ g x v) :=
    (hg.fderiv_right (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).clm_apply contDiff_const
  have hi : Integrable (fun x ↦ fderiv ℝ g x v) := hd.continuous.integrable_of_hasCompactSupport (hc.fderiv_apply ℝ v)
  have h := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    (μ := volume) (f := fun _ : Coord d ↦ (1:ℝ)) (g := g) (v := v)
    (by simp) (by simpa using hi)
    (by simpa using hg.continuous.integrable_of_hasCompactSupport hc)
    (fun _ _ ↦ differentiableAt_const 1) (fun x _ ↦ hg.differentiable (by simp) x)
  simpa using h

theorem integral_weightedDiv_compact_zero (gamma : Coord d → ℝ)
    (hg : ContDiff ℝ ∞ gamma) (hgn : ∀ x, gamma x ≠ 0)
    (V : Coord d → Coord d) (hV : ∀ i, ContDiff ℝ ∞ (fun x ↦ V x i))
    (hc : ∀ i, HasCompactSupport (fun x ↦ V x i)) :
    Integrable (fun x ↦ gamma x*weightedDiv gamma V x) ∧
    (∫ x, gamma x*weightedDiv gamma V x) = 0 := by
  let W : Fin d → Coord d → ℝ := fun i x ↦ gamma x*V x i
  have hW (i : Fin d) : ContDiff ℝ ∞ (W i) := hg.mul (hV i)
  have hWc (i : Fin d) : HasCompactSupport (W i) := (hc i).mul_left
  have hd (i : Fin d) : ContDiff ℝ ∞ (fun x ↦ fderiv ℝ (W i) x (Pi.single i 1)) :=
    ((hW i).fderiv_right (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).clm_apply contDiff_const
  have hi (i : Fin d) : Integrable (fun x ↦ fderiv ℝ (W i) x (Pi.single i 1)) :=
    (hd i).continuous.integrable_of_hasCompactSupport ((hWc i).fderiv_apply ℝ (Pi.single i 1))
  have he : (fun x ↦ gamma x*weightedDiv gamma V x) =
      (fun x ↦ ∑ i, fderiv ℝ (W i) x (Pi.single i 1)) := by
    funext x
    simp only [weightedDiv,coordDiv,coordPartial,← mul_assoc,mul_inv_cancel₀ (hgn x),one_mul,W]
  rw [he]
  refine ⟨integrable_finsetSum _ (fun i _ ↦ hi i),?_⟩
  rw [integral_finsetSum _ (fun i _ ↦ hi i)]
  simp only [integral_directional_derivative_compact_zero _ (hW _) (hWc _),Finset.sum_const_zero]

end
end Yau

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
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_CompactWeightedWeakEquation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau
open MeasureTheory
open scoped ContDiff
noncomputable section
variable {n : ℕ}

theorem compact_weighted_integration_by_parts (gamma phi : Coord n → ℝ)
    (hg : ContDiff ℝ ∞ gamma) (hgn : ∀ x, gamma x ≠ 0)
    (hphi : ContDiff ℝ ∞ phi) (hc : HasCompactSupport phi)
    (V : Coord n → Coord n) (hV : ∀ i, ContDiff ℝ ∞ (fun x ↦ V x i)) :
    Integrable (fun x ↦ gamma x*pairing phi V x) ∧
    Integrable (fun x ↦ gamma x*phi x*weightedDiv gamma V x) ∧
    (∫ x, gamma x*pairing phi V x) = -(∫ x, gamma x*phi x*weightedDiv gamma V x) := by
  have hp : HasCompactSupport (pairing phi V) := by
    unfold pairing
    have h := HasCompactSupport.finset_sum
      (s := Finset.univ) (fun i _ ↦ (hc.fderiv_apply ℝ (Pi.single i 1)).mul_right
        (f' := fun x ↦ V x i))
    convert h using 1 <;> first | rfl | (ext x; simp [coordPartial])
  have hiP : Integrable (fun x ↦ gamma x*pairing phi V x) :=
    (hg.mul (pairing_smooth hphi hV)).continuous.integrable_of_hasCompactSupport hp.mul_left
  have hiD : Integrable (fun x ↦ gamma x*phi x*weightedDiv gamma V x) :=
    ((hg.mul hphi).mul (weightedDiv_smooth hg hgn hV)).continuous.integrable_of_hasCompactSupport
      hc.mul_left.mul_right
  obtain ⟨_,hz⟩ := integral_weightedDiv_compact_zero gamma hg hgn
    (fun x i ↦ phi x*V x i) (fun i ↦ hphi.mul (hV i)) (fun _ ↦ hc.mul_right)
  have he : (fun x ↦ gamma x*weightedDiv gamma (fun y i ↦ phi y*V y i) x) =
      (fun x ↦ gamma x*phi x*weightedDiv gamma V x + gamma x*pairing phi V x) := by
    funext x
    rw [weightedDiv_mul (hg.differentiable (by simp) x) (hgn x)
      (hphi.differentiable (by simp) x) (fun i ↦ (hV i).differentiable (by simp) x)]
    ring
  rw [he,integral_add hiD hiP] at hz
  exact ⟨hiP,hiD,by linarith⟩

end
end Yau

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_CoordinateNorm
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Yau.Jets
noncomputable section

lemma sourceEuclideanNorm_le (x : _root_.OAI.Yau.Jets.Coord) : sourceEuclideanNorm x ≤ 2*‖x‖ := by
  apply (Real.sqrt_le_iff).mpr
  refine ⟨by positivity,?_⟩
  have hh (i : Fin 4) : (x i)^2 ≤ ‖x‖^2 := by
    have hi := norm_le_pi_norm x i
    change |x i| ≤ ‖x‖ at hi
    nlinarith [sq_abs (x i),norm_nonneg x,abs_nonneg (x i)]
  have hs := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin 4))) ↦ hh i)
  norm_num at hs
  nlinarith

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_CoordinateMatrixEllipticity
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Yau.Jets Matrix
noncomputable section
attribute [local instance] clmTopology clmAdd clmModule

lemma coordMatrixForm_apply (B : Matrix (Fin 4) (Fin 4) ℝ) (v w : _root_.OAI.Yau.Jets.Coord) :
    coordMatrixForm B v w = ∑ i, ∑ j, v i*B i j*w j := by
  simp [coordMatrixForm,mul_comm,mul_left_comm]

lemma coordMatrixForm_positive (B : Matrix (Fin 4) (Fin 4) ℝ) (hB : B.PosDef)
    (v : _root_.OAI.Yau.Jets.Coord) (hv : v ≠ 0) : 0 < coordMatrixForm B v v := by
  rw [coordMatrixForm_apply]
  simpa [dotProduct,mulVec,Finset.mul_sum,mul_assoc] using hB.dotProduct_mulVec_pos hv

lemma coordMatrixForm_continuous {T : Type*} [TopologicalSpace T]
    (B : T → Matrix (Fin 4) (Fin 4) ℝ)
    (hB : ∀ i j, Continuous (fun x ↦ B x i j)) :
    Continuous (fun x ↦ coordMatrixForm (B x)) := by
  unfold coordMatrixForm
  exact continuous_finsetSum _ (fun i _ ↦ continuous_finsetSum _
    (fun j _ ↦ (hB i j).smul continuous_const))

lemma coord_norm_sq_le_sum_sq (v : _root_.OAI.Yau.Jets.Coord) : ‖v‖^2 ≤ ∑ i, v i^2 := by
  have h := norm_le_sourceEuclideanNorm v
  have he : sourceEuclideanNorm v ^ 2 = ∑ i, v i^2 :=
    Real.sq_sqrt (Finset.sum_nonneg (fun i _ ↦ sq_nonneg (v i)))
  nlinarith [norm_nonneg v,sourceEuclideanNorm_nonneg v]

lemma coord_sum_sq_le_four_norm_sq (v : _root_.OAI.Yau.Jets.Coord) : (∑ i, v i^2) ≤ 4*‖v‖^2 := by
  have h := sourceEuclideanNorm_le v
  have he : sourceEuclideanNorm v ^ 2 = ∑ i, v i^2 :=
    Real.sq_sqrt (Finset.sum_nonneg (fun i _ ↦ sq_nonneg (v i)))
  nlinarith [norm_nonneg v,sourceEuclideanNorm_nonneg v]

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_RealMatrixEnergy
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Yau.Jets Matrix MeasureTheory
open scoped ContDiff
noncomputable section
attribute [local instance] clmTopology clmAdd clmModule

lemma realMatrixEnergy_apply (B : Yau.Jets.Coord → Matrix (Fin 4) (Fin 4) ℝ)
    (u v : Yau.Jets.Coord → ℝ) (x : Yau.Jets.Coord) :
    realMatrixEnergy B u v x = ∑ i, ∑ j, Yau.coordPartial u x i*B x i j*Yau.coordPartial v x j :=
  coordMatrixForm_apply _ _ _

lemma coordMatrixForm_symmetric (B : Matrix (Fin 4) (Fin 4) ℝ) (hs : ∀ i j, B i j = B j i)
    (v w : Yau.Jets.Coord) : coordMatrixForm B v w = coordMatrixForm B w v := by
  rw [coordMatrixForm_apply,coordMatrixForm_apply,Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [hs j i]
  ring

lemma realCoordGradient_cutoff (eta w : Yau.Jets.Coord → ℝ)
    (heta : ContDiff ℝ ∞ eta) (hw : ContDiff ℝ ∞ w) (x : Yau.Jets.Coord) :
    realCoordGradient (fun y ↦ eta y^2*w y) x =
      (eta x^2) • realCoordGradient w x + (2*eta x*w x) • realCoordGradient eta x := by
  ext i
  have he : (fun y ↦ eta y^2*w y) = fun y ↦ (eta y*eta y)*w y := by
    funext y; ring
  simp only [realCoordGradient,he,Yau.real_coordPartial_mul _ _ (heta.mul heta) hw,
    Yau.real_coordPartial_mul _ _ heta heta,Pi.add_apply,Pi.smul_apply,smul_eq_mul]
  ring

lemma realMatrixEnergy_cutoff (B : Yau.Jets.Coord → Matrix (Fin 4) (Fin 4) ℝ)
    (eta w : Yau.Jets.Coord → ℝ) (heta : ContDiff ℝ ∞ eta) (hw : ContDiff ℝ ∞ w) (x : Yau.Jets.Coord) :
    realMatrixEnergy B (fun y ↦ eta y^2*w y) w x =
      eta x^2*realMatrixEnergy B w w x + 2*eta x*w x*realMatrixEnergy B eta w x := by
  unfold realMatrixEnergy
  rw [realCoordGradient_cutoff eta w heta hw x]
  simp [map_add,map_smul,smul_eq_mul]

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_RealWeightedElliptic
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Yau.Jets Matrix MeasureTheory
open scoped ContDiff
noncomputable section

lemma realMatrixFlux_smooth (B : Yau.Jets.Coord → Matrix (Fin 4) (Fin 4) ℝ) (w : Yau.Jets.Coord → ℝ)
    (hB : ∀ i j, ContDiff ℝ ∞ (fun x ↦ B x i j)) (hw : ContDiff ℝ ∞ w) (i : Fin 4) :
    ContDiff ℝ ∞ (fun x ↦ realMatrixFlux B w x i) :=
  ContDiff.sum (fun j _ ↦ (hB i j).mul (Yau.real_coordPartial_smooth w hw j))

lemma realMatrixEnergy_pairing (B : Yau.Jets.Coord → Matrix (Fin 4) (Fin 4) ℝ)
    (u v : Yau.Jets.Coord → ℝ) (x : Yau.Jets.Coord) :
    Yau.pairing u (realMatrixFlux B v) x = realMatrixEnergy B u v x := by
  simp only [Yau.pairing,realMatrixFlux,realMatrixEnergy_apply,Finset.mul_sum,mul_assoc]

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
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_RealDifferentiatedEquation
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open scoped ContDiff
noncomputable section

lemma real_coordDiv_add (F G : Yau.Jets.Coord → Yau.Jets.Coord)
    (hF : ∀ i, ContDiff ℝ ∞ (fun x ↦ F x i)) (hG : ∀ i, ContDiff ℝ ∞ (fun x ↦ G x i))
    (x : Yau.Jets.Coord) :
    Yau.coordDiv (fun y i ↦ F y i+G y i) x = Yau.coordDiv F x+Yau.coordDiv G x := by
  simp only [Yau.coordDiv,Yau.real_coordPartial_add _ _ (hF _) (hG _),Finset.sum_add_distrib]

lemma real_coordDiv_partial (F : Yau.Jets.Coord → Yau.Jets.Coord)
    (hF : ∀ i, ContDiff ℝ ∞ (fun x ↦ F x i)) (x : Yau.Jets.Coord) (k : Fin 4) :
    Yau.coordPartial (Yau.coordDiv F) x k =
      Yau.coordDiv (fun y i ↦ Yau.coordPartial (fun z ↦ F z i) y k) x := by
  unfold Yau.coordDiv
  rw [Yau.real_coordPartial_sum _ (fun i ↦ Yau.real_coordPartial_smooth _ (hF i) i)]
  apply Finset.sum_congr rfl; intro i _
  exact Yau.real_coordPartial_commute _ (hF i) x k i

lemma realDerivativeErrorFlux_smooth (C : Yau.Jets.Coord → Matrix (Fin 4) (Fin 4) ℝ)
    (W : Yau.Jets.Coord → ℝ) (k : Fin 4)
    (hC : ∀ i j, ContDiff ℝ ∞ (fun x ↦ C x i j)) (hW : ContDiff ℝ ∞ W) (i : Fin 4) :
    ContDiff ℝ ∞ (fun x ↦ realDerivativeErrorFlux C W k x i) :=
  ContDiff.sum (fun j _ ↦ (Yau.real_coordPartial_smooth _ (hC i j) k).mul
    (Yau.real_coordPartial_smooth W hW j))

lemma realMatrixFlux_partial (C : Yau.Jets.Coord → Matrix (Fin 4) (Fin 4) ℝ)
    (W : Yau.Jets.Coord → ℝ) (hC : ∀ i j, ContDiff ℝ ∞ (fun x ↦ C x i j))
    (hW : ContDiff ℝ ∞ W) (x : Yau.Jets.Coord) (i k : Fin 4) :
    Yau.coordPartial (fun y ↦ realMatrixFlux C W y i) x k =
      realDerivativeErrorFlux C W k x i+realMatrixFlux C (fun y ↦ Yau.coordPartial W y k) x i := by
  unfold realMatrixFlux realDerivativeErrorFlux
  rw [Yau.real_coordPartial_sum _ (fun j ↦ (hC i j).mul (Yau.real_coordPartial_smooth W hW j))]
  simp only [Yau.real_coordPartial_mul _ _ (hC i _) (Yau.real_coordPartial_smooth W hW _),
    Yau.real_coordPartial_commute W hW x k,Finset.sum_add_distrib]

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_RealTransportQuadratic
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Matrix
open scoped ContDiff
noncomputable section

lemma realGradientSquare_smooth (v : Yau.Jets.Coord → ℝ) (hv : ContDiff ℝ ∞ v) :
    ContDiff ℝ ∞ (realGradientSquare v) :=
  ContDiff.sum (fun i _ ↦ (Yau.real_coordPartial_smooth v hv i).pow 2)

lemma realGradientSquare_compact (v : Yau.Jets.Coord → ℝ) (hc : HasCompactSupport v) :
    HasCompactSupport (realGradientSquare v) := by
  have hd (i : Fin 4) : HasCompactSupport (fun x ↦ (Yau.coordPartial v x i)^2) := by
    convert (hc.fderiv_apply ℝ (Pi.single i 1)).mul_right
      (f' := fun x ↦ Yau.coordPartial v x i) using 1
    all_goals try with_reducible_and_instances rfl
    first | rfl | (ext x; simp [pow_two,Yau.coordPartial])
  have h := HasCompactSupport.finset_sum (s := Finset.univ) (fun i _ ↦ hd i)
  exact h

lemma realCoordGradient_zero_off_support (v : Yau.Jets.Coord → ℝ)
    {x : Yau.Jets.Coord} (hx : x ∉ tsupport v) : realCoordGradient v x = 0 := by
  ext i
  simp only [realCoordGradient,Yau.coordPartial,fderiv_of_notMem_tsupport ℝ hx,
    _root_.zero_apply,Pi.zero_apply]

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_RealDerivativeErrorBounds
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open scoped ContDiff
noncomputable section

lemma realGradientSquare_nonneg (W : Yau.Jets.Coord → ℝ) (x : Yau.Jets.Coord) :
    0 ≤ realGradientSquare W x := Finset.sum_nonneg (fun _i _ ↦ sq_nonneg _)

lemma real_partial_sq_le_gradient (W : Yau.Jets.Coord → ℝ) (x : Yau.Jets.Coord) (i : Fin 4) :
    (Yau.coordPartial W x i)^2 ≤ realGradientSquare W x :=
  Finset.single_le_sum (fun j _ ↦ sq_nonneg (Yau.coordPartial W x j)) (Finset.mem_univ i)

lemma real_coordDiv_neg (F : Yau.Jets.Coord → Yau.Jets.Coord)
    (hF : ∀ i, ContDiff ℝ ∞ (fun x ↦ F x i)) (x : Yau.Jets.Coord) :
    Yau.coordDiv (fun y i ↦ -F y i) x = -Yau.coordDiv F x := by
  unfold Yau.coordDiv Yau.coordPartial
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro index _
  exact congrArg (fun derivative : Yau.Jets.Coord →L[ℝ] ℝ ↦ derivative (Pi.single index 1))
    (((hF index).differentiable (by simp)).differentiableAt.hasFDerivAt.neg.fderiv)

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_RealCutoffIntegralsLemmas
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Yau.Geometry

open MeasureTheory
open scoped ContDiff

lemma realCutoffWeight_nonneg (eta : Yau.Jets.Coord → ℝ) (x : Yau.Jets.Coord) :
    0 ≤ realCutoffWeight eta x := add_nonneg (sq_nonneg _) (realGradientSquare_nonneg eta x)

lemma realCutoffWeight_smooth (eta : Yau.Jets.Coord → ℝ) (h : ContDiff ℝ ∞ eta) :
    ContDiff ℝ ∞ (realCutoffWeight eta) := (h.pow 2).add (realGradientSquare_smooth eta h)

lemma realCutoffWeight_compact (eta : Yau.Jets.Coord → ℝ) (hc : HasCompactSupport eta) :
    HasCompactSupport (realCutoffWeight eta) := by
  have hsq : HasCompactSupport (fun x ↦ eta x^2) := by
    convert hc.mul_right (f' := eta) using 1
    all_goals try with_reducible_and_instances rfl
    first | rfl | (ext x; simp [pow_two])
  exact hsq.add (realGradientSquare_compact eta hc)

lemma realCutoffWeight_zero_off_support (eta : Yau.Jets.Coord → ℝ)
    {x : Yau.Jets.Coord} (hx : x ∉ tsupport eta) : realCutoffWeight eta x=0 := by
  have hz : eta x=0 := image_eq_zero_of_notMem_tsupport hx
  have hd := realCoordGradient_zero_off_support eta hx
  have hi (i : Fin 4) : Yau.coordPartial eta x i=0 := congrFun hd i
  simp [realCutoffWeight,realGradientSquare,hz,hi]

lemma realCutoffWeight_integrable_mul (eta H : Yau.Jets.Coord → ℝ)
    (heta : ContDiff ℝ ∞ eta) (hc : HasCompactSupport eta) (hH : Continuous H) :
    Integrable (fun x ↦ realCutoffWeight eta x*H x) :=
  ((realCutoffWeight_smooth eta heta).continuous.mul hH).integrable_of_hasCompactSupport
    (realCutoffWeight_compact eta hc).mul_right

lemma real_coordDiv_sub (F G : Yau.Jets.Coord → Yau.Jets.Coord)
    (hF : ∀ i, ContDiff ℝ ∞ (fun x ↦ F x i)) (hG : ∀ i, ContDiff ℝ ∞ (fun x ↦ G x i))
    (x : Yau.Jets.Coord) :
    Yau.coordDiv (fun y i ↦ F y i-G y i) x=Yau.coordDiv F x-Yau.coordDiv G x := by
  simp only [sub_eq_add_neg,real_coordDiv_add _ _ hF (fun i ↦ (hG i).neg),real_coordDiv_neg _ hG]

end Yau.Geometry

end

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_RealJetErrorEquation
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

lemma realJetErrorFlux_smooth (C : Yau.Jets.Coord → Matrix (Fin 4) (Fin 4) ℝ)
    (W : Yau.Jets.Coord → ℝ) (hC : ∀ i j, ContDiff ℝ ∞ (fun x ↦ C x i j))
    (hW : ContDiff ℝ ∞ W) (ds : List (Fin 4)) (i : Fin 4) :
    ContDiff ℝ ∞ (fun x ↦ realJetErrorFlux C W ds x i) := by
  induction ds with
  | nil => exact contDiff_const
  | cons l ds ih =>
    exact (Yau.real_coordPartial_smooth _ ih l).sub
      (realDerivativeErrorFlux_smooth C (partialJet W ds) l hC (partialJet_smooth W hW ds) i)

lemma realJetErrorSource_smooth (V W : Yau.Jets.Coord → ℝ)
    (hV : ContDiff ℝ ∞ V) (hW : ContDiff ℝ ∞ W) (ds : List (Fin 4)) :
    ContDiff ℝ ∞ (realJetErrorSource V W ds) := by
  induction ds with
  | nil => exact contDiff_const
  | cons l ds ih =>
    exact (Yau.real_coordPartial_smooth _ ih l).sub
      ((Yau.real_coordPartial_smooth V hV l).mul (partialJet_smooth W hW ds))

end
end Yau.Geometry

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

theorem real_finite_ball_jet_subsequence (W : ℕ → Yau.Jets.Coord → ℝ)
    (hW : ∀ j, ContDiff ℝ ∞ (W j)) (y : Yau.Jets.Coord) (r : ℝ) (n : ℕ)
    (B : ℝ) (hB : 0 ≤ B)
    (hb : ∀ j (ds : List (Fin 4)), ds.length ≤ n+1 →
      ∀ x ∈ closedBall y r, |partialJet (W j) ds x| ≤ B) :
    ∃ f : {ds : List (Fin 4) // ds.length ≤ n} → closedBall y r → ℝ,
      (∀ ds, Continuous (f ds)) ∧ ∃ nu : ℕ → ℕ, StrictMono nu ∧
        ∀ ds : {ds : List (Fin 4) // ds.length ≤ n},
          TendstoUniformly (fun j (x : closedBall y r) ↦ partialJet (W (nu j)) ds.val x)
            (f ds) atTop := by
  let F (ds : {ds : List (Fin 4) // ds.length ≤ n}) (j : ℕ) (x : closedBall y r) :=
    partialJet (W j) ds.val x
  let C : ℝ≥0 := ⟨B,hB⟩
  apply real_countable_uniform_subsequence F (fun _ ↦ B) (fun _ ↦ 4*C)
  · intro ds j x
    exact hb j ds.val (by have := ds.property; omega) x x.property
  · intro ds j
    apply LipschitzOnWith.to_restrict
    apply real_partialJet_lipschitz (W j) (hW j) ds.val y r C
    intro i x hx
    exact hb j (i::ds.val) (by simp only [List.length_cons]; have := ds.property; omega) x hx

end Yau.Geometry

end

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
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_RealFiniteLocalJetLimit
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

theorem real_finite_local_jet_limit_derivative (O : Set Yau.Jets.Coord) (hO : IsOpen O)
    (W : ℕ → Yau.Jets.Coord → ℝ) (hW : ∀ j, ContDiff ℝ ∞ (W j))
    (N : ℕ) (g : List (Fin 4) → Yau.Jets.Coord → ℝ)
    (ht : ∀ ds : List (Fin 4), ds.length ≤ N →
      TendstoUniformlyOn (fun j ↦ partialJet (W j) ds) (g ds) atTop O)
    (ds : List (Fin 4)) (hd : ds.length < N) (x : Yau.Jets.Coord) (hx : x ∈ O) :
    HasFDerivAt (g ds) (realCoordinateDual (fun i ↦ g (i::ds) x)) x := by
  have hu := real_uniform_coordinate_dual (fun i ↦ ht (i::ds) (by simp; omega))
  apply hasFDerivAt_of_tendstoUniformlyOn hO hu (f := fun j ↦ partialJet (W j) ds)
  · intro j y _
    change HasFDerivAt (partialJet (W j) ds)
      (realCoordinateDual (fun i ↦ fderiv ℝ (partialJet (W j) ds) y (Pi.single i 1))) y
    rw [← real_fderiv_coordinateDual]
    exact ((partialJet_smooth _ (hW j) ds).differentiable (by simp) y).hasFDerivAt
  · intro y hy
    exact (ht ds hd.le).tendsto_at hy
  · exact hx

theorem real_finite_local_jet_limit_identification (O : Set Yau.Jets.Coord) (hO : IsOpen O)
    (N : ℕ) (g : List (Fin 4) → Yau.Jets.Coord → ℝ)
    (hd : ∀ ds : List (Fin 4), ds.length < N → ∀ x ∈ O,
      HasFDerivAt (g ds) (realCoordinateDual (fun i ↦ g (i::ds) x)) x)
    (ds : List (Fin 4)) (hds : ds.length ≤ N) :
    EqOn (partialJet (g []) ds) (g ds) O := by
  induction ds with
  | nil => intro x hx; rfl
  | cons i ds ih =>
    intro x hx
    have hlen : ds.length < N := by simp only [List.length_cons] at hds; omega
    have he : partialJet (g []) ds =ᶠ[𝓝 x] g ds := by
      filter_upwards [hO.mem_nhds hx] with y hy
      exact ih hlen.le hy
    change fderiv ℝ (partialJet (g []) ds) x (Pi.single i 1) = _
    rw [he.fderiv_eq,(hd ds hlen x hx).fderiv,realCoordinateDual_single]

theorem real_finite_local_jet_limit_contDiffOn (O : Set Yau.Jets.Coord) (hO : IsOpen O)
    (N : ℕ) (g : List (Fin 4) → Yau.Jets.Coord → ℝ)
    (hc : ∀ ds : List (Fin 4), ds.length ≤ N → ContinuousOn (g ds) O)
    (hd : ∀ ds : List (Fin 4), ds.length < N → ∀ x ∈ O,
      HasFDerivAt (g ds) (realCoordinateDual (fun i ↦ g (i::ds) x)) x) :
    ContDiffOn ℝ N (g []) O := by
  have hn (k : ℕ) : ∀ ds : List (Fin 4), ds.length+k ≤ N → ContDiffOn ℝ k (g ds) O := by
    induction k with
    | zero => intro ds hh; exact contDiffOn_zero.mpr (hc ds (by omega))
    | succ k ih =>
      intro ds hh
      rw [show ((k+1:ℕ) : ℕ∞ω) = (k:ℕ∞ω)+1 by simp,contDiffOn_succ_iff_fderiv_of_isOpen hO]
      refine ⟨fun x hx ↦ (hd ds (by omega) x hx).differentiableAt.differentiableWithinAt,by simp,?_⟩
      have hs : ContDiffOn ℝ k (fun x ↦ realCoordinateDual (fun i ↦ g (i::ds) x)) O :=
        realCoordinateDual.contDiff.comp_contDiffOn
          (contDiffOn_pi.mpr (fun i ↦ ih (i::ds) (by simp only [List.length_cons]; omega)))
      apply hs.congr
      intro x hx
      exact (hd ds (by omega) x hx).fderiv
  exact hn N [] (by simp)

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_SmoothLimit_RealFiniteBallSmoothLimit
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

theorem real_finite_ball_limit_identification (W : ℕ → Yau.Jets.Coord → ℝ)
    (hW : ∀ j, ContDiff ℝ ∞ (W j)) (y : Yau.Jets.Coord) (r : ℝ) (n : ℕ)
    (f : {ds : List (Fin 4) // ds.length ≤ n} → closedBall y r → ℝ)
    (ht : ∀ ds : {ds : List (Fin 4) // ds.length ≤ n},
      TendstoUniformly (fun j (x : closedBall y r) ↦ partialJet (W j) ds.val x) (f ds) atTop) :
    ∃ v : Yau.Jets.Coord → ℝ, ContinuousOn v (closedBall y r) ∧
      ContDiffOn ℝ n v (ball y r) ∧
      TendstoUniformlyOn W v atTop (closedBall y r) ∧
      ∀ ds : List (Fin 4), ds.length ≤ n →
        TendstoUniformlyOn (fun j ↦ partialJet (W j) ds) (partialJet v ds) atTop (ball y r) := by
  classical
  let g (ds : List (Fin 4)) (x : Yau.Jets.Coord) :=
    if hd : ds.length ≤ n then if hx : x ∈ closedBall y r then f ⟨ds,hd⟩ ⟨x,hx⟩ else 0 else 0
  have hu (ds : List (Fin 4)) (hd : ds.length ≤ n) :
      TendstoUniformlyOn (fun j ↦ partialJet (W j) ds) (g ds) atTop (closedBall y r) := by
    rw [tendstoUniformlyOn_iff_restrict]
    change TendstoUniformly (fun j (x : closedBall y r) ↦ partialJet (W j) ds x)
      (fun x : closedBall y r ↦ g ds x) atTop
    have heq : (fun x : closedBall y r ↦ g ds x) = f ⟨ds,hd⟩ := by
      funext x
      simp only [g,dite_eq_left hd,dite_eq_left x.property]
    rw [heq]
    exact ht ⟨ds,hd⟩
  have hc (ds : List (Fin 4)) (hd : ds.length ≤ n) : ContinuousOn (g ds) (closedBall y r) :=
    (hu ds hd).continuousOn (Filter.Eventually.frequently (Filter.Eventually.of_forall
      (fun j ↦ (partialJet_smooth (W j) (hW j) ds).continuous.continuousOn)))
  have hd (ds : List (Fin 4)) (hh : ds.length < n) (x : Yau.Jets.Coord) (hx : x ∈ ball y r) :
      HasFDerivAt (g ds) (realCoordinateDual (fun i ↦ g (i::ds) x)) x :=
    real_finite_local_jet_limit_derivative (ball y r) isOpen_ball W hW n g
      (fun es he ↦ (hu es he).mono ball_subset_closedBall) ds hh x hx
  refine ⟨g [],hc [] (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top),real_finite_local_jet_limit_contDiffOn (ball y r) isOpen_ball n g
    (fun es he ↦ (hc es he).mono ball_subset_closedBall) hd,hu [] (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top),?_⟩
  intro ds hh
  apply ((hu ds hh).mono ball_subset_closedBall).congr_right
  exact (real_finite_local_jet_limit_identification (ball y r) isOpen_ball n g hd ds hh).symm

theorem real_finite_ball_smooth_subsequence (W : ℕ → Yau.Jets.Coord → ℝ)
    (hW : ∀ j, ContDiff ℝ ∞ (W j)) (y : Yau.Jets.Coord) (r : ℝ) (n : ℕ)
    (B : ℝ) (hB : 0 ≤ B)
    (hb : ∀ j (ds : List (Fin 4)), ds.length ≤ n+1 →
      ∀ x ∈ closedBall y r, |partialJet (W j) ds x| ≤ B) :
    ∃ v : Yau.Jets.Coord → ℝ, ContinuousOn v (closedBall y r) ∧ ContDiffOn ℝ n v (ball y r) ∧
      ∃ nu : ℕ → ℕ, StrictMono nu ∧ TendstoUniformlyOn (fun j ↦ W (nu j)) v atTop (closedBall y r) ∧
        ∀ ds : List (Fin 4), ds.length ≤ n →
          TendstoUniformlyOn (fun j ↦ partialJet (W (nu j)) ds) (partialJet v ds) atTop (ball y r) := by
  obtain ⟨f,hf,nu,hnu,ht⟩ := real_finite_ball_jet_subsequence W hW y r n B hB hb
  obtain ⟨v,hv,hs,hzero,hjet⟩ := real_finite_ball_limit_identification
    (fun j ↦ W (nu j)) (fun j ↦ hW (nu j)) y r n f ht
  exact ⟨v,hv,hs,nu,hnu,hzero,hjet⟩

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Charts_RealFiniteAtlasBallSubsequence
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

theorem real_finite_atlas_ball_subsequence {I : Type*} [Fintype I]
    (W : I → ℕ → Yau.Jets.Coord → ℝ)
    (hW : ∀ i j, ContDiff ℝ ∞ (W i j)) (r : ℝ) (n : ℕ)
    (B : I → ℝ) (hB : ∀ i, 0 ≤ B i)
    (hb : ∀ i j (ds : List (Fin 4)), ds.length ≤ n+1 →
      ∀ x ∈ closedBall (0 : Yau.Jets.Coord) r, |partialJet (W i j) ds x| ≤ B i) :
    ∃ nu : ℕ → ℕ, StrictMono nu ∧ ∀ i,
      ∃ v : Yau.Jets.Coord → ℝ, ContinuousOn v (closedBall 0 r) ∧
        ContDiffOn ℝ n v (ball 0 r) ∧
        TendstoUniformlyOn (fun j ↦ W i (nu j)) v atTop (closedBall 0 r) ∧
        ∀ ds : List (Fin 4), ds.length ≤ n →
          TendstoUniformlyOn (fun j ↦ partialJet (W i (nu j)) ds)
            (partialJet v ds) atTop (ball 0 r) := by
  classical
  obtain ⟨nu,hnu,hR⟩ := finite_subsequence_selection (Finset.univ : Finset I)
    (fun i nu ↦ ∃ v : Yau.Jets.Coord → ℝ, ContinuousOn v (closedBall 0 r) ∧
      ContDiffOn ℝ n v (ball 0 r) ∧
      TendstoUniformlyOn (fun j ↦ W i (nu j)) v atTop (closedBall 0 r) ∧
      ∀ ds : List (Fin 4), ds.length ≤ n →
        TendstoUniformlyOn (fun j ↦ partialJet (W i (nu j)) ds)
          (partialJet v ds) atTop (ball 0 r)) (by
      intro i nu hnu
      obtain ⟨v,hv,hs,mu,hmu,ht,hjet⟩ := real_finite_ball_smooth_subsequence
        (fun j ↦ W i (nu j)) (fun j ↦ hW i (nu j)) 0 r n (B i) (hB i)
        (fun j ↦ hb i (nu j))
      exact ⟨mu,hmu,v,hv,hs,ht,hjet⟩) (by
      intro i nu mu hR hmu
      obtain ⟨v,hv,hs,ht,hjet⟩ := hR
      exact ⟨v,hv,hs,ht.seq_tendstoUniformlyOn mu hmu.tendsto_atTop,
        fun ds hd ↦ (hjet ds hd).seq_tendstoUniformlyOn mu hmu.tendsto_atTop⟩)
  exact ⟨nu,hnu,fun i ↦ hR i (Finset.mem_univ i)⟩

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Coefficients_IntrinsicCoefficientMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Manifold Matrix Yau.Geometry
open scoped ContDiff
noncomputable section

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

end
end Yau.Target

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

lemma intrinsicRealPrincipal_posDef (A : IntrinsicTensor)
    (hs : ∀ p v w, A p v w = A p w v) (hp : ∀ p v, v ≠ 0 → 0 < A p v v)
    (p : Base) (x : Yau.Jets.Coord) : (intrinsicRealPrincipal A p x).PosDef :=
  intrinsicSphereChartTensor_posDef A hs hp p (by rw [centeredSphereChart_target]; trivial)

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

local instance sphereChartDivergenceDataMeasurable_r6a81dc_1 : MeasurableSpace Base := borel Base
local instance sphereChartDivergenceDataBorel_r6a81dc_1 : BorelSpace Base := ⟨rfl⟩
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

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Charts_SphereFiniteOrderLimitGluing
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Manifold Yau.Analysis Yau.Geometry Set Metric Filter
open scoped Topology ContDiff
noncomputable section

theorem sphere_finite_order_limit_gluing (P : Finset Base) (r : ℝ) (n : ℕ)
    (hcover : ∀ x : Base, ∃ p ∈ P, ∃ z ∈ ball (0 : Yau.Jets.Coord) r,
      sphereChartCoordMap p z=x)
    (w : ℕ → Base → ℝ)
    (f : {p // p ∈ P} → Yau.Jets.Coord → ℝ)
    (hf : ∀ p, ContDiffOn ℝ n (f p) (ball 0 r))
    (ht : ∀ p, TendstoUniformlyOn (fun j ↦ w j ∘ sphereChartCoordMap p.val)
      (f p) atTop (closedBall 0 r)) :
    ∃ v : Base → ℝ, ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) n v ∧
      TendstoUniformly w v atTop ∧
      ∀ p : {p // p ∈ P}, EqOn (v ∘ sphereChartCoordMap p.val) (f p) (ball 0 r) := by
  classical
  have hcov (x : Base) : ∃ p : {p // p ∈ P}, ∃ z ∈ ball (0 : Yau.Jets.Coord) r,
      sphereChartCoordMap p.val z=x := by
    obtain ⟨p,hp,z,hz,he⟩ := hcover x
    exact ⟨⟨p,hp⟩,z,hz,he⟩
  choose c z hz he using hcov
  let v : Base → ℝ := fun x ↦ f (c x) (z x)
  have hvpoint (x : Base) : Tendsto (fun j ↦ w j x) atTop (𝓝 (v x)) := by
    have h := (ht (c x)).tendsto_at (ball_subset_closedBall (hz x))
    simpa only [Function.comp_apply,he,v] using h
  have hvchart (p : {p // p ∈ P}) :
      EqOn (v ∘ sphereChartCoordMap p.val) (f p) (ball 0 r) := by
    intro y hy
    exact tendsto_nhds_unique (hvpoint _) ((ht p).tendsto_at (ball_subset_closedBall hy))
  have hvsmooth : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) n v := by
    intro x
    have hsource : x ∈ (extChartAt (𝓡 4) (c x).val).source := by
      have h := sphereChartCoordMap_source (c x).val (z x)
      rwa [he x] at h
    have hchart := contMDiffAt_extChartAt' (I := 𝓡 4) (n := (n : ℕ∞ω))
      (x := (c x).val) (x' := x) (by simpa only [extChartAt_source] using hsource)
    let coord : Base → Yau.Jets.Coord := fun y ↦
      seedCoordEquiv.symm ((extChartAt (𝓡 4) (c x).val) y)
    have hc : ContMDiffAt (𝓡 4) 𝓘(ℝ,Yau.Jets.Coord) n coord x :=
      seedCoordEquiv.symm.contDiff.contMDiff.contMDiffAt.comp x hchart
    have hcx : coord x=z x := by
      have hi : (extChartAt (𝓡 4) (c x).val)
          (sphereChartCoordMap (c x).val (z x)) = seedCoordEquiv (z x) :=
        (extChartAt (𝓡 4) (c x).val).right_inv (by rw [centeredSphereChart_target]; trivial)
      rw [he x] at hi
      change seedCoordEquiv.symm ((extChartAt (𝓡 4) (c x).val) x)=z x
      rw [hi,seedCoordEquiv.symm_apply_apply]
    have hh := ((hf (c x)).contDiffAt (isOpen_ball.mem_nhds (hz x)))
    rw [← hcx] at hh
    have hh' := hh.comp_contMDiffAt hc
    apply hh'.congr_of_eventuallyEq
    have hb : ∀ᶠ y in 𝓝 x, coord y ∈ ball (0 : Yau.Jets.Coord) r :=
      hc.continuousAt (isOpen_ball.mem_nhds (hcx ▸ hz x))
    filter_upwards [(isOpen_extChartAt_source (c x).val).mem_nhds hsource,hb] with y hy hby
    have h := hvchart (c x) hby
    simpa only [Function.comp_apply,coord,sphereChartCoordMap,seedCoordEquiv.apply_symm_apply,
      (extChartAt (𝓡 4) (c x).val).left_inv hy] using h
  refine ⟨v,hvsmooth,?_,hvchart⟩
  rw [Metric.tendstoUniformly_iff]
  intro eps heps
  have hh (p : {p // p ∈ P}) := Metric.tendstoUniformlyOn_iff.mp (ht p) eps heps
  filter_upwards [Filter.eventually_all.mpr hh] with j hj x
  have h := hj (c x) (z x) (ball_subset_closedBall (hz x))
  simpa only [Function.comp_apply,he,v] using h

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Charts_SphereFiniteJetCompactness
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Manifold Yau.Analysis Yau.Geometry Set Metric Filter
open scoped Topology ContDiff
noncomputable section

theorem sphere_finite_jet_compactness (P : Finset Base) (s r : ℝ) (hsr : s < r) (n : ℕ)
    (hcover : ∀ x : Base, ∃ p ∈ P, ∃ z ∈ ball (0 : Yau.Jets.Coord) s,
      sphereChartCoordMap p z=x)
    (w : ℕ → Base → ℝ) (hw : ∀ j, ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ (w j))
    (B : {p // p ∈ P} → ℝ) (hB : ∀ p, 0 ≤ B p)
    (hb : ∀ (p : {p // p ∈ P}) j (ds : List (Fin 4)), ds.length ≤ n+1 →
      ∀ x ∈ closedBall (0 : Yau.Jets.Coord) r,
        |partialJet (w j ∘ sphereChartCoordMap p.val) ds x| ≤ B p) :
    ∃ v : Base → ℝ, ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) n v ∧
      ∃ nu : ℕ → ℕ, StrictMono nu ∧ TendstoUniformly (fun j ↦ w (nu j)) v atTop ∧
        ∀ p ∈ P, ∀ ds : List (Fin 4), ds.length ≤ n →
          TendstoUniformlyOn (fun j ↦ partialJet (w (nu j) ∘ sphereChartCoordMap p) ds)
            (partialJet (v ∘ sphereChartCoordMap p) ds) atTop (ball 0 r) := by
  classical
  obtain ⟨nu,hnu,hlim⟩ := real_finite_atlas_ball_subsequence
    (fun (p : {p // p ∈ P}) j ↦ w j ∘ sphereChartCoordMap p.val)
    (fun p j ↦ ((hw j).comp (sphereChartCoordMap_smooth p.val)).contDiff) r n B hB hb
  choose f hfc hfs hft hfj using hlim
  obtain ⟨v,hv,ht,hvchart⟩ := sphere_finite_order_limit_gluing P r n (by
    intro x
    obtain ⟨p,hp,z,hz,he⟩ := hcover x
    exact ⟨p,hp,z,ball_subset_ball hsr.le hz,he⟩) (fun j ↦ w (nu j)) f hfs hft
  refine ⟨v,hv,nu,hnu,ht,?_⟩
  intro p hp ds hd
  apply (hfj ⟨p,hp⟩ ds hd).congr_right
  intro x hx
  exact (partialJet_germ_eq (v ∘ sphereChartCoordMap p) (f ⟨p,hp⟩) x
    (Filter.Eventually.mono (isOpen_ball.mem_nhds hx) (fun y hy ↦ hvchart ⟨p,hp⟩ hy)) ds).symm

end
end Yau.Target

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
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_RealJetProductExpansion
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

lemma realJetProductSum_smooth (a b : Yau.Jets.Coord → ℝ)
    (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b)
    (ts : List (List (Fin 4) × List (Fin 4))) :
    ContDiff ℝ ∞ (realJetProductSum a b ts) := by
  induction ts with
  | nil => exact contDiff_const
  | cons t ts ih =>
    exact ((partialJet_smooth a ha t.1).mul (partialJet_smooth b hb t.2)).add ih

lemma realJetProductSum_partial (a b : Yau.Jets.Coord → ℝ)
    (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b)
    (ts : List (List (Fin 4) × List (Fin 4))) (l : Fin 4) (x : Yau.Jets.Coord) :
    Yau.coordPartial (realJetProductSum a b ts) x l =
      realJetProductSum a b (ts.map (fun t ↦ (l::t.1,t.2))) x +
      realJetProductSum a b (ts.map (fun t ↦ (t.1,l::t.2))) x := by
  induction ts with
  | nil =>
    change Yau.coordPartial (fun _ ↦ (0:ℝ)) x l = 0+0
    simp [Yau.coordPartial]
  | cons t ts ih =>
    change Yau.coordPartial (fun y ↦ partialJet a t.1 y*partialJet b t.2 y +
      realJetProductSum a b ts y) x l = _
    rw [Yau.real_coordPartial_add _ _
      ((partialJet_smooth a ha t.1).mul (partialJet_smooth b hb t.2))
      (realJetProductSum_smooth a b ha hb ts),
      Yau.real_coordPartial_mul _ _ (partialJet_smooth a ha t.1) (partialJet_smooth b hb t.2),ih]
    simp only [realJetProductSum,List.map_cons,List.sum_cons,partialJet,Yau.coordPartial]
    ring

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

lemma realJetErrorTerms_length (extra ds : List (Fin 4)) :
    (realJetErrorTerms extra ds).length ≤ 3^ds.length := by
  induction ds with
  | nil => simp [realJetErrorTerms]
  | cons l ds ih =>
    have hp : 1 ≤ (3:ℕ)^ds.length := Nat.one_le_pow _ _ (by decide)
    simp only [realJetErrorTerms,List.length_append,List.length_map,List.length_cons,
      List.length_nil,pow_succ]
    omega

lemma realJetProductSum_error_cons (a b : Yau.Jets.Coord → ℝ)
    (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b)
    (extra ds : List (Fin 4)) (l : Fin 4) (x : Yau.Jets.Coord) :
    realJetProductSum a b (realJetErrorTerms extra (l::ds)) x =
      Yau.coordPartial (realJetProductSum a b (realJetErrorTerms extra ds)) x l +
        Yau.coordPartial a x l * partialJet b (extra++ds) x := by
  rw [realJetProductSum_partial a b ha hb]
  simp [realJetErrorTerms,realJetProductSum,partialJet,Yau.coordPartial,add_assoc]

end
end Yau.Geometry

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

theorem real_closedBall_subset_cube {n : ℕ} (r : ℝ) :
    closedBall (0 : Coord n) r ⊆ realCenteredCube n r := by
  intro x hx i hi
  have hx' : ‖x‖ ≤ r := by simpa only [mem_closedBall,dist_zero_right] using hx
  exact abs_le.mp ((norm_le_pi_norm x i).trans hx')

theorem real_closedBall_subset_cube_interior {n : ℕ} {r R : ℝ} (h : r < R) :
    closedBall (0 : Coord n) r ⊆ interior (realCenteredCube n R) := by
  intro x hx
  rw [realCenteredCube,interior_pi_set finite_univ]
  intro i hi
  rw [interior_Icc]
  have hb := (real_closedBall_subset_cube r hx) i hi
  exact ⟨(neg_lt_neg h).trans_le hb.1,hb.2.trans_lt h⟩

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

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Spectral_SphereEigenGlobalNormalization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open MeasureTheory Manifold Set Yau.Geometry
open scoped ContDiff
noncomputable section
attribute [local instance] sphereGlobalRepresentativeMeasurable sphereGlobalRepresentativeBorel

theorem sphere_L2_representative_pairing (d : SphereEnergyData) (f : SphereWeightedL2 d)
    (u : Base → ℝ) (ha : u =ᵐ[sphereWeightedMeasure d.density] (f : Base → ℝ)) :
    sphereWeightedPairing d.density u u=‖f‖^2 := by
  rw [sphereWeightedPairing,sphereWeightedL2_norm_sq_integral]
  apply integral_congr_ae
  filter_upwards [(sphereWeightedMeasure_ae_iff d _).mp ha] with x hx
  rw [hx]
  ring

theorem sphere_eigen_global_normalized (d : SphereEnergyData)
    (hrho : ∀ p : Base, ContDiff ℝ ∞ (fun x ↦ d.density (sphereChartCoordMap p x)))
    (mu : ℝ) (hmu : mu ≠ 0) (f : SphereWeightedL2 d)
    (heigen : sphereL2Resolvent d f=mu • f) (hn : ‖f‖=1) :
    ∃ u : Base → ℝ, ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ u ∧
      u =ᵐ[sphereWeightedMeasure d.density] (f : Base → ℝ) ∧
      sphereWeightedPairing d.density u u=1 ∧ u ≠ 0 ∧
      ∀ p x, x ∈ interior (Yau.realCenteredCube 4 (1/64)) →
        Yau.coordDiv (realMatrixFlux (sphereChartPrincipalDensity d p) (u ∘ sphereChartCoordMap p)) x+
          sphereEigenForcingCoefficient d p mu x*u (sphereChartCoordMap p x)=0 := by
  obtain ⟨u,hu,ha,he⟩ := sphere_eigen_global_representative d hrho mu hmu f heigen
  have hnorm : sphereWeightedPairing d.density u u=1 := by
    rw [sphere_L2_representative_pairing d f u ha,hn,one_pow]
  refine ⟨u,hu,ha,hnorm,?_,he⟩
  intro hz
  simp only [hz,sphereWeightedPairing,Pi.zero_apply,mul_zero,integral_zero] at hnorm
  norm_num at hnorm

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Charts_SphereUniformChartL2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open MeasureTheory Set Yau.Geometry
noncomputable section

local instance sphereUniformChartMeasurable_r6a81dc_1 : MeasurableSpace Base := borel Base
local instance sphereUniformChartBorel_r6a81dc_1 : BorelSpace Base := ⟨rfl⟩
theorem sphereWeightedL2_chart_bound_of_lower (d : SphereEnergyData) (p : Base)
    {K : Set Yau.Jets.Coord} (hK : IsCompact K) (q : ℝ) (hq : 0 < q)
    (hlow : ∀ x ∈ K, q ≤ roundCoordDensity x*d.density (sphereChartCoordMap p x))
    (f : SphereWeightedL2 d) :
    MemLp (fun x ↦ f (sphereChartCoordMap p x)) 2 (volume.restrict K) ∧
      (∫ x in K, (f (sphereChartCoordMap p x))^2) ≤ q⁻¹*‖f‖^2 := by
  let a := fun x ↦ roundCoordDensity x*d.density (sphereChartCoordMap p x)
  have hf := sphereWeightedL2_chart_aestronglyMeasurable d f p
  have hs := (Lp.memLp f).integrable_sq
  have hi : Integrable (fun x ↦ a x*(f (sphereChartCoordMap p x))^2) := by
    have h := (sphereReferenceMeasure_integrable_chart p _).mp
      ((sphereWeightedMeasure_integrable_iff d _).mp hs)
    simpa only [roundChartDensity_coord_eq,a,mul_assoc] using h
  have hbound : ∀ x ∈ K, (f (sphereChartCoordMap p x))^2 ≤ q⁻¹*(a x*(f (sphereChartCoordMap p x))^2) := by
    intro x hx
    have h := mul_le_mul_of_nonneg_right (hlow x hx) (sq_nonneg (f (sphereChartCoordMap p x)))
    calc
      _ = q⁻¹*(q*(f (sphereChartCoordMap p x))^2) := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left h (inv_nonneg.mpr hq.le)
  have his : IntegrableOn (fun x ↦ (f (sphereChartCoordMap p x))^2) K := by
    apply ((hi.const_mul q⁻¹).integrableOn).mono' (hf.pow 2).restrict
    filter_upwards [ae_restrict_mem hK.measurableSet] with x hx
    change |(f (sphereChartCoordMap p x))^2| ≤ _
    rw [abs_of_nonneg (sq_nonneg _)]
    exact hbound x hx
  refine ⟨(memLp_two_iff_integrable_sq hf.restrict).mpr his,?_⟩
  calc
    _ ≤ ∫ x in K, q⁻¹*(a x*(f (sphereChartCoordMap p x))^2) :=
      setIntegral_mono_on his (hi.const_mul q⁻¹).integrableOn hK.measurableSet hbound
    _ ≤ ∫ x, q⁻¹*(a x*(f (sphereChartCoordMap p x))^2) :=
      setIntegral_le_integral (hi.const_mul q⁻¹) (Filter.Eventually.of_forall (fun x ↦ by
        exact mul_nonneg (inv_nonneg.mpr hq.le)
          (mul_nonneg (mul_pos (roundCoordDensity_pos x) (d.positive _)).le (sq_nonneg _))))
    _ = _ := by
      rw [integral_const_mul,sphereWeightedL2_norm_sq_integral,sphereReferenceMeasure_integral_chart p]
      simp only [roundChartDensity_coord_eq,a,mul_assoc]

theorem sphereWeightedL2_chart_neighborhood (d₀ : SphereEnergyData) (p : Base)
    {Q : Set Yau.Jets.Coord} (hQ : IsCompact Q) :
    ∃ eps > 0, ∃ K > 0, ∀ d : SphereEnergyData,
      (∀ x ∈ Q, |roundCoordDensity x*d.density (sphereChartCoordMap p x)-
        roundCoordDensity x*d₀.density (sphereChartCoordMap p x)| ≤ eps) →
      ∀ f : SphereWeightedL2 d,
        MemLp (fun x ↦ f (sphereChartCoordMap p x)) 2 (volume.restrict Q) ∧
        (∫ x in Q, (f (sphereChartCoordMap p x))^2) ≤ K*‖f‖^2 := by
  obtain ⟨q,hq,_,_,hb⟩ := Yau.Jets.compact_positive_bounds hQ
    (fun x ↦ roundCoordDensity x*d₀.density (sphereChartCoordMap p x))
    ((roundCoordDensity_smooth.continuous.mul
      (d₀.continuous.comp (sphereChartCoordMap_smooth p).continuous)).continuousOn)
    (fun x _ ↦ mul_pos (roundCoordDensity_pos x) (d₀.positive _))
  refine ⟨q/2,by positivity,(q/2)⁻¹,by positivity,fun d hclose f ↦ ?_⟩
  apply sphereWeightedL2_chart_bound_of_lower d p hQ (q/2) (by positivity) _ f
  intro x hx
  have h := (abs_le.mp (hclose x hx)).1
  have hbase := (hb x hx).1
  linarith

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_CompactParameterEllipticityLemmas
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Yau.Geometry

section

open Set
variable {T : Type*} [TopologicalSpace T] [CompactSpace T]

theorem compact_parameter_matrix_ellipticity
    (B : T → Yau.Jets.Coord → Matrix (Fin 4) (Fin 4) ℝ) {Q : Set Yau.Jets.Coord}
    (hQ : IsCompact Q)
    (hB : ∀ i j, Continuous (fun z : T × Q ↦ B z.1 z.2 i j))
    (hp : ∀ t x, x ∈ Q → (B t x).PosDef) :
    ∃ k > 0, ∃ L > 0, ∀ t x, x ∈ Q → ∀ v : Yau.Jets.Coord,
      k*(∑ i, v i^2) ≤ (∑ i, ∑ j, v i*B t x i j*v j) ∧
      (∑ i, ∑ j, v i*B t x i j*v j) ≤ L*(∑ i, v i^2) := by
  let : CompactSpace Q := isCompact_iff_compactSpace.mp hQ
  let g := fun z : T × Q ↦ coordMatrixForm (B z.1 z.2)
  obtain ⟨k,hk,L,hL,hb⟩ := uniform_metric_coercivity g
    (coordMatrixForm_continuous (fun z : T × Q ↦ B z.1 z.2) hB)
    (fun z v hv ↦ coordMatrixForm_positive _ (hp z.1 z.2 z.2.property) v hv)
  refine ⟨k/4,by positivity,L,hL,?_⟩
  intro t x hx v
  have h := hb (t,⟨x,hx⟩)
  have hlo : k*‖v‖^2 ≤ coordMatrixForm (B t x) v v := h.2 v
  have hhi : coordMatrixForm (B t x) v v ≤ L*‖v‖^2 := calc
    _ ≤ |coordMatrixForm (B t x) v v| := le_abs_self _
    _ ≤ ‖g (t,⟨x,hx⟩)‖*‖v‖*‖v‖ := bilinear_pairing_bound _ v v
    _ ≤ L*‖v‖^2 := by nlinarith [mul_le_mul_of_nonneg_right h.1 (sq_nonneg ‖v‖)]
  rw [coordMatrixForm_apply] at hlo hhi
  constructor
  · nlinarith [mul_le_mul_of_nonneg_left (coord_sum_sq_le_four_norm_sq v) hk.le]
  · exact hhi.trans (mul_le_mul_of_nonneg_left (coord_norm_sq_le_sum_sq v) hL.le)

lemma compact_parameter_scalar_bound (f : T → Yau.Jets.Coord → ℝ)
    {Q : Set Yau.Jets.Coord} (hQ : IsCompact Q)
    (hf : Continuous (fun z : T × Q ↦ f z.1 z.2)) :
    ∃ M > 0, ∀ t x, x ∈ Q → |f t x| ≤ M := by
  let : CompactSpace Q := isCompact_iff_compactSpace.mp hQ
  obtain ⟨M,hM,hb⟩ := (isCompact_univ.image hf).isBounded.exists_pos_norm_le
  refine ⟨M,hM,?_⟩
  intro t x hx
  exact hb _ ⟨(t,⟨x,hx⟩),mem_univ _,rfl⟩

end

open Metric
attribute [local instance] clmTopology clmAdd clmModule

end Yau.Geometry

end

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_CompactParameterDerivativeBounds
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
noncomputable section
variable {T : Type*} [TopologicalSpace T] [CompactSpace T]
variable {ι : Type*} [Fintype ι]

lemma compact_parameter_finite_scalar_bound (f : ι → T → Yau.Jets.Coord → ℝ)
    {Q : Set Yau.Jets.Coord} (hQ : IsCompact Q)
    (hf : ∀ i, Continuous (fun z : T × Q ↦ f i z.1 z.2)) :
    ∃ M > 0, ∀ i t x, x ∈ Q → |f i t x| ≤ M := by
  classical
  have hb (i : ι) := compact_parameter_scalar_bound (f i) hQ (hf i)
  choose M hM hb using hb
  refine ⟨1+∑ i, |M i|,by positivity,?_⟩
  intro i t x hx
  have h := (hb i t x hx).trans ((le_abs_self (M i)).trans
    (Finset.single_le_sum (fun j _ ↦ abs_nonneg (M j)) (Finset.mem_univ i)))
  linarith

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_CompactParameterJetBounds
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Yau.Analysis
noncomputable section
variable {T : Type*} [TopologicalSpace T] [CompactSpace T]
variable {ι : Type*} [Fintype ι]

theorem compact_parameter_finite_jet_bound (n : ℕ)
    (f : ι → T → Yau.Jets.Coord → ℝ) {Q : Set Yau.Jets.Coord} (hQ : IsCompact Q)
    (hf : ∀ i ds, ds.length ≤ n → Continuous (fun z : T × Q ↦ partialJet (f i z.1) ds z.2)) :
    ∃ B > 0, ∀ i t x, x ∈ Q → ∀ ds : List (Fin 4), ds.length ≤ n →
      |partialJet (f i t) ds x| ≤ B := by
  let I := ι × (Σ r : Fin (n+1), Fin r.val → Fin 4)
  obtain ⟨B,hB,hbound⟩ := compact_parameter_finite_scalar_bound
    (fun e : I ↦ fun t x ↦ partialJet (f e.1 t) (List.ofFn e.2.2) x)
    hQ (fun e ↦ hf e.1 _ (by simp only [List.length_ofFn]; exact Nat.le_of_lt_succ e.2.1.isLt))
  refine ⟨B,hB,?_⟩
  intro i t x hx ds hd
  have h := hbound (i,⟨⟨ds.length,by omega⟩,ds.get⟩) t x hx
  simpa only [List.ofFn_get] using h

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_RealMatrixEntryPerturbation
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
noncomputable section

theorem real_matrix_entry_perturbation (A B : Matrix (Fin 4) (Fin 4) ℝ)
    (eps : ℝ) (heps : 0 ≤ eps) (hAB : ∀ i j, |A i j-B i j| ≤ eps)
    (z : Yau.Jets.Coord) :
    |(∑ i, ∑ j, z i*A i j*z j)-(∑ i, ∑ j, z i*B i j*z j)| ≤
      16*eps*(∑ i, z i^2) := by
  let S : ℝ := ∑ i, z i^2
  have hzi (i : Fin 4) : (z i)^2 ≤ S :=
    Finset.single_le_sum (fun j _ ↦ sq_nonneg (z j)) (Finset.mem_univ i)
  have hz (i j : Fin 4) : |z i| * |z j| ≤ S := by
    nlinarith [sq_abs (z i),sq_abs (z j),sq_nonneg (|z i|-|z j|),hzi i,hzi j]
  have ht (i j : Fin 4) : |z i*(A i j-B i j)*z j| ≤ eps*S := by
    rw [abs_mul,abs_mul]
    have h := mul_le_mul_of_nonneg_left (hAB i j) (mul_nonneg (abs_nonneg (z i)) (abs_nonneg (z j)))
    have h' := mul_le_mul_of_nonneg_left (hz i j) heps
    nlinarith only [h,h']
  have he : (∑ i, ∑ j, z i*A i j*z j)-(∑ i, ∑ j, z i*B i j*z j)=
      ∑ i, ∑ j, z i*(A i j-B i j)*z j := by
    simp only [mul_sub,sub_mul,Finset.sum_sub_distrib]
  rw [he]
  calc
    _ ≤ ∑ i, |∑ j, z i*(A i j-B i j)*z j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, ∑ j, |z i*(A i j-B i j)*z j| :=
      Finset.sum_le_sum (fun i _ ↦ Finset.abs_sum_le_sum_abs _ _)
    _ ≤ ∑ _i : Fin 4, ∑ _j : Fin 4, eps*S :=
      Finset.sum_le_sum (fun i _ ↦ Finset.sum_le_sum (fun j _ ↦ ht i j))
    _ = _ := by simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] <;> ring

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_RealEllipticityNeighborhood
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Set
noncomputable section

theorem real_ellipticity_neighborhood (Q : Set Yau.Jets.Coord)
    (C₀ : Yau.Jets.Coord → Matrix (Fin 4) (Fin 4) ℝ)
    (k L : ℝ) (hk : 0 < k)
    (hlo : ∀ x ∈ Q, ∀ z : Yau.Jets.Coord,
      k*(∑ i, z i^2) ≤ ∑ i, ∑ j, z i*C₀ x i j*z j)
    (hhi : ∀ x ∈ Q, ∀ z : Yau.Jets.Coord,
      (∑ i, ∑ j, z i*C₀ x i j*z j) ≤ L*(∑ i, z i^2))
    (C : Yau.Jets.Coord → Matrix (Fin 4) (Fin 4) ℝ)
    (hclose : ∀ x ∈ Q, ∀ i j, |C x i j-C₀ x i j| ≤ k/32) :
    ∀ x ∈ Q, ∀ z : Yau.Jets.Coord,
      (k/2)*(∑ i, z i^2) ≤ (∑ i, ∑ j, z i*C x i j*z j) ∧
      (∑ i, ∑ j, z i*C x i j*z j) ≤ (L+k/2)*(∑ i, z i^2) := by
  intro x hx z
  have h := real_matrix_entry_perturbation (C x) (C₀ x) (k/32) (by positivity) (hclose x hx) z
  obtain ⟨h₁,h₂⟩ := abs_le.mp h
  constructor <;> nlinarith only [h₁,h₂,hlo x hx z,hhi x hx z]

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_RealFiniteJetIntegrals
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Yau.Analysis MeasureTheory
open scoped ContDiff
noncomputable section

lemma real_cutoff_square_integrable (eta H : Yau.Jets.Coord → ℝ)
    (heta : ContDiff ℝ ∞ eta) (hc : HasCompactSupport eta) (hH : Continuous H) :
    Integrable (fun x ↦ eta x^2*H x) := by
  have hsq : HasCompactSupport (fun x ↦ eta x^2) := by
    convert hc.mul_right (f' := eta) using 1
    all_goals try with_reducible_and_instances rfl
    first | rfl | (ext x; simp [pow_two])
  exact ((heta.pow 2).continuous.mul hH).integrable_of_hasCompactSupport hsq.mul_right

lemma realFiniteJetSquare_zero (W : Yau.Jets.Coord → ℝ) (x : Yau.Jets.Coord) :
    realFiniteJetSquare W 0 x = W x^2 := by
  simp [realFiniteJetSquare,partialJet]

lemma realFiniteJetSquare_integrable (eta W : Yau.Jets.Coord → ℝ)
    (heta : ContDiff ℝ ∞ eta) (hc : HasCompactSupport eta)
    (hW : ContDiff ℝ ∞ W) (n : ℕ) :
    Integrable (fun x ↦ eta x^2*realFiniteJetSquare W n x) :=
  real_cutoff_square_integrable eta _ heta hc (realFiniteJetSquare_smooth W hW n).continuous

lemma realFiniteJetSquare_integral_sum (eta W : Yau.Jets.Coord → ℝ)
    (heta : ContDiff ℝ ∞ eta) (hc : HasCompactSupport eta)
    (hW : ContDiff ℝ ∞ W) (n : ℕ) :
    (∫ x, eta x^2*realFiniteJetSquare W n x) =
      ∑ r ∈ Finset.range (n+1), ∑ w : Fin r → Fin 4, ∫ x, eta x^2*(partialJet W (List.ofFn w) x)^2 := by
  have hi (r : ℕ) (w : Fin r → Fin 4) :
      Integrable (fun x ↦ eta x^2*(partialJet W (List.ofFn w) x)^2) :=
    real_cutoff_square_integrable eta _ heta hc ((partialJet_smooth W hW _).pow 2).continuous
  simp only [realFiniteJetSquare,Finset.mul_sum]
  rw [integral_finsetSum _ (fun r _ ↦ integrable_finsetSum _ (fun w _ ↦ hi r w))]
  apply Finset.sum_congr rfl
  intro r _
  exact integral_finsetSum _ (fun w _ ↦ hi r w)

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_RealCutoffAbsorption
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Yau.Jets
noncomputable section

lemma real_young_quarter (k a b : ℝ) (hk : 0 < k) :
    a*b ≤ k/4*a^2+k⁻¹*b^2 := by
  have hi : k*k⁻¹=1 := mul_inv_cancel₀ hk.ne'
  have h := sq_nonneg (k*a-2*b)
  have ht := mul_nonneg (inv_nonneg.mpr hk.le) h
  nlinarith [hi]

lemma real_dot_young_quarter (k : ℝ) (hk : 0 < k) (v w : Yau.Jets.Coord) :
    (∑ i, v i*w i) ≤ k/4*(∑ i, v i^2)+k⁻¹*(∑ i, w i^2) := by
  have h := Finset.sum_le_sum (s := Finset.univ) (fun i _ ↦ real_young_quarter k (v i) (w i) hk)
  simpa only [Finset.sum_add_distrib,← Finset.mul_sum] using h

lemma real_dot_young (v w : Yau.Jets.Coord) :
    2*(∑ i, v i*w i) ≤ (∑ i, v i^2)+(∑ i, w i^2) := by
  have h := Finset.sum_nonneg (s := Finset.univ) (fun i _ ↦ sq_nonneg (v i-w i))
  simp only [sub_sq,Finset.sum_add_distrib,Finset.sum_sub_distrib,mul_assoc,← Finset.mul_sum] at h
  nlinarith only [h]

lemma real_matrix_cutoff_absorption (B : Matrix (Fin 4) (Fin 4) ℝ)
    (hs : ∀ i j, B i j = B j i)
    (hn : ∀ v : Yau.Jets.Coord, 0 ≤ coordMatrixForm B v v)
    (eta W : ℝ) (g d : Yau.Jets.Coord) :
    -(2*eta*W*coordMatrixForm B d g) ≤
      (eta^2*coordMatrixForm B g g)/4+4*W^2*coordMatrixForm B d d := by
  have h := hn (eta • g+(4*W) • d)
  simp only [map_add,map_smul,_root_.add_apply,_root_.smul_apply,smul_eq_mul] at h
  rw [coordMatrixForm_symmetric B hs g d] at h
  nlinarith only [h]

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_RealInhomogeneousPointwise
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
noncomputable section

lemma real_inhomogeneous_pointwise (k L M : ℝ) (hk : 0 < k) (hL : 0 < L) (hM : 0 ≤ M)
    (B : Matrix (Fin 4) (Fin 4) ℝ) (hs : ∀ i j, B i j=B j i)
    (hlo : ∀ z : Yau.Jets.Coord, k*(∑ i, z i^2) ≤ coordMatrixForm B z z)
    (hhi : ∀ z : Yau.Jets.Coord, coordMatrixForm B z z ≤ L*(∑ i, z i^2))
    (eta W V f : ℝ) (hV : |V| ≤ M) (g d F : Yau.Jets.Coord) :
    k/2*(eta^2*(∑ i, g i^2)) ≤
      (eta^2*coordMatrixForm B g g+2*eta*W*coordMatrixForm B d g -
        eta^2*W*V*W - (eta^2*(∑ i, g i*F i)+2*eta*W*(∑ i, d i*F i)) +eta^2*W*f) +
      (M+4*L+k⁻¹+3)*((eta^2+(∑ i, d i^2))*W^2+eta^2*f^2+eta^2*(∑ i, F i^2)) := by
  have hn (z : Yau.Jets.Coord) : 0 ≤ coordMatrixForm B z z :=
    (mul_nonneg hk.le (Finset.sum_nonneg (fun i _ ↦ sq_nonneg (z i)))).trans (hlo z)
  have hcross := real_matrix_cutoff_absorption B hs hn eta W g d
  have hg := mul_le_mul_of_nonneg_left (hlo g) (sq_nonneg eta)
  have hd := mul_le_mul_of_nonneg_left (hhi d) (sq_nonneg W)
  have hp1 := mul_le_mul_of_nonneg_left (real_dot_young_quarter k hk g F) (sq_nonneg eta)
  have hp2 := real_dot_young (fun i ↦ W*d i) (fun i ↦ eta*F i)
  simp only [mul_pow,mul_assoc,← Finset.mul_sum] at hp2
  have hpot := mul_le_mul_of_nonneg_left ((le_abs_self V).trans hV) (mul_nonneg (sq_nonneg eta) (sq_nonneg W))
  have hf := mul_nonneg (sq_nonneg eta) (sq_nonneg (W+f))
  have hg0 : 0 ≤ ∑ i, g i^2 := Finset.sum_nonneg (fun i _ ↦ sq_nonneg _)
  have hd0 : 0 ≤ ∑ i, d i^2 := Finset.sum_nonneg (fun i _ ↦ sq_nonneg _)
  have hF0 : 0 ≤ ∑ i, F i^2 := Finset.sum_nonneg (fun i _ ↦ sq_nonneg _)
  have hdi : 0 ≤ k⁻¹ := inv_nonneg.mpr hk.le
  have hp2' : 2*eta*W*(∑ i, d i*F i) ≤ W^2*(∑ i, d i^2)+eta^2*(∑ i, F i^2) := by
    convert hp2 using 1
    all_goals try with_reducible_and_instances rfl
    rw [Finset.mul_sum,Finset.mul_sum,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have base : k/2*(eta^2*(∑ i, g i^2)) ≤
      (eta^2*coordMatrixForm B g g+2*eta*W*coordMatrixForm B d g -
        eta^2*W*V*W - (eta^2*(∑ i, g i*F i)+2*eta*W*(∑ i, d i*F i)) +eta^2*W*f) +
      (M+1)*(eta^2*W^2)+(4*L+1)*((∑ i, d i^2)*W^2)+
        eta^2*f^2+(k⁻¹+1)*(eta^2*(∑ i, F i^2)) := by
    nlinarith only [hcross,hg,hd,hp1,hp2',hpot,hf,
      mul_nonneg (sq_nonneg eta) (sq_nonneg W),mul_nonneg (sq_nonneg eta) (sq_nonneg f)]
  have h1 := mul_nonneg (show 0 ≤ 4*L+k⁻¹+2 by positivity) (mul_nonneg (sq_nonneg eta) (sq_nonneg W))
  have h2 := mul_nonneg (show 0 ≤ M+k⁻¹+2 by positivity) (mul_nonneg hd0 (sq_nonneg W))
  have h3 := mul_nonneg (show 0 ≤ M+4*L+k⁻¹+2 by positivity) (mul_nonneg (sq_nonneg eta) (sq_nonneg f))
  have h4 := mul_nonneg (show 0 ≤ M+4*L+2 by positivity) (mul_nonneg (sq_nonneg eta) hF0)
  nlinarith only [base,h1,h2,h3,h4]

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_RealInhomogeneousWeakEquation
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open MeasureTheory
open scoped ContDiff
noncomputable section

lemma real_coord_integration_by_parts (phi : Yau.Jets.Coord → ℝ)
    (hphi : ContDiff ℝ ∞ phi) (hc : HasCompactSupport phi)
    (F : Yau.Jets.Coord → Yau.Jets.Coord) (hF : ∀ i, ContDiff ℝ ∞ (fun x ↦ F x i)) :
    Integrable (Yau.pairing phi F) ∧ Integrable (fun x ↦ phi x*Yau.coordDiv F x) ∧
      (∫ x, Yau.pairing phi F x) = -(∫ x, phi x*Yau.coordDiv F x) := by
  have hh := Yau.compact_weighted_integration_by_parts (fun _ ↦ 1) phi contDiff_const
    (fun _ ↦ one_ne_zero) hphi hc F hF
  simpa only [Yau.weightedDiv,inv_one,one_mul] using hh

theorem real_inhomogeneous_density_test (C : Yau.Jets.Coord → Matrix (Fin 4) (Fin 4) ℝ)
    (V W f phi : Yau.Jets.Coord → ℝ) (F : Yau.Jets.Coord → Yau.Jets.Coord)
    (hC : ∀ i j, ContDiff ℝ ∞ (fun x ↦ C x i j)) (hV : ContDiff ℝ ∞ V)
    (hW : ContDiff ℝ ∞ W) (hf : ContDiff ℝ ∞ f)
    (hF : ∀ i, ContDiff ℝ ∞ (fun x ↦ F x i))
    (hphi : ContDiff ℝ ∞ phi) (hc : HasCompactSupport phi)
    (he : ∀ x, Yau.coordDiv (realMatrixFlux C W) x+V x*W x=Yau.coordDiv F x+f x) :
    Integrable (realMatrixEnergy C phi W) ∧
    Integrable (fun x ↦ phi x*V x*W x) ∧
    Integrable (Yau.pairing phi F) ∧ Integrable (fun x ↦ phi x*f x) ∧
    (∫ x, realMatrixEnergy C phi W x) = (∫ x, phi x*V x*W x)+
      (∫ x, Yau.pairing phi F x)-(∫ x, phi x*f x) := by
  obtain ⟨hiP,hiD,hP⟩ := real_coord_integration_by_parts phi hphi hc (realMatrixFlux C W)
    (realMatrixFlux_smooth C W hC hW)
  obtain ⟨hiF,hiDF,hFE⟩ := real_coord_integration_by_parts phi hphi hc F hF
  have hiV : Integrable (fun x ↦ phi x*V x*W x) :=
    ((hphi.mul hV).mul hW).continuous.integrable_of_hasCompactSupport hc.mul_right.mul_right
  have hif : Integrable (fun x ↦ phi x*f x) :=
    (hphi.mul hf).continuous.integrable_of_hasCompactSupport hc.mul_right
  have hid : (∫ x, phi x*Yau.coordDiv (realMatrixFlux C W) x+phi x*V x*W x) =
      (∫ x, phi x*Yau.coordDiv F x+phi x*f x) := by
    apply integral_congr_ae
    filter_upwards [] with x
    linear_combination phi x*he x
  rw [integral_add hiD hiV,integral_add hiDF hif] at hid
  have hpEq : Yau.pairing phi (realMatrixFlux C W) = realMatrixEnergy C phi W :=
    funext (realMatrixEnergy_pairing C phi W)
  rw [hpEq] at hiP hP
  refine ⟨hiP,hiV,hiF,hif,?_⟩
  linarith only [hid,hP,hFE]

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_RealInhomogeneousCaccioppoli
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open MeasureTheory
open scoped ContDiff
noncomputable section

lemma real_pairing_cutoff (eta W : Yau.Jets.Coord → ℝ)
    (heta : ContDiff ℝ ∞ eta) (hW : ContDiff ℝ ∞ W)
    (F : Yau.Jets.Coord → Yau.Jets.Coord) (x : Yau.Jets.Coord) :
    Yau.pairing (fun y ↦ eta y^2*W y) F x =
      eta x^2*(∑ i, Yau.coordPartial W x i*F x i)+
        2*eta x*W x*(∑ i, Yau.coordPartial eta x i*F x i) := by
  change (∑ i, realCoordGradient (fun y ↦ eta y^2*W y) x i*F x i) = _
  rw [realCoordGradient_cutoff eta W heta hW x]
  simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul,add_mul,Finset.sum_add_distrib,
    mul_assoc,← Finset.mul_sum,realCoordGradient]

theorem real_inhomogeneous_caccioppoli (k L M : ℝ)
    (hk : 0 < k) (hL : 0 < L) (hM : 0 ≤ M) :
    ∃ K > 0, ∀ (C : Yau.Jets.Coord → Matrix (Fin 4) (Fin 4) ℝ)
      (V W f eta : Yau.Jets.Coord → ℝ) (F : Yau.Jets.Coord → Yau.Jets.Coord),
      (∀ i j, ContDiff ℝ ∞ (fun x ↦ C x i j)) → ContDiff ℝ ∞ V →
      ContDiff ℝ ∞ W → ContDiff ℝ ∞ f → ContDiff ℝ ∞ eta →
      (∀ i, ContDiff ℝ ∞ (fun x ↦ F x i)) → HasCompactSupport eta →
      (∀ x i j, C x i j=C x j i) →
      (∀ x ∈ tsupport eta, ∀ z : Yau.Jets.Coord,
        k*(∑ i, z i^2) ≤ ∑ i, ∑ j, z i*C x i j*z j) →
      (∀ x ∈ tsupport eta, ∀ z : Yau.Jets.Coord,
        (∑ i, ∑ j, z i*C x i j*z j) ≤ L*(∑ i, z i^2)) →
      (∀ x ∈ tsupport eta, |V x| ≤ M) →
      (∀ x, Yau.coordDiv (realMatrixFlux C W) x+V x*W x=Yau.coordDiv F x+f x) →
      Integrable (fun x ↦ eta x^2*realGradientSquare W x) ∧
      Integrable (fun x ↦ (eta x^2+realGradientSquare eta x)*W x^2) ∧
      Integrable (fun x ↦ eta x^2*f x^2) ∧
      Integrable (fun x ↦ eta x^2*(∑ i, F x i^2)) ∧
      (∫ x, eta x^2*realGradientSquare W x) ≤ K *
        ((∫ x, (eta x^2+realGradientSquare eta x)*W x^2)+
          (∫ x, eta x^2*f x^2)+(∫ x, eta x^2*(∑ i, F x i^2))) := by
  let D := M+4*L+k⁻¹+3
  refine ⟨(2/k)*D,by dsimp [D] <;> positivity,?_⟩
  intro C V W f eta F hC hV hW hf heta hF hc hs hlo hhi hpot he
  let phi := fun x ↦ eta x^2*W x
  let a := fun x ↦ eta x^2*realGradientSquare W x
  let q := fun x ↦ (eta x^2+realGradientSquare eta x)*W x^2
  let r := fun x ↦ eta x^2*f x^2
  let s := fun x ↦ eta x^2*(∑ i, F x i^2)
  have hcsq : HasCompactSupport (fun x ↦ eta x^2) := by
    convert hc.mul_right (f' := eta) using 1
    all_goals try with_reducible_and_instances rfl
    first | rfl | (ext x; simp [pow_two])
  have ha : Integrable a := ((heta.pow 2).mul (realGradientSquare_smooth W hW)).continuous.integrable_of_hasCompactSupport hcsq.mul_right
  have hq : Integrable q := (((heta.pow 2).add (realGradientSquare_smooth eta heta)).mul (hW.pow 2)).continuous.integrable_of_hasCompactSupport
    (hcsq.add (realGradientSquare_compact eta hc)).mul_right
  have hr : Integrable r := ((heta.pow 2).mul (hf.pow 2)).continuous.integrable_of_hasCompactSupport hcsq.mul_right
  have hsint : Integrable s := ((heta.pow 2).mul (ContDiff.sum (fun i _ ↦ (hF i).pow 2))).continuous.integrable_of_hasCompactSupport hcsq.mul_right
  obtain ⟨hE,hP,hFint,hfint,hweak⟩ := real_inhomogeneous_density_test C V W f phi F
    hC hV hW hf hF ((heta.pow 2).mul hW) hcsq.mul_right he
  let R := fun x ↦ realMatrixEnergy C phi W x-phi x*V x*W x-Yau.pairing phi F x+phi x*f x
  have hR : Integrable R := ((hE.sub hP).sub hFint).add hfint
  have hRzero : (∫ x, R x)=0 := by
    dsimp [R]
    rw [integral_add (f := fun x ↦ realMatrixEnergy C phi W x-phi x*V x*W x-Yau.pairing phi F x)
        ((hE.sub hP).sub hFint) hfint,
      integral_sub (f := fun x ↦ realMatrixEnergy C phi W x-phi x*V x*W x) (hE.sub hP) hFint,
      integral_sub hE hP,hweak]
    ring
  have hpoint (x : Yau.Jets.Coord) : k/2*a x ≤ R x+D*(q x+r x+s x) := by
    by_cases hx : x ∈ tsupport eta
    · have hh := real_inhomogeneous_pointwise k L M hk hL hM (C x) (hs x)
        (fun z ↦ by simpa only [coordMatrixForm_apply] using hlo x hx z)
        (fun z ↦ by simpa only [coordMatrixForm_apply] using hhi x hx z)
        (eta x) (W x) (V x) (f x) (hpot x hx)
        (realCoordGradient W x) (realCoordGradient eta x) (F x)
      dsimp [R,phi]
      rw [realMatrixEnergy_cutoff C eta W heta hW x,real_pairing_cutoff eta W heta hW F x]
      exact hh
    · have hz : eta x=0 := image_eq_zero_of_notMem_tsupport hx
      have hd := realCoordGradient_zero_off_support eta hx
      have hdz (i : Fin 4) : Yau.coordPartial eta x i=0 := congrFun hd i
      simp [a,R,phi,q,r,s,hz,realGradientSquare,hdz,
        realMatrixEnergy_cutoff C eta W heta hW x,real_pairing_cutoff eta W heta hW F x]
  have hint := integral_mono (ha.const_mul (k/2)) (hR.add (((hq.add hr).add hsint).const_mul D)) hpoint
  change (∫ x, k/2*a x) ≤ ∫ x, R x+D*(q x+r x+s x) at hint
  rw [integral_const_mul,integral_add (g := fun x ↦ D*(q x+r x+s x)) hR (((hq.add hr).add hsint).const_mul D),
    integral_const_mul,integral_add (f := fun x ↦ q x+r x) (hq.add hr) hsint,integral_add hq hr,hRzero,zero_add] at hint
  refine ⟨ha,hq,hr,hsint,?_⟩
  change (∫ x, a x) ≤ (2/k)*D*((∫ x, q x)+(∫ x, r x)+(∫ x, s x))
  have hi : (2/k)*(k/2)=1 := by field_simp
  have hh := mul_le_mul_of_nonneg_left hint (show 0 ≤ 2/k by positivity)
  rw [← mul_assoc,hi,one_mul] at hh
  simpa only [mul_assoc] using hh

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_RealJetErrorExpansion
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

lemma realJetErrorSource_expansion (V W : Yau.Jets.Coord → ℝ)
    (hV : ContDiff ℝ ∞ V) (hW : ContDiff ℝ ∞ W) (ds : List (Fin 4)) :
    realJetErrorSource V W ds = fun x ↦
      -realJetProductSum V W (realJetErrorTerms [] ds) x := by
  induction ds with
  | nil => funext x; simp [realJetErrorSource,realJetErrorTerms,realJetProductSum]
  | cons l ds ih =>
    funext x
    rw [realJetErrorSource,ih,realJetProductSum_error_cons V W hV hW]
    simp only [List.nil_append,Yau.coordPartial,fderiv_fun_neg,_root_.neg_apply]
    ring

lemma realJetErrorFlux_expansion (C : Yau.Jets.Coord → Matrix (Fin 4) (Fin 4) ℝ)
    (W : Yau.Jets.Coord → ℝ) (hC : ∀ i j, ContDiff ℝ ∞ (fun x ↦ C x i j))
    (hW : ContDiff ℝ ∞ W) (ds : List (Fin 4)) :
    realJetErrorFlux C W ds = fun x i ↦
      -∑ j, realJetProductSum (fun y ↦ C y i j) W (realJetErrorTerms [j] ds) x := by
  induction ds with
  | nil => funext x i; simp [realJetErrorFlux,realJetErrorTerms,realJetProductSum]
  | cons l ds ih =>
    funext x i
    rw [realJetErrorFlux,ih]
    dsimp only
    have hn (H : Yau.Jets.Coord → ℝ) :
        Yau.coordPartial (fun y ↦ -H y) x l = -Yau.coordPartial H x l := by
      simp [Yau.coordPartial]
    rw [hn,Yau.real_coordPartial_sum _ (fun j ↦
      realJetProductSum_smooth _ W (hC i j) hW (realJetErrorTerms [j] ds))]
    simp_rw [realJetProductSum_error_cons _ W (hC i _) hW]
    simp only [List.singleton_append,Finset.sum_add_distrib,realDerivativeErrorFlux,
      partialJet,Yau.coordPartial]
    ring

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_RealJetErrorBound
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

lemma real_list_sum_square_bound {α : Type*} (ts : List α) (f : α → ℝ) (D : ℝ)
    (hf : ∀ t ∈ ts, (f t)^2 ≤ D) :
    (ts.map f).sum^2 ≤ (ts.length:ℝ)^2*D := by
  have hs : (ts.map f).sum = ∑ i : Fin ts.length, f (ts.get i) := by
    conv_lhs => rw [← List.ofFn_get ts]
    simp
  have hc := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun _i : Fin ts.length ↦ (1:ℝ)) (fun i ↦ f (ts.get i))
  simp only [one_mul,one_pow,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,
    mul_one] at hc
  have he : (∑ i : Fin ts.length, (f (ts.get i))^2) ≤ (ts.length:ℝ)*D := by
    calc
      _ ≤ ∑ _i : Fin ts.length, D := Finset.sum_le_sum (fun i _ ↦ hf _ (List.get_mem ..))
      _ = _ := by simp
  rw [hs]
  calc
    _ ≤ (ts.length:ℝ)*(∑ i : Fin ts.length, (f (ts.get i))^2) := hc
    _ ≤ (ts.length:ℝ)*((ts.length:ℝ)*D) :=
      mul_le_mul_of_nonneg_left he (Nat.cast_nonneg _)
    _ = _ := by ring

lemma realJetProductSum_square_bound (a W : Yau.Jets.Coord → ℝ)
    (n : ℕ) (B : ℝ) (hB : 0 ≤ B) (extra ds : List (Fin 4))
    (he : extra.length ≤ 1) (hd : ds.length ≤ n) (x : Yau.Jets.Coord)
    (ha : ∀ es : List (Fin 4), es.length ≤ n → |partialJet a es x| ≤ B) :
    (realJetProductSum a W (realJetErrorTerms extra ds) x)^2 ≤
      (3:ℝ)^(2*n)*B^2*realFiniteJetSquare W n x := by
  have hterm (t : List (Fin 4) × List (Fin 4)) (ht : t ∈ realJetErrorTerms extra ds) :
      (partialJet a t.1 x*partialJet W t.2 x)^2 ≤ B^2*realFiniteJetSquare W n x := by
    obtain ⟨haord,hword⟩ := realJetErrorTerms_orders extra ds he t ht
    have hca : (partialJet a t.1 x)^2 ≤ B^2 := by
      simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hB).mpr (ha t.1 (haord.trans hd))
    rw [mul_pow]
    exact mul_le_mul hca (partialJet_sq_le_realFiniteJetSquare W n t.2 (hword.trans hd) x)
      (sq_nonneg _) (sq_nonneg _)
  have hcount : ((realJetErrorTerms extra ds).length:ℝ) ≤ (3:ℝ)^n := by
    have hc : ((realJetErrorTerms extra ds).length:ℝ) ≤ (3:ℝ)^ds.length := by
      exact_mod_cast realJetErrorTerms_length extra ds
    exact hc.trans (by gcongr; norm_num)
  have hsq : ((realJetErrorTerms extra ds).length:ℝ)^2 ≤ (3:ℝ)^(2*n) := by
    calc
      _ ≤ ((3:ℝ)^n)^2 := by gcongr
      _ = _ := by rw [← pow_mul]; congr 1; omega
  exact (real_list_sum_square_bound (realJetErrorTerms extra ds)
    (fun t ↦ partialJet a t.1 x*partialJet W t.2 x)
    (B^2*realFiniteJetSquare W n x) hterm).trans (by
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hsq
        (mul_nonneg (sq_nonneg B) (realFiniteJetSquare_nonneg W n x)))

theorem real_jet_error_bound (n : ℕ) (B : ℝ) (hB : 0 ≤ B) :
    ∃ K > 0, ∀ (C : Yau.Jets.Coord → Matrix (Fin 4) (Fin 4) ℝ)
      (V W : Yau.Jets.Coord → ℝ),
      (∀ i j, ContDiff ℝ ∞ (fun x ↦ C x i j)) → ContDiff ℝ ∞ V → ContDiff ℝ ∞ W →
      ∀ (x : Yau.Jets.Coord) (ds : List (Fin 4)), ds.length ≤ n →
      (∀ es : List (Fin 4), es.length ≤ n →
        (∀ i j, |partialJet (fun y ↦ C y i j) es x| ≤ B) ∧ |partialJet V es x| ≤ B) →
      (realJetErrorSource V W ds x)^2 + (∑ i, (realJetErrorFlux C W ds x i)^2) ≤
        K*realFiniteJetSquare W n x := by
  refine ⟨65*(3:ℝ)^(2*n)*B^2+1,by positivity,?_⟩
  intro C V W hC hV hW x ds hd hb
  let D := (3:ℝ)^(2*n)*B^2*realFiniteJetSquare W n x
  have hs : (realJetErrorSource V W ds x)^2 ≤ D := by
    rw [realJetErrorSource_expansion V W hV hW]
    simpa only [neg_sq] using realJetProductSum_square_bound V W n B hB [] ds
      (by simp) hd x (fun es hes ↦ (hb es hes).2)
  have hr (i : Fin 4) : (realJetErrorFlux C W ds x i)^2 ≤ 16*D := by
    rw [realJetErrorFlux_expansion C W hC hW]
    simp only [neg_sq]
    have ht (j : Fin 4) :
        (realJetProductSum (fun y ↦ C y i j) W (realJetErrorTerms [j] ds) x)^2 ≤ D :=
      realJetProductSum_square_bound _ W n B hB [j] ds (by simp) hd x
        (fun es hes ↦ (hb es hes).1 i j)
    have hh := real_list_sum_square_bound (List.ofFn (fun j : Fin 4 ↦ j))
      (fun j ↦ realJetProductSum (fun y ↦ C y i j) W (realJetErrorTerms [j] ds) x)
      D (fun j _ ↦ ht j)
    simpa only [List.map_ofFn,List.sum_ofFn,List.length_ofFn,Function.comp_apply,
      Nat.cast_ofNat,show (4:ℝ)^2=16 from by norm_num] using hh
  have hf : (∑ i, (realJetErrorFlux C W ds x i)^2) ≤ 64*D := by
    calc
      _ ≤ ∑ _i : Fin 4, 16*D := Finset.sum_le_sum (fun i _ ↦ hr i)
      _ = _ := by simp <;> ring
  have hS := realFiniteJetSquare_nonneg W n x
  dsimp [D] at hs hf
  nlinarith only [hs,hf,hS]

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_RealNestedCutoffWeight
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open MeasureTheory
open scoped ContDiff
noncomputable section

lemma real_nested_cutoff_support (eta chi : Yau.Jets.Coord → ℝ)
    (h : ∀ x ∈ tsupport eta, chi x=1) : tsupport eta ⊆ tsupport chi := by
  intro x hx
  apply subset_tsupport chi
  change chi x≠0
  rw [h x hx]
  exact one_ne_zero

lemma real_nested_cutoff_weight (eta chi : Yau.Jets.Coord → ℝ)
    (heta : ContDiff ℝ ∞ eta) (hc : HasCompactSupport eta)
    (h : ∀ x ∈ tsupport eta, chi x=1) :
    ∃ D > 0, ∀ x, realCutoffWeight eta x ≤ D*chi x^2 := by
  obtain ⟨A,hA⟩ := hc.isCompact.exists_bound_of_continuousOn (realCutoffWeight_smooth eta heta).continuous.continuousOn
  refine ⟨|A|+1,by positivity,?_⟩
  intro x
  by_cases hx : x ∈ tsupport eta
  · have hb := (le_abs_self (realCutoffWeight eta x)).trans (by simpa only [Real.norm_eq_abs] using hA x hx)
    rw [h x hx,one_pow,mul_one]
    exact hb.trans ((le_abs_self A).trans (by linarith))
  · rw [realCutoffWeight_zero_off_support eta hx]
    positivity

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_RealInteriorJetEstimate
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Yau.Analysis MeasureTheory
open scoped ContDiff
noncomputable section

lemma real_cutoff_chain_support (eta : ℕ → Yau.Jets.Coord → ℝ)
    (hnest : ∀ j x, x ∈ tsupport (eta (j+1)) → eta j x=1) (n : ℕ) :
    tsupport (eta n) ⊆ tsupport (eta 0) := by
  induction n with
  | zero => exact Set.Subset.rfl
  | succ n ih =>
    exact (real_nested_cutoff_support (eta (n+1)) (eta n) (hnest n)).trans ih

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_RealBallCutoffChain
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Metric
open scoped ContDiff
noncomputable section

lemma realCutoffRadius_le (r R : ℝ) (hR : r < R) (n : ℕ) :
    realCutoffRadius r R n ≤ R := by
  have h : (R-r)/(2:ℝ)^n ≤ R-r :=
    div_le_self (sub_nonneg.mpr hR.le) (one_le_pow₀ (by norm_num))
  dsimp [realCutoffRadius] <;> linarith

theorem real_ball_cutoff_chain (y : Yau.Jets.Coord) (r R : ℝ) (hr : 0 < r) (hR : r < R) :
    ∃ eta : ℕ → Yau.Jets.Coord → ℝ,
      (∀ j, ContDiff ℝ ∞ (eta j)) ∧ (∀ j, HasCompactSupport (eta j)) ∧
      (∀ j x, 0 ≤ eta j x ∧ eta j x ≤ 1) ∧
      (∀ j, tsupport (eta j) ⊆ closedBall y R) ∧
      (∀ j x, x ∈ closedBall y r → eta j x=1) ∧
      (∀ j x, x ∈ tsupport (eta (j+1)) → eta j x=1) := by
  refine ⟨fun j ↦ realBallCutoff y r R hr hR j,?_,?_,?_,?_,?_,?_⟩
  · intro j; exact (realBallCutoff y r R hr hR j).contDiff
  · intro j; exact (realBallCutoff y r R hr hR j).hasCompactSupport
  · intro j x
    exact ⟨(realBallCutoff y r R hr hR j).nonneg,(realBallCutoff y r R hr hR j).le_one⟩
  · intro j
    rw [(realBallCutoff y r R hr hR j).tsupport_eq]
    exact closedBall_subset_closedBall (realCutoffRadius_le r R hR j)
  · intro j x hx
    apply (realBallCutoff y r R hr hR j).one_of_mem_closedBall
    exact closedBall_subset_closedBall (realCutoffRadius_gt r R hR (j+1)).le hx
  · intro j x hx
    apply (realBallCutoff y r R hr hR j).one_of_mem_closedBall
    rw [(realBallCutoff y r R hr hR (j+1)).tsupport_eq] at hx
    exact hx

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_RealCutoffBallIntegrals
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open MeasureTheory Metric
open scoped ContDiff
noncomputable section

lemma real_cutoff_inner_integral_le (eta H : Yau.Jets.Coord → ℝ)
    (heta : ContDiff ℝ ∞ eta) (hc : HasCompactSupport eta) (hH : Continuous H)
    (hpos : ∀ x, 0 ≤ H x) (y : Yau.Jets.Coord) (r : ℝ)
    (hone : ∀ x ∈ closedBall y r, eta x=1) :
    (∫ x in closedBall y r, H x) ≤ ∫ x, eta x^2*H x := by
  have hi := real_cutoff_square_integrable eta H heta hc hH
  calc
    _ = ∫ x in closedBall y r, eta x^2*H x := by
      apply setIntegral_congr_fun measurableSet_closedBall
      intro x hx
      dsimp only
      rw [hone x hx]; simp
    _ ≤ _ := setIntegral_le_integral hi
      (Filter.Eventually.of_forall (fun x ↦ mul_nonneg (sq_nonneg _) (hpos x)))

lemma real_cutoff_outer_integral_le (eta H : Yau.Jets.Coord → ℝ)
    (heta : ContDiff ℝ ∞ eta) (hc : HasCompactSupport eta) (hH : Continuous H)
    (hpos : ∀ x, 0 ≤ H x) (hval : ∀ x, 0 ≤ eta x ∧ eta x ≤ 1)
    (y : Yau.Jets.Coord) (R : ℝ) (hs : tsupport eta ⊆ closedBall y R) :
    (∫ x, eta x^2*H x) ≤ ∫ x in closedBall y R, H x := by
  have hi := real_cutoff_square_integrable eta H heta hc hH
  have hI := hH.continuousOn.integrableOn_compact (μ := volume) (isCompact_closedBall y R)
  calc
    _ = ∫ x in closedBall y R, eta x^2*H x := by
      symm
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro x hx
      have hz : eta x=0 := image_eq_zero_of_notMem_tsupport (fun h ↦ hx (hs h))
      rw [hz]; simp
    _ ≤ _ := setIntegral_mono_on hi.integrableOn hI measurableSet_closedBall (fun x _ ↦ by
      have hsq : eta x^2 ≤ 1 := by nlinarith [(hval x).1,(hval x).2]
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hsq (hpos x))

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_RealLocalCaccioppoli
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open MeasureTheory Set
open scoped ContDiff
noncomputable section

theorem real_local_inhomogeneous_caccioppoli (k L M : ℝ)
    (hk : 0 < k) (hL : 0 < L) (hM : 0 ≤ M) :
    ∃ K > 0, ∀ (C : Yau.Jets.Coord → Matrix (Fin 4) (Fin 4) ℝ)
      (V W f eta : Yau.Jets.Coord → ℝ) (F : Yau.Jets.Coord → Yau.Jets.Coord),
      (∀ i j, ContDiff ℝ ∞ (fun x ↦ C x i j)) → ContDiff ℝ ∞ V →
      ContDiff ℝ ∞ W → ContDiff ℝ ∞ f → ContDiff ℝ ∞ eta →
      (∀ i, ContDiff ℝ ∞ (fun x ↦ F x i)) → HasCompactSupport eta →
      (∀ x i j, C x i j=C x j i) →
      (∀ x ∈ tsupport eta, ∀ z : Yau.Jets.Coord,
        k*(∑ i, z i^2) ≤ ∑ i, ∑ j, z i*C x i j*z j) →
      (∀ x ∈ tsupport eta, ∀ z : Yau.Jets.Coord,
        (∑ i, ∑ j, z i*C x i j*z j) ≤ L*(∑ i, z i^2)) →
      (∀ x ∈ tsupport eta, |V x| ≤ M) →
      (∀ x ∈ tsupport eta,
        Yau.coordDiv (realMatrixFlux C W) x+V x*W x=Yau.coordDiv F x+f x) →
      Integrable (fun x ↦ eta x^2*realGradientSquare W x) ∧
      Integrable (fun x ↦ (eta x^2+realGradientSquare eta x)*W x^2) ∧
      Integrable (fun x ↦ eta x^2*f x^2) ∧
      Integrable (fun x ↦ eta x^2*(∑ i, F x i^2)) ∧
      (∫ x, eta x^2*realGradientSquare W x) ≤ K *
        ((∫ x, (eta x^2+realGradientSquare eta x)*W x^2)+
          (∫ x, eta x^2*f x^2)+(∫ x, eta x^2*(∑ i, F x i^2))) := by
  obtain ⟨K,hK,hbound⟩ := real_inhomogeneous_caccioppoli k L M hk hL hM
  refine ⟨K,hK,fun C V W f eta F hC hV hW hf heta hF hc hs hlo hhi hpot he ↦ ?_⟩
  let g := fun x ↦ Yau.coordDiv (realMatrixFlux C W) x+V x*W x-Yau.coordDiv F x
  have hg : ContDiff ℝ ∞ g :=
    ((ContDiff.sum (fun i _ ↦ Yau.real_coordPartial_smooth _ (realMatrixFlux_smooth C W hC hW i) i)).add
      (hV.mul hW)).sub (ContDiff.sum (fun i _ ↦ Yau.real_coordPartial_smooth _ (hF i) i))
  have h := hbound C V W g eta F hC hV hW hg heta hF hc hs hlo hhi hpot (fun x ↦ by dsimp [g] <;> ring)
  have hid : (fun x ↦ eta x^2*g x^2)=(fun x ↦ eta x^2*f x^2) := by
    funext x
    by_cases hx : x ∈ tsupport eta
    · have heq : g x=f x := by dsimp [g]; linarith only [he x hx]
      rw [heq]
    · rw [image_eq_zero_of_notMem_tsupport hx]
      simp
  rw [hid] at h
  exact h

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_RealLocalEquationDifferentiation
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Set Filter
open scoped ContDiff Topology
noncomputable section

theorem real_local_inhomogeneous_differentiation
    (O : Set Yau.Jets.Coord) (hO : IsOpen O)
    (C : Yau.Jets.Coord → Matrix (Fin 4) (Fin 4) ℝ)
    (V W f : Yau.Jets.Coord → ℝ) (F : Yau.Jets.Coord → Yau.Jets.Coord)
    (hC : ∀ i j, ContDiff ℝ ∞ (fun x ↦ C x i j))
    (hV : ContDiff ℝ ∞ V) (hW : ContDiff ℝ ∞ W) (hf : ContDiff ℝ ∞ f)
    (hF : ∀ i, ContDiff ℝ ∞ (fun x ↦ F x i))
    (he : ∀ x ∈ O, Yau.coordDiv (realMatrixFlux C W) x+V x*W x=Yau.coordDiv F x+f x)
    (k : Fin 4) :
    ∀ x ∈ O, Yau.coordDiv (realMatrixFlux C (fun y ↦ Yau.coordPartial W y k)) x+
      V x*Yau.coordPartial W x k =
      Yau.coordDiv (fun y i ↦ Yau.coordPartial (fun z ↦ F z i) y k-realDerivativeErrorFlux C W k y i) x+
        (Yau.coordPartial f x k-Yau.coordPartial V x k*W x) := by
  have hflux := realMatrixFlux_smooth C W hC hW
  have hdiv : ContDiff ℝ ∞ (Yau.coordDiv (realMatrixFlux C W)) :=
    ContDiff.sum (fun i _ ↦ Yau.real_coordPartial_smooth _ (hflux i) i)
  have hdivF : ContDiff ℝ ∞ (Yau.coordDiv F) :=
    ContDiff.sum (fun i _ ↦ Yau.real_coordPartial_smooth _ (hF i) i)
  intro x hx
  have heg : (fun y ↦ Yau.coordDiv (realMatrixFlux C W) y+V y*W y) =ᶠ[𝓝 x]
      (fun y ↦ Yau.coordDiv F y+f y) := by
    filter_upwards [hO.mem_nhds hx] with y hy
    exact he y hy
  have hd := congrArg (fun D : Yau.Jets.Coord →L[ℝ] ℝ ↦ D (Pi.single k 1))
    (heg.fderiv_eq (𝕜 := ℝ))
  change Yau.coordPartial (fun y ↦ Yau.coordDiv (realMatrixFlux C W) y+V y*W y) x k =
    Yau.coordPartial (fun y ↦ Yau.coordDiv F y+f y) x k at hd
  rw [Yau.real_coordPartial_add _ _ hdiv (hV.mul hW),Yau.real_coordPartial_mul _ _ hV hW,
    Yau.real_coordPartial_add _ _ hdivF hf,real_coordDiv_partial _ hflux,real_coordDiv_partial _ hF] at hd
  have hpart : (fun y i ↦ Yau.coordPartial (fun z ↦ realMatrixFlux C W z i) y k) =
      fun y i ↦ realDerivativeErrorFlux C W k y i+realMatrixFlux C (fun z ↦ Yau.coordPartial W z k) y i := by
    funext y i; exact realMatrixFlux_partial C W hC hW y i k
  rw [hpart,real_coordDiv_add _ _ (realDerivativeErrorFlux_smooth C W k hC hW)
    (realMatrixFlux_smooth C _ hC (Yau.real_coordPartial_smooth W hW k))] at hd
  rw [real_coordDiv_sub _ _ (fun i ↦ Yau.real_coordPartial_smooth _ (hF i) k)
    (realDerivativeErrorFlux_smooth C W k hC hW)]
  linarith only [hd]

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_RealLocalJetErrorEquation
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Set Yau.Analysis
open scoped ContDiff
noncomputable section

theorem real_local_jet_error_equation (O : Set Yau.Jets.Coord) (hO : IsOpen O)
    (C : Yau.Jets.Coord → Matrix (Fin 4) (Fin 4) ℝ)
    (V W : Yau.Jets.Coord → ℝ) (hC : ∀ i j, ContDiff ℝ ∞ (fun x ↦ C x i j))
    (hV : ContDiff ℝ ∞ V) (hW : ContDiff ℝ ∞ W)
    (he : ∀ x ∈ O, Yau.coordDiv (realMatrixFlux C W) x+V x*W x=0)
    (ds : List (Fin 4)) :
    ∀ x ∈ O, Yau.coordDiv (realMatrixFlux C (partialJet W ds)) x+V x*partialJet W ds x =
      Yau.coordDiv (realJetErrorFlux C W ds) x+realJetErrorSource V W ds x := by
  induction ds with
  | nil =>
    intro x hx
    simpa [partialJet,realJetErrorFlux,realJetErrorSource,Yau.coordDiv,Yau.coordPartial] using he x hx
  | cons l ds ih =>
    exact real_local_inhomogeneous_differentiation O hO C V (partialJet W ds) (realJetErrorSource V W ds)
      (realJetErrorFlux C W ds) hC hV (partialJet_smooth W hW ds)
      (realJetErrorSource_smooth V W hV hW ds) (realJetErrorFlux_smooth C W hC hW ds) ih l

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_RealLocalJetCutoffEstimate
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

theorem real_local_jet_cutoff_estimate (O : Set Yau.Jets.Coord) (hO : IsOpen O)
    (k L M : ℝ) (hk : 0 < k) (hL : 0 < L) (hM : 0 ≤ M) :
    ∃ K > 0, ∀ (C : Yau.Jets.Coord → Matrix (Fin 4) (Fin 4) ℝ)
      (V W eta : Yau.Jets.Coord → ℝ),
      (∀ i j, ContDiff ℝ ∞ (fun x ↦ C x i j)) → ContDiff ℝ ∞ V →
      ContDiff ℝ ∞ W → ContDiff ℝ ∞ eta → HasCompactSupport eta → tsupport eta ⊆ O →
      (∀ x i j, C x i j=C x j i) →
      (∀ x ∈ tsupport eta, ∀ z : Yau.Jets.Coord,
        k*(∑ i, z i^2) ≤ ∑ i, ∑ j, z i*C x i j*z j) →
      (∀ x ∈ tsupport eta, ∀ z : Yau.Jets.Coord,
        (∑ i, ∑ j, z i*C x i j*z j) ≤ L*(∑ i, z i^2)) →
      (∀ x ∈ tsupport eta, |V x| ≤ M) →
      (∀ x ∈ O, Yau.coordDiv (realMatrixFlux C W) x+V x*W x=0) →
      ∀ ds : List (Fin 4),
      Integrable (fun x ↦ eta x^2*realGradientSquare (partialJet W ds) x) ∧
      Integrable (fun x ↦ (eta x^2+realGradientSquare eta x)*(partialJet W ds x)^2) ∧
      Integrable (fun x ↦ eta x^2*(realJetErrorSource V W ds x)^2) ∧
      Integrable (fun x ↦ eta x^2*(∑ i, (realJetErrorFlux C W ds x i)^2)) ∧
      (∫ x, eta x^2*realGradientSquare (partialJet W ds) x) ≤ K *
        ((∫ x, (eta x^2+realGradientSquare eta x)*(partialJet W ds x)^2)+
          (∫ x, eta x^2*(realJetErrorSource V W ds x)^2)+
          (∫ x, eta x^2*(∑ i, (realJetErrorFlux C W ds x i)^2))) := by
  obtain ⟨K,hK,h⟩ := real_local_inhomogeneous_caccioppoli k L M hk hL hM
  refine ⟨K,hK,?_⟩
  intro C V W eta hC hV hW heta hc hsO hs hlo hhi hpot he ds
  exact h C V (partialJet W ds) (realJetErrorSource V W ds) eta (realJetErrorFlux C W ds)
    hC hV (partialJet_smooth W hW ds) (realJetErrorSource_smooth V W hV hW ds) heta
    (realJetErrorFlux_smooth C W hC hW ds) hc hs hlo hhi hpot
    (fun x hx ↦ real_local_jet_error_equation O hO C V W hC hV hW he ds x (hsO hx))

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_RealLocalJetClosedCutoff
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

theorem real_local_jet_closed_cutoff (O : Set Yau.Jets.Coord) (hO : IsOpen O)
    (n : ℕ) (k L M B : ℝ)
    (hk : 0 < k) (hL : 0 < L) (hM : 0 ≤ M) (hB : 0 ≤ B) :
    ∃ K > 0, ∀ (C : Yau.Jets.Coord → Matrix (Fin 4) (Fin 4) ℝ)
      (V W eta : Yau.Jets.Coord → ℝ),
      (∀ i j, ContDiff ℝ ∞ (fun x ↦ C x i j)) → ContDiff ℝ ∞ V →
      ContDiff ℝ ∞ W → ContDiff ℝ ∞ eta → HasCompactSupport eta → tsupport eta ⊆ O →
      (∀ x i j, C x i j=C x j i) →
      (∀ x ∈ tsupport eta, ∀ z : Yau.Jets.Coord,
        k*(∑ i, z i^2) ≤ ∑ i, ∑ j, z i*C x i j*z j) →
      (∀ x ∈ tsupport eta, ∀ z : Yau.Jets.Coord,
        (∑ i, ∑ j, z i*C x i j*z j) ≤ L*(∑ i, z i^2)) →
      (∀ x ∈ tsupport eta, |V x| ≤ M) →
      (∀ x ∈ tsupport eta, ∀ es : List (Fin 4), es.length ≤ n →
        (∀ i j, |partialJet (fun y ↦ C y i j) es x| ≤ B) ∧ |partialJet V es x| ≤ B) →
      (∀ x ∈ O, Yau.coordDiv (realMatrixFlux C W) x+V x*W x=0) →
      ∀ ds : List (Fin 4), ds.length ≤ n →
      Integrable (fun x ↦ eta x^2*realGradientSquare (partialJet W ds) x) ∧
      Integrable (fun x ↦ realCutoffWeight eta x*realFiniteJetSquare W n x) ∧
      (∫ x, eta x^2*realGradientSquare (partialJet W ds) x) ≤
        K*(∫ x, realCutoffWeight eta x*realFiniteJetSquare W n x) := by
  obtain ⟨K,hK,hcut⟩ := real_local_jet_cutoff_estimate O hO k L M hk hL hM
  obtain ⟨E,hE,herror⟩ := real_jet_error_bound n B hB
  refine ⟨K*(1+E),by positivity,?_⟩
  intro C V W eta hC hV hW heta hc hsO hs hlo hhi hpot hb he ds hd
  obtain ⟨hG,hI,hS,hF,hest⟩ := hcut C V W eta hC hV hW heta hc hsO hs hlo hhi hpot he ds
  have hJ := realCutoffWeight_integrable_mul eta _ heta hc (realFiniteJetSquare_smooth W hW n).continuous
  have hbase : (∫ x, (eta x^2+realGradientSquare eta x)*(partialJet W ds x)^2) ≤
      ∫ x, realCutoffWeight eta x*realFiniteJetSquare W n x := by
    apply integral_mono hI hJ
    intro x
    exact mul_le_mul_of_nonneg_left (partialJet_sq_le_realFiniteJetSquare W n ds hd x)
      (realCutoffWeight_nonneg eta x)
  have hpoint (x : Yau.Jets.Coord) :
      eta x^2*(realJetErrorSource V W ds x)^2 +
        eta x^2*(∑ i, (realJetErrorFlux C W ds x i)^2) ≤
      E*(realCutoffWeight eta x*realFiniteJetSquare W n x) := by
    by_cases hx : x ∈ tsupport eta
    · have herr := herror C V W hC hV hW x ds hd (hb x hx)
      have hm := mul_le_mul_of_nonneg_left herr (sq_nonneg (eta x))
      have hw : eta x^2 ≤ realCutoffWeight eta x :=
        le_add_of_nonneg_right (realGradientSquare_nonneg eta x)
      have hcomp := mul_le_mul_of_nonneg_right hw
        (mul_nonneg hE.le (realFiniteJetSquare_nonneg W n x))
      nlinarith only [hm,hcomp]
    · rw [image_eq_zero_of_notMem_tsupport hx,realCutoffWeight_zero_off_support eta hx]
      simp
  have herr := integral_mono (hS.add hF) (hJ.const_mul E) hpoint
  simp only [Pi.add_apply] at herr
  rw [integral_add hS hF,integral_const_mul] at herr
  refine ⟨hG,hJ,?_⟩
  have hh := mul_le_mul_of_nonneg_left (add_le_add hbase herr) hK.le
  nlinarith only [hest,hh]

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_RealLocalJetSuccessorCutoff
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

theorem real_local_jet_successor_cutoff (O : Set Yau.Jets.Coord) (hO : IsOpen O)
    (n : ℕ) (k L M B : ℝ)
    (hk : 0 < k) (hL : 0 < L) (hM : 0 ≤ M) (hB : 0 ≤ B) :
    ∃ K > 0, ∀ (C : Yau.Jets.Coord → Matrix (Fin 4) (Fin 4) ℝ)
      (V W eta : Yau.Jets.Coord → ℝ),
      (∀ i j, ContDiff ℝ ∞ (fun x ↦ C x i j)) → ContDiff ℝ ∞ V →
      ContDiff ℝ ∞ W → ContDiff ℝ ∞ eta → HasCompactSupport eta → tsupport eta ⊆ O →
      (∀ x i j, C x i j=C x j i) →
      (∀ x ∈ tsupport eta, ∀ z : Yau.Jets.Coord,
        k*(∑ i, z i^2) ≤ ∑ i, ∑ j, z i*C x i j*z j) →
      (∀ x ∈ tsupport eta, ∀ z : Yau.Jets.Coord,
        (∑ i, ∑ j, z i*C x i j*z j) ≤ L*(∑ i, z i^2)) →
      (∀ x ∈ tsupport eta, |V x| ≤ M) →
      (∀ x ∈ tsupport eta, ∀ es : List (Fin 4), es.length ≤ n →
        (∀ i j, |partialJet (fun y ↦ C y i j) es x| ≤ B) ∧ |partialJet V es x| ≤ B) →
      (∀ x ∈ O, Yau.coordDiv (realMatrixFlux C W) x+V x*W x=0) →
      Integrable (fun x ↦ eta x^2*realFiniteJetSquare W (n+1) x) ∧
      Integrable (fun x ↦ realCutoffWeight eta x*realFiniteJetSquare W n x) ∧
      (∫ x, eta x^2*realFiniteJetSquare W (n+1) x) ≤
        K*(∫ x, realCutoffWeight eta x*realFiniteJetSquare W n x) := by
  obtain ⟨K,hK,hcut⟩ := real_local_jet_closed_cutoff O hO n k L M B hk hL hM hB
  let N : ℝ := ∑ r ∈ Finset.range (n+2), (4:ℝ)^r
  have hN : 0 ≤ N := Finset.sum_nonneg (fun _ _ ↦ by positivity)
  refine ⟨N*(K+1)+1,by positivity,?_⟩
  intro C V W eta hC hV hW heta hc hsO hs hlo hhi hpot hb he
  let J : ℝ := ∫ x, realCutoffWeight eta x*realFiniteJetSquare W n x
  have hJ := realCutoffWeight_integrable_mul eta _ heta hc (realFiniteJetSquare_smooth W hW n).continuous
  have hJn : 0 ≤ J := integral_nonneg (fun x ↦
    mul_nonneg (realCutoffWeight_nonneg eta x) (realFiniteJetSquare_nonneg W n x))
  have hi (ds : List (Fin 4)) : Integrable (fun x ↦ eta x^2*(partialJet W ds x)^2) :=
    real_cutoff_square_integrable eta _ heta hc ((partialJet_smooth W hW ds).pow 2).continuous
  have hw (ds : List (Fin 4)) (hd : ds.length ≤ n+1) :
      (∫ x, eta x^2*(partialJet W ds x)^2) ≤ (K+1)*J := by
    cases ds with
    | nil =>
      have hp (x : Yau.Jets.Coord) : eta x^2*(partialJet W [] x)^2 ≤
          realCutoffWeight eta x*realFiniteJetSquare W n x :=
        mul_le_mul (le_add_of_nonneg_right (realGradientSquare_nonneg eta x))
          (partialJet_sq_le_realFiniteJetSquare W n [] (by simp) x) (sq_nonneg _)
          (realCutoffWeight_nonneg eta x)
      have hh := integral_mono (hi []) hJ hp
      change (∫ x, eta x^2*(partialJet W [] x)^2) ≤ J at hh
      nlinarith [mul_nonneg hK.le hJn]
    | cons l ds =>
      obtain ⟨hG,_,hest⟩ := hcut C V W eta hC hV hW heta hc hsO hs hlo hhi hpot hb he ds (by simpa using hd)
      have hh : (∫ x, eta x^2*(partialJet W (l::ds) x)^2) ≤
          ∫ x, eta x^2*realGradientSquare (partialJet W ds) x := by
        apply integral_mono (hi (l::ds)) hG
        intro x
        exact mul_le_mul_of_nonneg_left (real_partial_sq_le_gradient (partialJet W ds) x l) (sq_nonneg _)
      change (∫ x, eta x^2*realGradientSquare (partialJet W ds) x) ≤ K*J at hest
      nlinarith only [hh,hest,hJn]
  refine ⟨realFiniteJetSquare_integrable eta W heta hc hW _,hJ,?_⟩
  rw [realFiniteJetSquare_integral_sum eta W heta hc hW]
  have hh := Finset.sum_le_sum (s := Finset.range (n+2)) (fun r hr ↦
    Finset.sum_le_sum (s := Finset.univ) (fun w _ ↦ hw (List.ofFn w) (by
      simp only [List.length_ofFn]; exact Nat.le_of_lt_succ (Finset.mem_range.mp hr))))
  have hcN : (∑ r ∈ Finset.range (n+2), ∑ _w : Fin r → Fin 4, (K+1)*J) = N*((K+1)*J) := by
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fun,Fintype.card_fin,
      nsmul_eq_mul,Nat.cast_pow,Nat.cast_ofNat]
    exact (Finset.sum_mul ..).symm
  rw [hcN] at hh
  change (∑ r ∈ Finset.range (n+1+1), ∑ w : Fin r → Fin 4,
    ∫ x, eta x^2*(partialJet W (List.ofFn w) x)^2) ≤ (N*(K+1)+1)*J
  nlinarith only [hh,hJn]

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_RealLocalNestedJetCutoff
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

theorem real_local_nested_jet_cutoff (O : Set Yau.Jets.Coord) (hO : IsOpen O)
    (n : ℕ) (k L M B : ℝ)
    (hk : 0 < k) (hL : 0 < L) (hM : 0 ≤ M) (hB : 0 ≤ B)
    (eta chi : Yau.Jets.Coord → ℝ) (heta : ContDiff ℝ ∞ eta) (hchi : ContDiff ℝ ∞ chi)
    (hce : HasCompactSupport eta) (hcc : HasCompactSupport chi)
    (hnest : ∀ x ∈ tsupport eta, chi x=1) (hsO : tsupport eta ⊆ O) :
    ∃ K > 0, ∀ (C : Yau.Jets.Coord → Matrix (Fin 4) (Fin 4) ℝ)
      (V W : Yau.Jets.Coord → ℝ),
      (∀ i j, ContDiff ℝ ∞ (fun x ↦ C x i j)) → ContDiff ℝ ∞ V → ContDiff ℝ ∞ W →
      (∀ x i j, C x i j=C x j i) →
      (∀ x ∈ tsupport eta, ∀ z : Yau.Jets.Coord,
        k*(∑ i, z i^2) ≤ ∑ i, ∑ j, z i*C x i j*z j) →
      (∀ x ∈ tsupport eta, ∀ z : Yau.Jets.Coord,
        (∑ i, ∑ j, z i*C x i j*z j) ≤ L*(∑ i, z i^2)) →
      (∀ x ∈ tsupport eta, |V x| ≤ M) →
      (∀ x ∈ tsupport eta, ∀ es : List (Fin 4), es.length ≤ n →
        (∀ i j, |partialJet (fun y ↦ C y i j) es x| ≤ B) ∧ |partialJet V es x| ≤ B) →
      (∀ x ∈ O, Yau.coordDiv (realMatrixFlux C W) x+V x*W x=0) →
      Integrable (fun x ↦ eta x^2*realFiniteJetSquare W (n+1) x) ∧
      Integrable (fun x ↦ chi x^2*realFiniteJetSquare W n x) ∧
      (∫ x, eta x^2*realFiniteJetSquare W (n+1) x) ≤
        K*(∫ x, chi x^2*realFiniteJetSquare W n x) := by
  obtain ⟨K,hK,hcut⟩ := real_local_jet_successor_cutoff O hO n k L M B hk hL hM hB
  obtain ⟨D,hD,hweight⟩ := real_nested_cutoff_weight eta chi heta hce hnest
  refine ⟨K*D,by positivity,?_⟩
  intro C V W hC hV hW hs hlo hhi hpot hb he
  obtain ⟨hI,hJ,hest⟩ := hcut C V W eta hC hV hW heta hce hsO hs hlo hhi hpot hb he
  have hQ := realFiniteJetSquare_integrable chi W hchi hcc hW n
  have hm := integral_mono hJ (hQ.const_mul D) (fun x ↦ by
    have hh := mul_le_mul_of_nonneg_right (hweight x) (realFiniteJetSquare_nonneg W n x)
    simpa only [mul_assoc] using hh)
  rw [integral_const_mul] at hm
  refine ⟨hI,hQ,?_⟩
  have hh := mul_le_mul_of_nonneg_left hm hK.le
  nlinarith only [hest,hh]

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_RealLocalInteriorJetEstimate
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

theorem real_local_interior_jet_estimate (O : Set Yau.Jets.Coord) (hO : IsOpen O)
    (n : ℕ) (k L M B : ℝ)
    (hk : 0 < k) (hL : 0 < L) (hM : 0 ≤ M) (hB : 0 ≤ B)
    (eta : ℕ → Yau.Jets.Coord → ℝ) (heta : ∀ j, ContDiff ℝ ∞ (eta j))
    (hc : ∀ j, HasCompactSupport (eta j))
    (hnest : ∀ j x, x ∈ tsupport (eta (j+1)) → eta j x=1)
    (hsO : tsupport (eta 0) ⊆ O) :
    ∃ K > 0, ∀ (C : Yau.Jets.Coord → Matrix (Fin 4) (Fin 4) ℝ)
      (V W : Yau.Jets.Coord → ℝ),
      (∀ i j, ContDiff ℝ ∞ (fun x ↦ C x i j)) → ContDiff ℝ ∞ V → ContDiff ℝ ∞ W →
      (∀ x i j, C x i j=C x j i) →
      (∀ x ∈ tsupport (eta 0), ∀ z : Yau.Jets.Coord,
        k*(∑ i, z i^2) ≤ ∑ i, ∑ j, z i*C x i j*z j) →
      (∀ x ∈ tsupport (eta 0), ∀ z : Yau.Jets.Coord,
        (∑ i, ∑ j, z i*C x i j*z j) ≤ L*(∑ i, z i^2)) →
      (∀ x ∈ tsupport (eta 0), |V x| ≤ M) →
      (∀ x ∈ tsupport (eta 0), ∀ es : List (Fin 4), es.length ≤ n →
        (∀ i j, |partialJet (fun y ↦ C y i j) es x| ≤ B) ∧ |partialJet V es x| ≤ B) →
      (∀ x ∈ O, Yau.coordDiv (realMatrixFlux C W) x+V x*W x=0) →
      Integrable (fun x ↦ eta n x^2*realFiniteJetSquare W n x) ∧
      Integrable (fun x ↦ eta 0 x^2*W x^2) ∧
      (∫ x, eta n x^2*realFiniteJetSquare W n x) ≤
        K*(∫ x, eta 0 x^2*W x^2) := by
  induction n with
  | zero =>
    refine ⟨1,by norm_num,?_⟩
    intro C V W hC hV hW hs hlo hhi hpot hb he
    have hi := real_cutoff_square_integrable (eta 0) _ (heta 0) (hc 0) (hW.pow 2).continuous
    simpa only [realFiniteJetSquare_zero,one_mul] using And.intro hi (And.intro hi (le_refl (∫ x, eta 0 x^2*W x^2)))
  | succ n ih =>
    obtain ⟨K0,hK0,hprevious⟩ := ih
    obtain ⟨K1,hK1,hstep⟩ := real_local_nested_jet_cutoff O hO n k L M B hk hL hM hB
      (eta (n+1)) (eta n) (heta (n+1)) (heta n) (hc (n+1)) (hc n) (hnest n) ((real_cutoff_chain_support eta hnest (n+1)).trans hsO)
    refine ⟨K1*K0,by positivity,?_⟩
    intro C V W hC hV hW hs hlo hhi hpot hb he
    obtain ⟨_,hQ,hprev⟩ := hprevious C V W hC hV hW hs hlo hhi hpot
      (fun x hx es hes ↦ hb x hx es (by omega)) he
    have hsub := real_cutoff_chain_support eta hnest (n+1)
    obtain ⟨hI,_,hnext⟩ := hstep C V W hC hV hW hs
      (fun x hx ↦ hlo x (hsub hx)) (fun x hx ↦ hhi x (hsub hx))
      (fun x hx ↦ hpot x (hsub hx))
      (fun x hx es hes ↦ hb x (hsub hx) es (by omega)) he
    refine ⟨hI,hQ,?_⟩
    have hh := mul_le_mul_of_nonneg_left hprev hK1.le
    nlinarith only [hnext,hh]

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_RealLocalBallJetEstimate
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Yau.Analysis MeasureTheory Metric Set
open scoped ContDiff
noncomputable section

theorem real_local_ball_jet_estimate (O : Set Yau.Jets.Coord) (hO : IsOpen O)
    (n : ℕ) (k L M B : ℝ)
    (hk : 0 < k) (hL : 0 < L) (hM : 0 ≤ M) (hB : 0 ≤ B)
    (y : Yau.Jets.Coord) (r R : ℝ) (hr : 0 < r) (hR : r < R) (hsO : closedBall y R ⊆ O) :
    ∃ K > 0, ∀ (C : Yau.Jets.Coord → Matrix (Fin 4) (Fin 4) ℝ)
      (V W : Yau.Jets.Coord → ℝ),
      (∀ i j, ContDiff ℝ ∞ (fun x ↦ C x i j)) → ContDiff ℝ ∞ V → ContDiff ℝ ∞ W →
      (∀ x i j, C x i j=C x j i) →
      (∀ x ∈ closedBall y R, ∀ z : Yau.Jets.Coord,
        k*(∑ i, z i^2) ≤ ∑ i, ∑ j, z i*C x i j*z j) →
      (∀ x ∈ closedBall y R, ∀ z : Yau.Jets.Coord,
        (∑ i, ∑ j, z i*C x i j*z j) ≤ L*(∑ i, z i^2)) →
      (∀ x ∈ closedBall y R, |V x| ≤ M) →
      (∀ x ∈ closedBall y R, ∀ es : List (Fin 4), es.length ≤ n →
        (∀ i j, |partialJet (fun z ↦ C z i j) es x| ≤ B) ∧ |partialJet V es x| ≤ B) →
      (∀ x ∈ O, Yau.coordDiv (realMatrixFlux C W) x+V x*W x=0) →
      IntegrableOn (realFiniteJetSquare W n) (closedBall y r) ∧
      IntegrableOn (fun x ↦ W x^2) (closedBall y R) ∧
      (∫ x in closedBall y r, realFiniteJetSquare W n x) ≤
        K*(∫ x in closedBall y R, W x^2) := by
  obtain ⟨eta,heta,hc,hval,hsupport,hone,hnest⟩ := real_ball_cutoff_chain y r R hr hR
  obtain ⟨K,hK,hest⟩ := real_local_interior_jet_estimate O hO n k L M B hk hL hM hB eta heta hc hnest ((hsupport 0).trans hsO)
  refine ⟨K,hK,?_⟩
  intro C V W hC hV hW hs hlo hhi hpot hb he
  obtain ⟨_,_,hbound⟩ := hest C V W hC hV hW hs
    (fun x hx ↦ hlo x (hsupport 0 hx)) (fun x hx ↦ hhi x (hsupport 0 hx))
    (fun x hx ↦ hpot x (hsupport 0 hx)) (fun x hx ↦ hb x (hsupport 0 hx)) he
  have hinner := real_cutoff_inner_integral_le (eta n) _ (heta n) (hc n)
    (realFiniteJetSquare_smooth W hW n).continuous (realFiniteJetSquare_nonneg W n) y r (hone n)
  have houter := real_cutoff_outer_integral_le (eta 0) (fun x ↦ W x^2) (heta 0) (hc 0)
    (hW.pow 2).continuous (fun x ↦ sq_nonneg _) (hval 0) y R (hsupport 0)
  exact ⟨(realFiniteJetSquare_smooth W hW n).continuous.continuousOn.integrableOn_compact
      (isCompact_closedBall y r),
    (hW.pow 2).continuous.continuousOn.integrableOn_compact (isCompact_closedBall y R),
    hinner.trans (hbound.trans (mul_le_mul_of_nonneg_left houter hK.le))⟩

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Coefficients_RealCoefficientNeighborhoodEstimate
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open MeasureTheory Set Metric Yau.Analysis
open scoped ContDiff
noncomputable section

theorem real_coefficient_neighborhood_estimate (O : Set Yau.Jets.Coord) (hO : IsOpen O)
    (n : ℕ) (y : Yau.Jets.Coord) (r R : ℝ) (hr : 0 < r) (hR : r < R)
    (hsO : closedBall y R ⊆ O)
    (C₀ : Yau.Jets.Coord → Matrix (Fin 4) (Fin 4) ℝ) (V₀ : Yau.Jets.Coord → ℝ)
    (hC₀ : ∀ i j, ContDiff ℝ ∞ (fun x ↦ C₀ x i j)) (hV₀ : ContDiff ℝ ∞ V₀)
    (hp₀ : ∀ x ∈ closedBall y R, (C₀ x).PosDef) :
    ∃ eps > 0, ∃ K > 0,
      ∀ (C : Yau.Jets.Coord → Matrix (Fin 4) (Fin 4) ℝ) (V W : Yau.Jets.Coord → ℝ),
        (∀ i j, ContDiff ℝ ∞ (fun x ↦ C x i j)) → ContDiff ℝ ∞ V → ContDiff ℝ ∞ W →
        (∀ x i j, C x i j=C x j i) →
        (∀ x ∈ closedBall y R, ∀ es : List (Fin 4), es.length ≤ n →
          (∀ i j, |partialJet (fun z ↦ C z i j) es x-partialJet (fun z ↦ C₀ z i j) es x| ≤ eps) ∧
          |partialJet V es x-partialJet V₀ es x| ≤ eps) →
        (∀ x ∈ O, Yau.coordDiv (realMatrixFlux C W) x+V x*W x=0) →
        IntegrableOn (realFiniteJetSquare W n) (closedBall y r) ∧
        IntegrableOn (fun x ↦ W x^2) (closedBall y R) ∧
        (∫ x in closedBall y r, realFiniteJetSquare W n x) ≤
          K*(∫ x in closedBall y R, W x^2) := by
  have hQ := isCompact_closedBall y R
  obtain ⟨k,hk,L,hL,hellUnit⟩ := compact_parameter_matrix_ellipticity (T := Unit)
    (fun _ ↦ C₀) hQ
    (fun i j ↦ (hC₀ i j).continuous.comp (continuous_subtype_val.comp continuous_snd))
    (fun _ ↦ hp₀)
  have hell := hellUnit ()
  obtain ⟨BC,hBC,hCd⟩ := compact_parameter_finite_jet_bound (T := Unit) n
    (fun ij : Fin 4 × Fin 4 ↦ fun _ x ↦ C₀ x ij.1 ij.2) hQ
    (fun ij ds _ ↦ (partialJet_smooth _ (hC₀ ij.1 ij.2) ds).continuous.comp
      (continuous_subtype_val.comp continuous_snd))
  obtain ⟨BV,hBV,hVd⟩ := compact_parameter_finite_jet_bound (T := Unit) n
    (fun _ : Unit ↦ fun _ x ↦ V₀ x) hQ
    (fun _ ds _ ↦ (partialJet_smooth V₀ hV₀ ds).continuous.comp
      (continuous_subtype_val.comp continuous_snd))
  let eps := min (k/32) 1
  let B := BC+BV+1
  have heps : 0 < eps := lt_min (by positivity) (by norm_num)
  have hB : 0 ≤ B := by dsimp [B] <;> linarith
  obtain ⟨K,hK,hest⟩ := real_local_ball_jet_estimate O hO n (k/2) (L+k/2) B B
    (by positivity) (by positivity) hB hB y r R hr hR hsO
  refine ⟨eps,heps,K,hK,fun C V W hC hV hW hs hclose he ↦ ?_⟩
  have hentry : ∀ x ∈ closedBall y R, ∀ i j, |C x i j-C₀ x i j| ≤ k/32 := by
    intro x hx i j
    exact ((hclose x hx [] (by simp)).1 i j).trans (min_le_left _ _)
  have hellC := real_ellipticity_neighborhood (closedBall y R) C₀ k L hk
    (fun x hx z ↦ (hell x hx z).1) (fun x hx z ↦ (hell x hx z).2) C hentry
  have hbounds : ∀ x ∈ closedBall y R, ∀ es : List (Fin 4), es.length ≤ n →
      (∀ i j, |partialJet (fun z ↦ C z i j) es x| ≤ B) ∧ |partialJet V es x| ≤ B := by
    intro x hx es hes
    have hdelta := hclose x hx es hes
    constructor
    · intro i j
      have hbase := hCd (i,j) () x hx es hes
      have htri := abs_add_le (partialJet (fun z ↦ C z i j) es x-partialJet (fun z ↦ C₀ z i j) es x)
        (partialJet (fun z ↦ C₀ z i j) es x)
      rw [sub_add_cancel] at htri
      have hsmall := (hdelta.1 i j).trans (min_le_right _ _)
      dsimp only [B]
      linarith
    · have hbase := hVd () () x hx es hes
      have htri := abs_add_le (partialJet V es x-partialJet V₀ es x) (partialJet V₀ es x)
      rw [sub_add_cancel] at htri
      have hsmall := hdelta.2.trans (min_le_right _ _)
      dsimp only [B]
      linarith
  exact hest C V W hC hV hW hs (fun x hx z ↦ (hellC x hx z).1)
    (fun x hx z ↦ (hellC x hx z).2) (fun x hx ↦ (hbounds x hx [] (by simp)).2) hbounds he

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Coefficients_RealCoefficientNeighborhoodPointwise
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open MeasureTheory Set Metric Yau.Analysis
open scoped ContDiff
noncomputable section

theorem real_coefficient_neighborhood_pointwise (O : Set Yau.Jets.Coord) (hO : IsOpen O)
    (n : ℕ) (y : Yau.Jets.Coord) (r R : ℝ) (hr : 0 < r) (hR : r < R)
    (hsO : closedBall y R ⊆ O)
    (C₀ : Yau.Jets.Coord → Matrix (Fin 4) (Fin 4) ℝ) (V₀ : Yau.Jets.Coord → ℝ)
    (hC₀ : ∀ i j, ContDiff ℝ ∞ (fun x ↦ C₀ x i j)) (hV₀ : ContDiff ℝ ∞ V₀)
    (hp₀ : ∀ x ∈ closedBall y R, (C₀ x).PosDef) :
    ∃ eps > 0, ∃ K > 0,
      ∀ (C : Yau.Jets.Coord → Matrix (Fin 4) (Fin 4) ℝ) (V W : Yau.Jets.Coord → ℝ),
        (∀ i j, ContDiff ℝ ∞ (fun x ↦ C x i j)) → ContDiff ℝ ∞ V → ContDiff ℝ ∞ W →
        (∀ x i j, C x i j=C x j i) →
        (∀ x ∈ closedBall y R, ∀ es : List (Fin 4), es.length ≤ n+5 →
          (∀ i j, |partialJet (fun z ↦ C z i j) es x-partialJet (fun z ↦ C₀ z i j) es x| ≤ eps) ∧
          |partialJet V es x-partialJet V₀ es x| ≤ eps) →
        (∀ x ∈ O, Yau.coordDiv (realMatrixFlux C W) x+V x*W x=0) →
        ∀ ds : List (Fin 4), ds.length ≤ n → ∀ x ∈ closedBall y r,
          (partialJet W ds x)^2 ≤ K*(∫ z in closedBall y R, W z^2) := by
  let t := (r+R)/2
  have hrt : r < t := by dsimp [t] <;> linarith
  have htR : t < R := by dsimp [t] <;> linarith
  obtain ⟨eps,heps,L,hL,hest⟩ := real_coefficient_neighborhood_estimate O hO
    (n+5) y t R (hr.trans hrt) htR hsO C₀ V₀ hC₀ hV₀ hp₀
  have hinner : closedBall y r ⊆ interior (closedBall y t) :=
    (closedBall_subset_ball hrt).trans ball_subset_interior_closedBall
  obtain ⟨A,hA,ha⟩ := real_compact_interior_pointwise (isCompact_closedBall y r)
    (isCompact_closedBall y t) hinner n
  refine ⟨eps,heps,A*L,mul_pos hA hL,fun C V W hC hV hW hs hclose he ds hd x hx ↦ ?_⟩
  have hb := (hest C V W hC hV hW hs hclose he).2.2
  calc
    _ ≤ A*(∫ z in closedBall y t, realFiniteJetSquare W (n+5) z) := ha W hW ds hd x hx
    _ ≤ A*(L*(∫ z in closedBall y R, W z^2)) := mul_le_mul_of_nonneg_left hb hA.le
    _ = _ := by ring

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Spectral_SphereEigenNeighborhoodPointwise
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open MeasureTheory Set Metric Yau.Geometry Yau.Analysis
open scoped ContDiff
noncomputable section

theorem sphere_eigen_neighborhood_pointwise (d₀ : SphereEnergyData) (p : Base)
    (hrho₀ : ContDiff ℝ ∞ (fun x ↦ d₀.density (sphereChartCoordMap p x)))
    (mu₀ : ℝ) (n : ℕ) (y : Yau.Jets.Coord) (r R : ℝ) (hr : 0 < r) (hR : r < R)
    (hRO : closedBall y R ⊆ interior (Yau.realCenteredCube 4 (1/64))) :
    ∃ eps > 0, ∃ K > 0, ∀ (d : SphereEnergyData) (mu : ℝ),
      ContDiff ℝ ∞ (fun x ↦ d.density (sphereChartCoordMap p x)) → mu ≠ 0 →
      (∀ x ∈ closedBall y R, ∀ es : List (Fin 4), es.length ≤ n+5 →
        (∀ i j, |partialJet (fun z ↦ sphereChartPrincipalDensity d p z i j) es x-
          partialJet (fun z ↦ sphereChartPrincipalDensity d₀ p z i j) es x| ≤ eps) ∧
        |partialJet (sphereEigenForcingCoefficient d p mu) es x-
          partialJet (sphereEigenForcingCoefficient d₀ p mu₀) es x| ≤ eps) →
      (∀ x ∈ closedBall y R, |roundCoordDensity x*d.density (sphereChartCoordMap p x)-
        roundCoordDensity x*d₀.density (sphereChartCoordMap p x)| ≤ eps) →
      ∀ f : SphereWeightedL2 d, sphereL2Resolvent d f=mu • f →
      ∀ v : Yau.Jets.Coord → ℝ, ContDiff ℝ ∞ v →
        v =ᵐ[volume.restrict (Yau.realCenteredCube 4 (1/32))]
          (fun x ↦ f (sphereChartCoordMap p x)) →
        ∀ ds : List (Fin 4), ds.length ≤ n → ∀ x ∈ closedBall y r,
          (partialJet v ds x)^2 ≤ K*‖f‖^2 := by
  have hB₀ : ContDiff ℝ ∞ (sphereEigenForcingCoefficient d₀ p mu₀) :=
    contDiff_const.mul (roundCoordDensity_smooth.mul hrho₀)
  obtain ⟨eps₁,heps₁,A,hA,ha⟩ := real_coefficient_neighborhood_pointwise
    (interior (Yau.realCenteredCube 4 (1/64))) isOpen_interior n y r R hr hR hRO
    (sphereChartPrincipalDensity d₀ p) (sphereEigenForcingCoefficient d₀ p mu₀)
    (sphereChartPrincipalDensity_smooth d₀ p) hB₀
    (fun x _ ↦ (intrinsicRealPrincipal_posDef d₀.tensor d₀.symm d₀.pos p x).smul
      (roundCoordDensity_pos x))
  obtain ⟨eps₂,heps₂,B,hB,hb⟩ := sphereWeightedL2_chart_neighborhood d₀ p (isCompact_closedBall y R)
  refine ⟨min eps₁ eps₂,lt_min heps₁ heps₂,A*B,mul_pos hA hB,
    fun d mu hrho hmu hclose hrclose f heigen v hv hvf ds hd x hx ↦ ?_⟩
  have hBv : ContDiff ℝ ∞ (sphereEigenForcingCoefficient d p mu) :=
    contDiff_const.mul (roundCoordDensity_smooth.mul hrho)
  have hpoint := ha (sphereChartPrincipalDensity d p) (sphereEigenForcingCoefficient d p mu) v
    (sphereChartPrincipalDensity_smooth d p) hBv hv (sphereChartPrincipalDensity_symmetric d p)
    (fun x hx es hes ↦ ⟨fun i j ↦ ((hclose x hx es hes).1 i j).trans (min_le_left _ _),
      (hclose x hx es hes).2.trans (min_le_left _ _)⟩)
    (sphere_eigen_direct_matrix_equation d p hrho mu hmu f heigen v hv hvf) ds hd x hx
  have hsize := (hb d (fun x hx ↦ (hrclose x hx).trans (min_le_right _ _)) f).2
  have hQ : closedBall y R ⊆ Yau.realCenteredCube 4 (1/32) :=
    hRO.trans (interior_subset.trans (Yau.realCenteredCube_mono (by norm_num)))
  have heq : v =ᵐ[volume.restrict (closedBall y R)]
      (fun x ↦ f (sphereChartCoordMap p x)) := ae_mono (Measure.restrict_mono hQ le_rfl) hvf
  have hi : (∫ z in closedBall y R, v z^2) =
      ∫ z in closedBall y R, (f (sphereChartCoordMap p z))^2 :=
    integral_congr_ae (heq.fun_comp (fun a : ℝ ↦ a^2))
  rw [hi] at hpoint
  exact hpoint.trans ((mul_le_mul_of_nonneg_left hsize hA.le).trans_eq (by ring))

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Charts_SphereFiniteNeighborhoodBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open MeasureTheory Manifold Set Metric Yau.Geometry Yau.Analysis
open scoped ContDiff
noncomputable section

theorem finite_positive_common_lower_bound {I : Type*} [Fintype I]
    (e : I → ℝ) (he : ∀ i, 0 < e i) : ∃ eps > 0, ∀ i, eps ≤ e i := by
  classical
  have h : ∀ P : Finset I, ∃ eps > 0, ∀ i ∈ P, eps ≤ e i := by
    intro P
    induction P using Finset.induction_on with
    | empty => exact ⟨1,by norm_num,by simp⟩
    | @insert i P hi ih =>
      obtain ⟨eps,heps,hsmall⟩ := ih
      refine ⟨min (e i) eps,lt_min (he i) heps,?_⟩
      intro j hj
      rcases Finset.mem_insert.mp hj with rfl | hj
      · exact min_le_left _ _
      · exact (min_le_right _ _).trans (hsmall j hj)
  obtain ⟨eps,heps,hs⟩ := h Finset.univ
  exact ⟨eps,heps,fun i ↦ hs i (Finset.mem_univ i)⟩

local instance sphereFiniteBoundsMeasurable_r6a81dc_1 : MeasurableSpace Base := borel Base
local instance sphereFiniteBoundsBorel_r6a81dc_1 : BorelSpace Base := ⟨rfl⟩
theorem sphere_finite_neighborhood_bounds (d₀ : SphereEnergyData) (P : Finset Base)
    (hrho₀ : ∀ p : Base, ContDiff ℝ ∞ (fun x ↦ d₀.density (sphereChartCoordMap p x)))
    (mu₀ : ℝ) (n : ℕ) (r R : ℝ) (hr : 0 < r) (hR : r < R)
    (hRO : closedBall (0 : Yau.Jets.Coord) R ⊆ interior (Yau.realCenteredCube 4 (1/64))) :
    ∃ eps > 0, ∃ B : {p // p ∈ P} → ℝ, (∀ p, 0 ≤ B p) ∧
      ∀ (d : SphereEnergyData) (mu : ℝ),
        (∀ p : Base, ContDiff ℝ ∞ (fun x ↦ d.density (sphereChartCoordMap p x))) → mu ≠ 0 →
        (∀ p ∈ P, ∀ x ∈ closedBall (0 : Yau.Jets.Coord) R,
          ∀ es : List (Fin 4), es.length ≤ n+5 →
            (∀ a b, |partialJet (fun z ↦ sphereChartPrincipalDensity d p z a b) es x-
              partialJet (fun z ↦ sphereChartPrincipalDensity d₀ p z a b) es x| ≤ eps) ∧
            |partialJet (sphereEigenForcingCoefficient d p mu) es x-
              partialJet (sphereEigenForcingCoefficient d₀ p mu₀) es x| ≤ eps) →
        (∀ p ∈ P, ∀ x ∈ closedBall (0 : Yau.Jets.Coord) R,
          |roundCoordDensity x*d.density (sphereChartCoordMap p x)-
            roundCoordDensity x*d₀.density (sphereChartCoordMap p x)| ≤ eps) →
        ∀ f : SphereWeightedL2 d, sphereL2Resolvent d f=mu • f → ‖f‖=1 →
        ∀ u : Base → ℝ, ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ u →
          u =ᵐ[sphereWeightedMeasure d.density] (f : Base → ℝ) →
          ∀ (p : {p // p ∈ P}) (ds : List (Fin 4)), ds.length ≤ n →
            ∀ x ∈ closedBall (0 : Yau.Jets.Coord) r,
              |partialJet (u ∘ sphereChartCoordMap p.val) ds x| ≤ B p := by
  classical
  choose e he K hK hb using (fun p : {p // p ∈ P} ↦
    sphere_eigen_neighborhood_pointwise d₀ p.val (hrho₀ p.val) mu₀ n 0 r R hr hR hRO)
  obtain ⟨eps,heps,hsmall⟩ := finite_positive_common_lower_bound e he
  refine ⟨eps,heps,(fun p ↦ Real.sqrt (K p)),(fun p ↦ Real.sqrt_nonneg _),?_⟩
  intro d mu hrho hmu hclose hrclose f heigen hn u hu ha p ds hd x hx
  have hachart : (u ∘ sphereChartCoordMap p.val) =ᵐ[
      volume.restrict (Yau.realCenteredCube 4 (1/32))]
        (fun x ↦ f (sphereChartCoordMap p.val x)) :=
    ae_restrict_of_ae ((sphereWeightedMeasure_ae_chart_iff d p.val _).mp ha)
  have hb' := hb p d mu (hrho p.val) hmu (by
    intro x hx es hes
    exact ⟨fun a b ↦ ((hclose p.val p.property x hx es hes).1 a b).trans (hsmall p),
      (hclose p.val p.property x hx es hes).2.trans (hsmall p)⟩)
    (fun x hx ↦ (hrclose p.val p.property x hx).trans (hsmall p)) f heigen
    (u ∘ sphereChartCoordMap p.val) ((hu.comp (sphereChartCoordMap_smooth p.val)).contDiff)
    hachart ds hd x hx
  rw [hn,one_pow,mul_one] at hb'
  simpa only [Real.sqrt_sq_eq_abs] using Real.sqrt_le_sqrt hb'

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Charts_SphereWeightedPairingLimit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Set Filter MeasureTheory
open scoped Topology
noncomputable section

attribute [local instance] OAI.Yau.Target.sphereWeightedPairingLimitMeasurable
local instance sphereWeightedPairingLimitBorel_r6a81dc_1 : BorelSpace Base := ⟨rfl⟩
lemma sphere_uniform_eventual_bound (w : ℕ → Base → ℝ) (v : Base → ℝ)
    (hv : Continuous v) (ht : TendstoUniformly w v atTop) :
    ∃ B > 0, ∀ᶠ j in atTop, ∀ x, |w j x| ≤ B := by
  obtain ⟨C,hC⟩ := isCompact_univ.exists_bound_of_continuousOn hv.continuousOn
  refine ⟨max 0 C+1,by positivity,?_⟩
  filter_upwards [Metric.tendstoUniformly_iff.mp ht 1 (by norm_num)] with j hj x
  have hb : |v x| ≤ max 0 C := by
    have hb' : |v x| ≤ C := by simpa only [Real.norm_eq_abs] using hC x (mem_univ x)
    exact hb'.trans (le_max_right _ _)
  have hd : |v x-w j x| < 1 := by simpa only [Real.dist_eq] using hj x
  have hvb := abs_le.mp hb
  have hdb := abs_lt.mp hd
  exact abs_le.mpr ⟨by linarith,by linarith⟩

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Charts_SphereUniformDensityPairingLimit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Set Filter MeasureTheory
open scoped Topology
noncomputable section
attribute [local instance] OAI.Yau.Target.sphereUniformDensityMeasurable
local instance sphereUniformDensityBorel : BorelSpace Base := ⟨rfl⟩

theorem sphereWeightedPairing_uniform_density_limit
    (rho : ℕ → Base → ℝ) (rho₀ : Base → ℝ)
    (hr : ∀ j, Continuous (rho j)) (hr₀ : Continuous rho₀)
    (htr : TendstoUniformly rho rho₀ atTop)
    (w1 w2 : ℕ → Base → ℝ) (v1 v2 : Base → ℝ)
    (hw1 : ∀ j, Continuous (w1 j)) (hw2 : ∀ j, Continuous (w2 j))
    (hv1 : Continuous v1) (hv2 : Continuous v2)
    (hc1 : TendstoUniformly w1 v1 atTop) (hc2 : TendstoUniformly w2 v2 atTop) :
    Tendsto (fun j ↦ sphereWeightedPairing (rho j) (w1 j) (w2 j)) atTop
      (𝓝 (sphereWeightedPairing rho₀ v1 v2)) := by
  let := sphereReferenceMeasure_finite
  obtain ⟨R,hR,hbR⟩ := sphere_uniform_eventual_bound rho rho₀ hr₀ htr
  obtain ⟨B1,hB1,hb1⟩ := sphere_uniform_eventual_bound w1 v1 hv1 hc1
  obtain ⟨B2,hB2,hb2⟩ := sphere_uniform_eventual_bound w2 v2 hv2 hc2
  apply tendsto_integral_filter_of_norm_le_const
  · exact Eventually.of_forall (fun j ↦ (((hr j).mul (hw1 j)).mul (hw2 j)).aestronglyMeasurable)
  · refine ⟨R*B1*B2,?_⟩
    filter_upwards [hbR,hb1,hb2] with j hjR hj1 hj2
    exact Eventually.of_forall (fun x ↦ by
      rw [norm_mul,norm_mul]
      exact mul_le_mul (mul_le_mul (hjR x) (hj1 x) (norm_nonneg _) hR.le)
        (hj2 x) (norm_nonneg _) (mul_nonneg hR.le hB1.le))
  · exact Eventually.of_forall (fun x ↦
      ((htr.tendsto_at x).mul (hc1.tendsto_at x)).mul (hc2.tendsto_at x))

theorem sphere_uniform_limit_normalized
    (rho : ℕ → Base → ℝ) (rho₀ : Base → ℝ)
    (hr : ∀ j, Continuous (rho j)) (hr₀ : Continuous rho₀)
    (htr : TendstoUniformly rho rho₀ atTop)
    (w : ℕ → Base → ℝ) (v : Base → ℝ)
    (hw : ∀ j, Continuous (w j)) (hv : Continuous v)
    (hc : TendstoUniformly w v atTop)
    (hn : ∀ j, sphereWeightedPairing (rho j) (w j) (w j)=1) :
    sphereWeightedPairing rho₀ v v=1 ∧ v ≠ 0 := by
  have ht := sphereWeightedPairing_uniform_density_limit rho rho₀ hr hr₀ htr
    w w v v hw hw hv hv hc hc
  have he : sphereWeightedPairing rho₀ v v=1 := by
    simp only [hn] at ht
    exact tendsto_nhds_unique ht tendsto_const_nhds
  refine ⟨he,?_⟩
  intro hz
  simp only [hz,sphereWeightedPairing,Pi.zero_apply,mul_zero,integral_zero] at he
  norm_num at he

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Charts_SphereGlobalNeighborhoodCompactness
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open MeasureTheory Manifold Set Metric Filter Yau.Geometry Yau.Analysis
open scoped ContDiff Topology
noncomputable section

local instance sphereGlobalCompactMeasurable_r6a81dc_1 : MeasurableSpace Base := borel Base
local instance sphereGlobalCompactBorel_r6a81dc_1 : BorelSpace Base := ⟨rfl⟩
theorem sphere_eigen_global_neighborhood_compactness_oai (d₀ : SphereEnergyData)
    (hrho₀ : ∀ p : Base, ContDiff ℝ ∞ (fun x ↦ d₀.density (sphereChartCoordMap p x)))
    (mu₀ : ℝ) (n : ℕ) :
    ∃ P : Finset Base,
      (∀ x : Base, ∃ p ∈ P, ∃ z ∈ ball (0 : Yau.Jets.Coord) (1/512),
        sphereChartCoordMap p z=x) ∧
      ∃ eps > 0, ∀ (d : ℕ → SphereEnergyData) (mu : ℕ → ℝ),
        (∀ j p, ContDiff ℝ ∞ (fun x ↦ (d j).density (sphereChartCoordMap p x))) →
        (∀ j, mu j ≠ 0) →
        (∀ j p, p ∈ P → ∀ x ∈ closedBall (0 : Yau.Jets.Coord) (1/128),
          ∀ es : List (Fin 4), es.length ≤ n+6 →
            (∀ a b, |partialJet (fun z ↦ sphereChartPrincipalDensity (d j) p z a b) es x-
              partialJet (fun z ↦ sphereChartPrincipalDensity d₀ p z a b) es x| ≤ eps) ∧
            |partialJet (sphereEigenForcingCoefficient (d j) p (mu j)) es x-
              partialJet (sphereEigenForcingCoefficient d₀ p mu₀) es x| ≤ eps) →
        (∀ j p, p ∈ P → ∀ x ∈ closedBall (0 : Yau.Jets.Coord) (1/128),
          |roundCoordDensity x*(d j).density (sphereChartCoordMap p x)-
            roundCoordDensity x*d₀.density (sphereChartCoordMap p x)| ≤ eps) →
        ∀ f : ∀ j, SphereWeightedL2 (d j),
          (∀ j, sphereL2Resolvent (d j) (f j)=mu j • f j) → (∀ j, ‖f j‖=1) →
        ∃ u : ℕ → Base → ℝ,
          (∀ j, ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ (u j)) ∧
          (∀ j, u j =ᵐ[sphereWeightedMeasure (d j).density] (f j : Base → ℝ)) ∧
          (∀ j, sphereWeightedPairing (d j).density (u j) (u j)=1) ∧
          (∀ j, u j ≠ 0) ∧
          ∃ v : Base → ℝ, ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) n v ∧
            ∃ nu : ℕ → ℕ, StrictMono nu ∧ TendstoUniformly (fun j ↦ u (nu j)) v atTop ∧
              (∀ p ∈ P, ∀ ds : List (Fin 4), ds.length ≤ n →
                TendstoUniformlyOn (fun j ↦ partialJet (u (nu j) ∘ sphereChartCoordMap p) ds)
                  (partialJet (v ∘ sphereChartCoordMap p) ds) atTop (ball 0 (1/256))) ∧
              (TendstoUniformly (fun j ↦ (d j).density) d₀.density atTop →
                sphereWeightedPairing d₀.density v v=1 ∧ v ≠ 0) := by
  classical
  obtain ⟨P,hP⟩ := finite_sphere_coordinate_cover_radius (1/512) (by norm_num)
  obtain ⟨eps,heps,B,hB,hbound⟩ := sphere_finite_neighborhood_bounds d₀ P hrho₀ mu₀
    (n+1) (1/256) (1/128) (by norm_num) (by norm_num)
    (Yau.real_closedBall_subset_cube_interior (by norm_num))
  refine ⟨P,hP,eps,heps,?_⟩
  intro d mu hrho hmu hclose hrclose f heigen hn
  choose u hu ha huN hu0 hue using (fun j ↦
    sphere_eigen_global_normalized (d j) (hrho j) (mu j) (hmu j) (f j) (heigen j) (hn j))
  have hb : ∀ (p : {p // p ∈ P}) j (ds : List (Fin 4)), ds.length ≤ n+1 →
      ∀ x ∈ closedBall (0 : Yau.Jets.Coord) (1/256),
        |partialJet (u j ∘ sphereChartCoordMap p.val) ds x| ≤ B p := by
    intro p j ds hd x hx
    exact hbound (d j) (mu j) (hrho j) (hmu j)
      (fun p hp x hx es hes ↦ hclose j p hp x hx es (by omega)) (hrclose j)
      (f j) (heigen j) (hn j) (u j) (hu j) (ha j) p ds hd x hx
  obtain ⟨v,hv,nu,hnu,ht,hjet⟩ := sphere_finite_jet_compactness P (1/512) (1/256)
    (by norm_num) n hP u hu B hB hb
  refine ⟨u,hu,ha,huN,hu0,v,hv,nu,hnu,ht,hjet,?_⟩
  intro htr
  exact sphere_uniform_limit_normalized (fun j ↦ (d (nu j)).density) d₀.density
    (fun j ↦ (d (nu j)).continuous) d₀.continuous
    (tendstoUniformly_iff_seq_tendstoUniformly.mp htr nu hnu.tendsto_atTop) (fun j ↦ u (nu j)) v
    (fun j ↦ (hu (nu j)).continuous) hv.continuous ht (fun j ↦ huN (nu j))

end
end Yau.Target

end OAI
end

theorem solution : type_of% @OAI.Yau.Target.sphere_eigen_global_neighborhood_compactness_oai := @OAI.Yau.Target.sphere_eigen_global_neighborhood_compactness_oai
