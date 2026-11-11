-- Prove2me | solution 1 for OAI.Yau.Target.sphere_finite_norm_simple_oriented_persistence
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T00:34:54.389315+00:00
-- url     : https://prove2.me/submissions/45e424ab-dadd-4169-9530-c942f3763ebd

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
import Mathlib.Analysis.InnerProductSpace.Harmonic.Basic
import Mathlib.Analysis.InnerProductSpace.Laplacian
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Analysis.InnerProductSpace.Spectrum
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
import Mathlib.Data.Fin.Tuple.Basic
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
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.ContDiff
import Mathlib.MeasureTheory.Integral.IntervalIntegral.DistLEIntegral
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Hausdorff
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
import Mathlib.Topology.MetricSpace.Cauchy
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Sequences
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Topology.UniformSpace.UniformApproximation
import Mathlib.Topology.UniformSpace.UniformConvergence
import Definitions.Def_YauCounterexample
import Definitions.Def_OAIQ237Ny004
import Theorems.Thm_OAI_Yau_Target_sphereL2Resolvent_compact
import Theorems.Thm_OAI_Yau_Target_sphere_finite_norm_indexed_eigenvalue_continuity
import Theorems.Thm_OAI_Yau_Target_sphere_finite_norm_simple_uniform_persistence
import Theorems.Thm_OAI_Yau_Target_sphere_resolvent_finite_smooth_frame

section
-- module Solutions.OAIQ237_NY.NodalSets_Charts_FiniteChartDerivativeSize
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Set
open scoped ContDiff
noncomputable section
variable {I E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

lemma finiteChartDerivativeValues_nonempty (P : Finset I) (Q : Set E) (J : ℕ) (f : I → E → F) :
    (finiteChartDerivativeValues P Q J f).Nonempty := ⟨0,Or.inl rfl⟩

lemma finiteChartDerivativeValues_bddAbove (P : Finset I) {Q : Set E} (hQ : IsCompact Q)
    (J : ℕ) (f : I → E → F) (hf : ∀ p ∈ P, ContDiff ℝ ∞ (f p)) :
    BddAbove (finiteChartDerivativeValues P Q J f) := by
  classical
  have hb (p : P) (i : Fin (J+1)) : ∃ C : ℝ, ∀ x ∈ Q, ‖iteratedFDeriv ℝ i.val (f p) x‖ ≤ C :=
    hQ.exists_bound_of_continuousOn ((hf p p.property).continuous_iteratedFDeriv
      (by exact_mod_cast (show (i.val:ℕ∞) ≤ ⊤ from le_top))).continuousOn
  choose C hC using hb
  let B : ℝ := 1+∑ p : P, ∑ i, |C p i|
  have hsum : 0 ≤ ∑ p : P, ∑ i, |C p i| :=
    Finset.sum_nonneg (fun _ _ ↦ Finset.sum_nonneg (fun _ _ ↦ abs_nonneg _))
  refine ⟨B,?_⟩
  rintro t (ht | ⟨p,hp,i,hi,x,hx,rfl⟩)
  · have ht0 : t=0 := ht
    rw [ht0]
    change 0 ≤ 1+∑ p : P, ∑ i, |C p i|
    linarith
  · let pi : P := ⟨p,hp⟩
    let ii : Fin (J+1) := ⟨i,by omega⟩
    have hci : C pi ii ≤ ∑ p : P, ∑ j, |C p j| :=
      (le_abs_self _).trans ((Finset.single_le_sum (fun j _ ↦ abs_nonneg (C pi j)) (Finset.mem_univ ii)).trans
        (Finset.single_le_sum (fun p _ ↦ Finset.sum_nonneg (fun j _ ↦ abs_nonneg (C p j))) (Finset.mem_univ pi)))
    exact (hC pi ii x hx).trans (by change C pi ii ≤ 1+∑ p : P, ∑ j, |C p j|; linarith)

lemma finiteChartDerivativeSize_le (P : Finset I) (Q : Set E) (J : ℕ) (f : I → E → F)
    {C : ℝ} (hC : 0 ≤ C) (hb : ∀ p ∈ P, ∀ i, i ≤ J → ∀ x ∈ Q,
      ‖iteratedFDeriv ℝ i (f p) x‖ ≤ C) : finiteChartDerivativeSize P Q J f ≤ C := by
  apply csSup_le (finiteChartDerivativeValues_nonempty P Q J f)
  rintro t (ht | ⟨p,hp,i,hi,x,hx,rfl⟩)
  · have ht0 : t=0 := ht
    simpa only [ht0] using hC
  · exact hb p hp i hi x hx

lemma finiteChartDerivativeSize_nonneg (P : Finset I) {Q : Set E} (hQ : IsCompact Q)
    (J : ℕ) (f : I → E → F) (hf : ∀ p ∈ P, ContDiff ℝ ∞ (f p)) :
    0 ≤ finiteChartDerivativeSize P Q J f :=
  le_csSup (finiteChartDerivativeValues_bddAbove P hQ J f hf) (Or.inl rfl)

lemma norm_le_finiteChartDerivativeSize (P : Finset I) {Q : Set E} (hQ : IsCompact Q)
    (J : ℕ) (f : I → E → F) (hf : ∀ p ∈ P, ContDiff ℝ ∞ (f p))
    (p : I) (hp : p ∈ P) (i : ℕ) (hi : i ≤ J) (x : E) (hx : x ∈ Q) :
    ‖iteratedFDeriv ℝ i (f p) x‖ ≤ finiteChartDerivativeSize P Q J f :=
  le_csSup (finiteChartDerivativeValues_bddAbove P hQ J f hf) (Or.inr ⟨p,hp,i,hi,x,hx,rfl⟩)

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Charts_FiniteChartDerivativeSeminorm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Set
open scoped ContDiff
noncomputable section
variable {I E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

lemma finiteChartDerivativeSize_mono_order (P : Finset I) {Q : Set E} (hQ : IsCompact Q)
    {J K : ℕ} (hJK : J ≤ K) (f : I → E → F) (hf : ∀ p ∈ P, ContDiff ℝ ∞ (f p)) :
    finiteChartDerivativeSize P Q J f ≤ finiteChartDerivativeSize P Q K f := by
  apply finiteChartDerivativeSize_le _ _ _ _ (finiteChartDerivativeSize_nonneg P hQ K f hf)
  intro p hp i hi x hx
  exact norm_le_finiteChartDerivativeSize P hQ K f hf p hp i (hi.trans hJK) x hx

end
end Yau.Geometry

end OAI
end

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
-- module Solutions.OAIQ237_NY.NodalSets_Coefficients_FiniteSphereCoefficientAtlas
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
local instance sphereCoefficientAtlasDim : Fact (Module.finrank ℝ AmbientBase = 4+1) := ⟨by simp [AmbientBase]⟩

lemma finiteAtlas_sphereChartCoordMap_isOpenMap (p : Base) : IsOpenMap (sphereChartCoordMap p) := by
  intro U hU
  have he : sphereChartCoordMap p '' U =
      (extChartAt (𝓡 4) p).symm '' (seedCoordEquiv '' U) := (image_image ((extChartAt (𝓡 4) p).symm) seedCoordEquiv U).symm
  rw [he]
  change IsOpen ((stereographic' 4 (-p)).symm '' (seedCoordEquiv '' U))
  exact (stereographic' 4 (-p)).isOpen_image_symm_of_subset_target
    (seedCoordEquiv.isOpenMap U hU) (by simp)

lemma finiteAtlas_sphereChartCoordMap_zero (p : Base) : sphereChartCoordMap p 0 = p := by
  simp only [sphereChartCoordMap,map_zero,centeredSphereChart_inverse_zero]

theorem finite_sphere_coordinate_cover :
    ∃ P : Finset Base, ∀ x : Base, ∃ p ∈ P, ∃ z ∈ ball (0 : Yau.Jets.Coord) 1,
      sphereChartCoordMap p z = x := by
  have hcover : (univ : Set Base) ⊆ ⋃ p : Base, sphereChartCoordMap p '' ball (0 : Yau.Jets.Coord) 1 := by
    intro x _
    exact mem_iUnion.mpr ⟨x,0,mem_ball_self (by norm_num),finiteAtlas_sphereChartCoordMap_zero x⟩
  obtain ⟨P,hP⟩ := isCompact_univ.elim_finite_subcover
    (fun p : Base ↦ sphereChartCoordMap p '' ball (0 : Yau.Jets.Coord) 1)
    (fun p ↦ finiteAtlas_sphereChartCoordMap_isOpenMap p _ isOpen_ball) hcover
  refine ⟨P,?_⟩
  intro x
  obtain ⟨p,hp,z,hz,hzx⟩ := mem_iUnion₂.mp (hP (mem_univ x))
  exact ⟨p,hp,z,hz,hzx⟩

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Charts_SphereFiniteSmoothPartition
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

theorem sphere_finite_smooth_partition :
    ∃ (P : Finset Base) (theta : {p // p ∈ P} → Base → ℝ),
      (∀ p, ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ (theta p)) ∧
      (∀ p x, 0 ≤ theta p x) ∧ (∀ x, ∑ p, theta p x=1) ∧
      (∀ p, tsupport (theta p) ⊆ sphereChartCoordMap p.val '' ball (0 : Yau.Jets.Coord) 1) ∧
      (∀ p, tsupport (theta p ∘ sphereChartCoordMap p.val) ⊆ closedBall (0 : Yau.Jets.Coord) 1) ∧
      (∀ p, HasCompactSupport (theta p ∘ sphereChartCoordMap p.val)) := by
  classical
  obtain ⟨P,hP⟩ := finite_sphere_coordinate_cover
  let U : {p // p ∈ P} → Set Base := fun p ↦ sphereChartCoordMap p.val '' ball (0 : Yau.Jets.Coord) 1
  have hcover : (univ : Set Base) ⊆ ⋃ p, U p := by
    intro x _
    obtain ⟨p,hp,z,hz,hzx⟩ := hP x
    exact mem_iUnion.mpr ⟨⟨p,hp⟩,z,hz,hzx⟩
  obtain ⟨theta,hsub⟩ := SmoothPartitionOfUnity.exists_isSubordinate (𝓡 4) isClosed_univ U
    (fun p ↦ sphereChartCoordMap_isOpenMap p.val _ isOpen_ball) hcover
  have hs (p : {p // p ∈ P}) :
      tsupport (theta p ∘ sphereChartCoordMap p.val) ⊆ closedBall (0 : Yau.Jets.Coord) 1 := by
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
    exact (isCompact_closedBall (0 : Yau.Jets.Coord) 1).of_isClosed_subset isClosed_closure (hs p)

end
end Yau.Target

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

theorem compact_weighted_weak_equation (gamma phi f : Coord n → ℝ)
    (hg : ContDiff ℝ ∞ gamma) (hgn : ∀ x, gamma x ≠ 0)
    (hphi : ContDiff ℝ ∞ phi) (hc : HasCompactSupport phi)
    (V : Coord n → Coord n) (hV : ∀ i, ContDiff ℝ ∞ (fun x ↦ V x i))
    (he : ∀ x, weightedDiv gamma V x + f x = 0) :
    Integrable (fun x ↦ gamma x*pairing phi V x) ∧
    Integrable (fun x ↦ gamma x*phi x*f x) ∧
    (∫ x, gamma x*pairing phi V x) = ∫ x, gamma x*phi x*f x := by
  obtain ⟨hiP,hiD,hid⟩ := compact_weighted_integration_by_parts gamma phi hg hgn hphi hc V hV
  have heq : (fun x ↦ gamma x*phi x*f x) =
      -(fun x ↦ gamma x*phi x*weightedDiv gamma V x) := by
    funext x
    have hx := he x
    simp only [Pi.neg_apply]
    rw [show f x = -weightedDiv gamma V x by linarith]
    ring
  rw [heq]
  refine ⟨hiP,hiD.neg,?_⟩
  change (∫ x, gamma x*pairing phi V x) = ∫ x, -(gamma x*phi x*weightedDiv gamma V x)
  rw [integral_neg]
  exact hid

end
end Yau

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

lemma real_seedCoordPartial_pullback (f : BaseModel → ℝ) (i : Fin 4) (x : Yau.Jets.Coord) :
    Yau.coordPartial (f ∘ seedCoordEquiv) x i =
      fderiv ℝ f (seedCoordEquiv x) (EuclideanSpace.basisFun (Fin 4) ℝ i) := by
  unfold Yau.coordPartial
  rw [seedCoordEquiv.comp_right_fderiv]
  simp only [ContinuousLinearMap.comp_apply,ContinuousLinearEquiv.coe_coe,seedCoordEquiv_basis]

lemma intrinsicRealFlux_pullback (A : IntrinsicTensor) (w : Base → ℝ) (p : Base) (i : Fin 4) :
    intrinsicRoundFlux A w p i ∘ seedCoordEquiv =
      fun x ↦ roundCoordDensity x * ∑ j,
        intrinsicRealPrincipal A p x i j*Yau.coordPartial (w ∘ sphereChartCoordMap p) x j := by
  funext x
  have hd (j : Fin 4) := real_seedCoordPartial_pullback (w ∘ (extChartAt (𝓡 4) p).symm) j x
  change ∀ j, Yau.coordPartial (w ∘ sphereChartCoordMap p) x j = _ at hd
  simp only [Function.comp_apply,intrinsicRoundFlux,← hd,intrinsicRealPrincipal]
  rw [show roundChartDensity p (seedCoordEquiv x) = roundCoordDensity x by
    simp only [roundCoordDensity,roundChartDensity_conformal]]

theorem intrinsicRealOperator_pullback (A : IntrinsicTensor) (rho w : Base → ℝ)
    (p : Base) (x : Yau.Jets.Coord) :
    intrinsicWeightedChartOperator A rho w p (seedCoordEquiv x) =
      (rho (sphereChartCoordMap p x))⁻¹ * Yau.weightedDiv roundCoordDensity
        (fun y i ↦ ∑ j, intrinsicRealPrincipal A p y i j*
          Yau.coordPartial (w ∘ sphereChartCoordMap p) y j) x := by
  unfold intrinsicWeightedChartOperator Yau.weightedDiv Yau.coordDiv
  have hg : roundChartDensity p (seedCoordEquiv x) = roundCoordDensity x := by
    simp only [roundCoordDensity,roundChartDensity_conformal]
  rw [hg,mul_assoc]
  congr 2
  apply Finset.sum_congr rfl
  intro i _
  rw [← real_seedCoordPartial_pullback, intrinsicRealFlux_pullback]

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_IntrinsicCompactWeakEquation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Manifold Yau.Geometry MeasureTheory
open scoped ContDiff
noncomputable section

lemma intrinsicRealVector_smooth (A : IntrinsicTensor) (hA : IntrinsicTensorSmooth A)
    (hs : ∀ p v w, A p v w = A p w v) (hp : ∀ p v, v ≠ 0 → 0 < A p v v)
    (w : Base → ℝ) (hw : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ w) (p : Base) (i : Fin 4) :
    ContDiff ℝ ∞ (fun y ↦ ∑ j, intrinsicRealPrincipal A p y i j*
      Yau.coordPartial (w ∘ sphereChartCoordMap p) y j) :=
  ContDiff.sum (fun j _ ↦ (intrinsicRealPrincipal_smooth A hA hs hp p i j).mul
    (real_coordPartial_smooth _ (spherePullback_smooth w hw p) j))

lemma intrinsic_real_divergence_equation (A : IntrinsicTensor) (rho : Base → ℝ)
    (hrp : ∀ p, 0 < rho p) (w : Base → ℝ) (lam : ℝ)
    (he : ∀ p z, -intrinsicWeightedChartOperator A rho w p z =
      lam*w ((extChartAt (𝓡 4) p).symm z)) (p : Base) (x : Yau.Jets.Coord) :
    Yau.weightedDiv roundCoordDensity
      (fun y i ↦ ∑ j, intrinsicRealPrincipal A p y i j*
        Yau.coordPartial (w ∘ sphereChartCoordMap p) y j) x +
      intrinsicRealPotential rho lam p x*w (sphereChartCoordMap p x) = 0 := by
  have h := he p (seedCoordEquiv x)
  rw [intrinsicRealOperator_pullback] at h
  change -((rho (sphereChartCoordMap p x))⁻¹ * _) = lam*w (sphereChartCoordMap p x) at h
  have hmul := congrArg (fun t : ℝ ↦ rho (sphereChartCoordMap p x)*t) h
  rw [mul_neg,← mul_assoc,mul_inv_cancel₀ (hrp _).ne',one_mul] at hmul
  dsimp [intrinsicRealPotential]
  linarith

theorem intrinsic_compact_weak_equation (A : IntrinsicTensor) (hA : IntrinsicTensorSmooth A)
    (hs : ∀ p v w, A p v w = A p w v) (hp : ∀ p v, v ≠ 0 → 0 < A p v v)
    (rho : Base → ℝ) (hrp : ∀ p, 0 < rho p)
    (w : Base → ℝ) (hw : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ w) (lam : ℝ)
    (he : ∀ p z, -intrinsicWeightedChartOperator A rho w p z =
      lam*w ((extChartAt (𝓡 4) p).symm z)) (p : Base)
    (phi : Yau.Jets.Coord → ℝ) (hphi : ContDiff ℝ ∞ phi) (hc : HasCompactSupport phi) :
    Integrable (fun x ↦ roundCoordDensity x *
      ∑ i, ∑ j, Yau.coordPartial phi x i*intrinsicRealPrincipal A p x i j*
        Yau.coordPartial (w ∘ sphereChartCoordMap p) x j) ∧
    Integrable (fun x ↦ roundCoordDensity x*phi x*
      (intrinsicRealPotential rho lam p x*w (sphereChartCoordMap p x))) ∧
    (∫ x, roundCoordDensity x * ∑ i, ∑ j,
      Yau.coordPartial phi x i*intrinsicRealPrincipal A p x i j*
        Yau.coordPartial (w ∘ sphereChartCoordMap p) x j) =
    ∫ x, roundCoordDensity x*phi x*(intrinsicRealPotential rho lam p x*w (sphereChartCoordMap p x)) := by
  have h := compact_weighted_weak_equation roundCoordDensity phi
    (fun x ↦ intrinsicRealPotential rho lam p x*w (sphereChartCoordMap p x))
    roundCoordDensity_smooth (fun x ↦ (roundCoordDensity_pos x).ne') hphi hc
    (fun y i ↦ ∑ j, intrinsicRealPrincipal A p y i j*
      Yau.coordPartial (w ∘ sphereChartCoordMap p) y j)
    (intrinsicRealVector_smooth A hA hs hp w hw p)
    (intrinsic_real_divergence_equation A rho hrp w lam he p)
  simpa only [Yau.pairing,Finset.mul_sum,mul_assoc] using h

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_IntrinsicEnergyFiniteSum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Manifold Yau.Geometry
open scoped ContDiff
noncomputable section

lemma sphere_differential_pair_finite_sum {ι : Type*} [Fintype ι]
    (A : IntrinsicTensor) (f : ι → Base → ℝ) (g v : Base → ℝ)
    (hf : ∀ k, ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ (f k))
    (hg : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ g) (hv : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ v)
    (he : ∀ x, ∑ k, f k x = g x) (x : Base) :
    (∑ k, A x (sphereDifferential (f k) x) (sphereDifferential v x)) =
      A x (sphereDifferential g x) (sphereDifferential v x) := by
  classical
  have hd (y : Yau.Jets.Coord) (i : Fin 4) :
      Yau.coordPartial (g ∘ sphereChartCoordMap x) y i =
        ∑ k, Yau.coordPartial (f k ∘ sphereChartCoordMap x) y i := by
    have heq : g ∘ sphereChartCoordMap x = fun z ↦ ∑ k, (f k ∘ sphereChartCoordMap x) z := by
      funext z
      exact (he _).symm
    rw [heq]
    unfold Yau.coordPartial
    rw [fderiv_fun_sum (fun k _ ↦ (spherePullback_smooth (f k) (hf k) x).differentiable (by simp) y)]
    simp
  have hchart (y : Yau.Jets.Coord) :
      (∑ k, A (sphereChartCoordMap x y)
        (sphereDifferential (f k) (sphereChartCoordMap x y))
        (sphereDifferential v (sphereChartCoordMap x y))) =
      A (sphereChartCoordMap x y) (sphereDifferential g (sphereChartCoordMap x y))
        (sphereDifferential v (sphereChartCoordMap x y)) := by
    simp_rw [intrinsic_differential_pair_chart A _ v (hf _) hv,
      intrinsic_differential_pair_chart A g v hg hv,hd,Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_comm]
  have h := hchart 0
  rw [sphereChartCoordMap_zero] at h
  exact h

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_IntrinsicGreenTesting
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Manifold Yau.Geometry MeasureTheory
open scoped ContDiff
noncomputable section

lemma intrinsic_green_compact_chart_test (A : IntrinsicTensor) (hA : IntrinsicTensorSmooth A)
    (hs : ∀ x alpha beta, A x alpha beta = A x beta alpha)
    (hp : ∀ x alpha, alpha ≠ 0 → 0 < A x alpha alpha)
    (rho : Base → ℝ) (hrp : ∀ x, 0 < rho x)
    (u v : Base → ℝ) (hu : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ u)
    (hv : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ v) (lam : ℝ)
    (he : ∀ p z, -intrinsicWeightedChartOperator A rho v p z =
      lam*v ((extChartAt (𝓡 4) p).symm z))
    (p : Base) (hc : HasCompactSupport (u ∘ sphereChartCoordMap p)) :
    (∫ x, A x (sphereDifferential u x) (sphereDifferential v x) ∂sphereReferenceMeasure) =
      lam*sphereWeightedPairing rho u v := by
  have hw := (intrinsic_compact_weak_equation A hA hs hp rho hrp v hv lam he p
    (u ∘ sphereChartCoordMap p) (spherePullback_smooth u hu p) hc).2.2
  rw [sphereReferenceMeasure_integral_chart p,sphereWeightedPairing,
    sphereReferenceMeasure_integral_chart p,← integral_const_mul]
  simp only [roundChartDensity_coord_eq,intrinsic_differential_pair_chart A u v hu hv]
  rw [hw]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun x ↦ by
    simp only [Function.comp_apply,intrinsicRealPotential]
    ring)

theorem intrinsic_green_eigenfunction_test (A : IntrinsicTensor) (hA : IntrinsicTensorSmooth A)
    (hs : ∀ x alpha beta, A x alpha beta = A x beta alpha)
    (hp : ∀ x alpha, alpha ≠ 0 → 0 < A x alpha alpha)
    (rho : Base → ℝ) (hr : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ rho) (hrp : ∀ x, 0 < rho x)
    (u v : Base → ℝ) (hu : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ u)
    (hv : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ v) (lam : ℝ)
    (he : ∀ p z, -intrinsicWeightedChartOperator A rho v p z =
      lam*v ((extChartAt (𝓡 4) p).symm z)) :
    Integrable (fun x ↦ A x (sphereDifferential u x) (sphereDifferential v x)) sphereReferenceMeasure ∧
    Integrable (fun x ↦ rho x*u x*v x) sphereReferenceMeasure ∧
    (∫ x, A x (sphereDifferential u x) (sphereDifferential v x) ∂sphereReferenceMeasure) =
      lam*sphereWeightedPairing rho u v := by
  classical
  refine ⟨intrinsic_differential_pair_integrable A hA hs hp u v hu hv,
    sphereWeightedPairing_integrable rho u v hr.continuous hu.continuous hv.continuous,?_⟩
  obtain ⟨P,theta,htheta,_,hsum,_,_,hcompact⟩ := sphere_finite_smooth_partition
  let f : {p // p ∈ P} → Base → ℝ := fun p x ↦ theta p x*u x
  have hf (p : {p // p ∈ P}) : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ (f p) := (htheta p).mul hu
  have hsumf (x : Base) : ∑ p, f p x = u x := by
    simp only [f,← Finset.sum_mul,hsum,one_mul]
  have hlocal (p : {p // p ∈ P}) := intrinsic_green_compact_chart_test A hA hs hp rho hrp
    (f p) v (hf p) hv lam he p.val ((hcompact p).mul_right)
  calc
    _ = ∫ x, ∑ p, A x (sphereDifferential (f p) x) (sphereDifferential v x) ∂sphereReferenceMeasure := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun x ↦ (sphere_differential_pair_finite_sum A f u v hf hu hv hsumf x).symm)
    _ = ∑ p, ∫ x, A x (sphereDifferential (f p) x) (sphereDifferential v x) ∂sphereReferenceMeasure :=
      integral_finsetSum _ (fun p _ ↦ intrinsic_differential_pair_integrable A hA hs hp (f p) v (hf p) hv)
    _ = lam*(∑ p, sphereWeightedPairing rho (f p) v) := by simp only [hlocal,Finset.mul_sum]
    _ = lam*sphereWeightedPairing rho u v := by
      congr 1
      unfold sphereWeightedPairing
      rw [← integral_finsetSum _ (fun p _ ↦ sphereWeightedPairing_integrable rho (f p) v
        hr.continuous (hf p).continuous hv.continuous)]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun x ↦ by
        change (∑ p, rho x*f p x*v x) = rho x*u x*v x
        rw [← Finset.sum_mul,← Finset.mul_sum,hsumf])

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Charts_SphereEnergyCompletion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Manifold
open scoped ContDiff
noncomputable section

namespace SphereEnergySmooth
variable (d : SphereEnergyData)

theorem norm_sq (u : SphereEnergySmooth d) :
    ‖u‖^2 = sphereWeightedPairing d.density (toSmooth d u) (toSmooth d u) +
      sphereDirichletForm d.tensor (toSmooth d u) (toSmooth d u) := by
  exact (real_inner_self_eq_norm_sq u).symm

end SphereEnergySmooth

theorem sphereEnergyToCompletion_dense (d : SphereEnergyData) :
    DenseRange (sphereEnergyToCompletion d) := UniformSpace.Completion.denseRange_coe

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Charts_SphereSmoothGreenLocal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Manifold Yau.Geometry MeasureTheory
open scoped ContDiff
noncomputable section

theorem sphere_smooth_green_compact_chart (A : IntrinsicTensor) (hA : IntrinsicTensorSmooth A)
    (hs : ∀ x alpha beta, A x alpha beta = A x beta alpha)
    (hp : ∀ x alpha, alpha ≠ 0 → 0 < A x alpha alpha)
    (u v : Base → ℝ) (hu : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ u)
    (hv : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ v) (p : Base)
    (hc : HasCompactSupport (u ∘ sphereChartCoordMap p)) :
    Integrable (fun x ↦ roundCoordDensity x*(u (sphereChartCoordMap p x))*
      Yau.weightedDiv roundCoordDensity (sphereChartFlux A v p) x) ∧
    sphereDirichletForm A u v = -(∫ x, roundCoordDensity x*(u (sphereChartCoordMap p x))*
      Yau.weightedDiv roundCoordDensity (sphereChartFlux A v p) x) := by
  have h := Yau.compact_weighted_integration_by_parts roundCoordDensity
    (u ∘ sphereChartCoordMap p) roundCoordDensity_smooth (fun x ↦ (roundCoordDensity_pos x).ne')
    (spherePullback_smooth u hu p) hc (sphereChartFlux A v p)
    (intrinsicRealVector_smooth A hA hs hp v hv p)
  refine ⟨h.2.1,?_⟩
  rw [sphereDirichletForm,sphereReferenceMeasure_integral_chart p]
  simp only [roundChartDensity_coord_eq,intrinsic_differential_pair_chart A u v hu hv]
  simpa only [Yau.pairing,sphereChartFlux,Function.comp_apply,Finset.mul_sum,mul_assoc] using h.2.2

theorem sphere_smooth_green_finite_partition (A : IntrinsicTensor) (hA : IntrinsicTensorSmooth A)
    (hs : ∀ x alpha beta, A x alpha beta = A x beta alpha)
    (hp : ∀ x alpha, alpha ≠ 0 → 0 < A x alpha alpha) :
    ∃ (P : Finset Base) (theta : {p // p ∈ P} → Base → ℝ),
      (∀ p, ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ (theta p)) ∧
      (∀ x, ∑ p, theta p x = 1) ∧
      (∀ p, HasCompactSupport (theta p ∘ sphereChartCoordMap p.val)) ∧
      ∀ u v : Base → ℝ, ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ u → ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ v →
        sphereDirichletForm A u v = -(∑ p, ∫ x, roundCoordDensity x*
          (theta p (sphereChartCoordMap p.val x)*u (sphereChartCoordMap p.val x))*
          Yau.weightedDiv roundCoordDensity (sphereChartFlux A v p.val) x) := by
  classical
  obtain ⟨P,theta,htheta,_,hsum,_,_,hcompact⟩ := sphere_finite_smooth_partition
  refine ⟨P,theta,htheta,hsum,hcompact,?_⟩
  intro u v hu hv
  let f : {p // p ∈ P} → Base → ℝ := fun p x ↦ theta p x*u x
  have hf (p : {p // p ∈ P}) : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ (f p) := (htheta p).mul hu
  have hsumf (x : Base) : ∑ p, f p x = u x := by
    simp only [f,← Finset.sum_mul,hsum,one_mul]
  have he (p : {p // p ∈ P}) :=
    (sphere_smooth_green_compact_chart A hA hs hp (f p) v (hf p) hv p.val ((hcompact p).mul_right)).2
  calc
    _ = ∫ x, ∑ p, A x (sphereDifferential (f p) x) (sphereDifferential v x) ∂sphereReferenceMeasure := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun x ↦ (sphere_differential_pair_finite_sum A f u v hf hu hv hsumf x).symm)
    _ = ∑ p, sphereDirichletForm A (f p) v :=
      integral_finsetSum _ (fun p _ ↦ intrinsic_differential_pair_integrable A hA hs hp (f p) v (hf p) hv)
    _ = _ := by simp only [he,Finset.sum_neg_distrib,f]

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Charts_SphereWeightedL2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open MeasureTheory
open scoped ENNReal
noncomputable section

attribute [local instance] OAI.Yau.Target.sphereWeightedL2Measurable
attribute [local instance] OAI.Yau.Target.sphereWeightedL2Borel
theorem sphereWeightedToLp_inner (rho : Base → ℝ) (hr : Continuous rho)
    (hp : ∀ x, 0 ≤ rho x) (u v : Base → ℝ) (hu : Continuous u) (hv : Continuous v) :
    inner ℝ (sphereWeightedToLp rho hr hp u hu) (sphereWeightedToLp rho hr hp v hv) =
      sphereWeightedPairing rho u v := by
  rw [L2.inner_def]
  calc
    _ = ∫ x, u x*v x ∂sphereWeightedMeasure rho := by
      apply integral_congr_ae
      filter_upwards [(sphereWeighted_memLp rho hr hp u hu).coeFn_toLp,
        (sphereWeighted_memLp rho hr hp v hv).coeFn_toLp] with x hx hy
      simp only [sphereWeightedToLp] at *
      rw [hx,hy]
      change v x*u x = u x*v x
      ring
    _ = _ := by
      rw [sphereWeightedMeasure_integral rho hr hp]
      simp only [sphereWeightedPairing,mul_assoc]

theorem sphereWeightedToLp_norm_sq (rho : Base → ℝ) (hr : Continuous rho)
    (hp : ∀ x, 0 ≤ rho x) (u : Base → ℝ) (hu : Continuous u) :
    ‖sphereWeightedToLp rho hr hp u hu‖^2 = sphereWeightedPairing rho u u := by
  rw [← real_inner_self_eq_norm_sq,sphereWeightedToLp_inner]

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Charts_SphereEnergyL2Map
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open MeasureTheory
noncomputable section

local instance sphereEnergyL2MapMeasurable_r689318_1 : MeasurableSpace Base := borel Base
local instance sphereEnergyL2MapBorel_r689318_1 : BorelSpace Base := ⟨rfl⟩
theorem sphereEnergyL2Linear_norm_sq (d : SphereEnergyData) (u : SphereEnergySmooth d) :
    ‖sphereEnergyL2Linear d u‖^2 =
      sphereWeightedPairing d.density (SphereEnergySmooth.toSmooth d u) (SphereEnergySmooth.toSmooth d u) :=
  sphereWeightedToLp_norm_sq d.density d.continuous (fun x ↦ (d.positive x).le)
    (SphereEnergySmooth.toSmooth d u) (SphereEnergySmooth.toSmooth d u).property.continuous

theorem sphereEnergyL2Linear_norm_le (d : SphereEnergyData) (u : SphereEnergySmooth d) :
    ‖sphereEnergyL2Linear d u‖ ≤ ‖u‖ := by
  have h := SphereEnergySmooth.norm_sq d u
  have he := sphereDirichletForm_nonneg d.tensor d.pos (SphereEnergySmooth.toSmooth d u)
  have hl := sphereEnergyL2Linear_norm_sq d u
  nlinarith [norm_nonneg u,norm_nonneg (sphereEnergyL2Linear d u)]

theorem sphereEnergyL2Map_coe (d : SphereEnergyData) (u : SphereEnergySmooth d) :
    sphereEnergyL2Map d (sphereEnergyToCompletion d u) = sphereEnergyL2Linear d u := by
  apply LinearMap.extendOfNorm_eq (sphereEnergyToCompletion_dense d)
  refine ⟨1,fun v ↦ ?_⟩
  simpa using sphereEnergyL2Linear_norm_le d v

theorem sphereEnergyL2Map_norm_le (d : SphereEnergyData) : ‖sphereEnergyL2Map d‖ ≤ 1 := by
  apply LinearMap.opNorm_extendOfNorm_le (sphereEnergyToCompletion_dense d) zero_le_one
  intro u
  simpa using sphereEnergyL2Linear_norm_le d u

theorem sphereEnergyL2Map_apply_norm_le (d : SphereEnergyData) (u : SphereEnergyHilbert d) :
    ‖sphereEnergyL2Map d u‖ ≤ ‖u‖ := by
  have h := (sphereEnergyL2Map d).le_opNorm u
  exact h.trans (by simpa using mul_le_mul_of_nonneg_right (sphereEnergyL2Map_norm_le d) (norm_nonneg u))

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Charts_SphereWeightedL1Bound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open MeasureTheory
noncomputable section

local instance sphereWeightedL1BoundMeasurable_r689318_1 : MeasurableSpace Base := borel Base
local instance sphereWeightedL1BoundBorel_r689318_1 : BorelSpace Base := ⟨rfl⟩
theorem sphere_reference_L1_bound (d : SphereEnergyData) : ∃ B : ℝ, 0 ≤ B ∧
    ∀ u : SphereEnergySmooth d,
      (∫ x, |(SphereEnergySmooth.toSmooth d u : Base → ℝ) x| ∂sphereReferenceMeasure) ≤
        B*‖sphereEnergyL2Linear d u‖ := by
  have hi : Continuous (fun x ↦ (d.density x)⁻¹) := d.continuous.inv₀ (fun x ↦ (d.positive x).ne')
  let g := sphereWeightedToLp d.density d.continuous (fun x ↦ (d.positive x).le) _ hi
  refine ⟨‖g‖,norm_nonneg _,?_⟩
  intro u
  let f : Base → ℝ := fun x ↦ |(SphereEnergySmooth.toSmooth d u : Base → ℝ) x|
  have hf : Continuous f := (SphereEnergySmooth.toSmooth d u).property.continuous.abs
  let L := sphereWeightedToLp d.density d.continuous (fun x ↦ (d.positive x).le) f hf
  have hn : ‖L‖ = ‖sphereEnergyL2Linear d u‖ := by
    have hL := sphereWeightedToLp_norm_sq d.density d.continuous (fun x ↦ (d.positive x).le) f hf
    have hu := sphereEnergyL2Linear_norm_sq d u
    have he : sphereWeightedPairing d.density f f =
        sphereWeightedPairing d.density (SphereEnergySmooth.toSmooth d u) (SphereEnergySmooth.toSmooth d u) := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun x ↦ by
        dsimp [f]
        simp only [mul_assoc,← sq,sq_abs])
    rw [he] at hL
    change ‖L‖^2 = _ at hL
    nlinarith [norm_nonneg L,norm_nonneg (sphereEnergyL2Linear d u)]
  have he : inner ℝ L g = ∫ x, f x ∂sphereReferenceMeasure := by
    rw [sphereWeightedToLp_inner]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun x ↦ by
      change d.density x*f x*(d.density x)⁻¹ = f x
      field_simp [(d.positive x).ne'])
  have h := real_inner_le_norm L g
  rw [he,hn] at h
  exact h.trans_eq (mul_comm _ _)

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Charts_SphereSmoothGreenBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Manifold Yau.Geometry MeasureTheory Set
open scoped ContDiff
noncomputable section

local instance sphereSmoothGreenBoundMeasurable_r689318_1 : MeasurableSpace Base := borel Base
local instance sphereSmoothGreenBoundBorel_r689318_1 : BorelSpace Base := ⟨rfl⟩
theorem sphere_smooth_dirichlet_L1_bound (d : SphereEnergyData) (v : SphereEnergySmooth d) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u : SphereEnergySmooth d,
      |sphereDirichletForm d.tensor (SphereEnergySmooth.toSmooth d u) (SphereEnergySmooth.toSmooth d v)| ≤
        C*(∫ x, |(SphereEnergySmooth.toSmooth d u : Base → ℝ) x| ∂sphereReferenceMeasure) := by
  classical
  obtain ⟨P,theta,htheta,_,hc,hgreen⟩ := sphere_smooth_green_finite_partition d.tensor d.smooth d.symm d.pos
  let I := {p // p ∈ P}
  let G : I → Yau.Jets.Coord → ℝ := fun p x ↦ theta p (sphereChartCoordMap p.val x)*
    Yau.weightedDiv roundCoordDensity (sphereChartFlux d.tensor (SphereEnergySmooth.toSmooth d v) p.val) x
  have hG (p : I) : Continuous (G p) :=
    (spherePullback_smooth (theta p) (htheta p) p.val).continuous.mul
      (Yau.weightedDiv_smooth roundCoordDensity_smooth (fun x ↦ (roundCoordDensity_pos x).ne')
        (intrinsicRealVector_smooth d.tensor d.smooth d.symm d.pos (SphereEnergySmooth.toSmooth d v)
          (SphereEnergySmooth.toSmooth d v).property p.val)).continuous
  have hGc (p : I) : HasCompactSupport (G p) := (hc p).mul_right
  have hb (p : I) : ∃ K : ℝ, 0 ≤ K ∧ ∀ x, |G p x| ≤ K := by
    obtain ⟨K,hK⟩ := (((hGc p).isCompact_range (hG p)).image continuous_norm).bddAbove
    refine ⟨max K 0,le_max_right _ _,fun x ↦ ?_⟩
    exact (hK ⟨G p x,⟨x,rfl⟩,rfl⟩).trans (le_max_left _ _)
  choose K hK hKb using hb
  refine ⟨∑ p, K p,Finset.sum_nonneg (fun p _ ↦ hK p),?_⟩
  intro u
  let f : Base → ℝ := SphereEnergySmooth.toSmooth d u
  have hf : Continuous f := (SphereEnergySmooth.toSmooth d u).property.continuous
  have hI (p : I) : Integrable (fun x ↦ roundCoordDensity x*|f (sphereChartCoordMap p.val x)|) := by
    simpa only [roundChartDensity_coord_eq] using
      (sphereReferenceMeasure_integrable_chart p.val (fun x ↦ |f x|)).mp
        (sphereReferenceMeasure_integrable_continuous _ hf.abs)
  have hterm (p : I) : |∫ x, roundCoordDensity x*f (sphereChartCoordMap p.val x)*G p x| ≤
      K p*(∫ x, |f x| ∂sphereReferenceMeasure) := by
    have hi : Integrable (fun x ↦ roundCoordDensity x*f (sphereChartCoordMap p.val x)*G p x) :=
      ((roundCoordDensity_smooth.continuous.mul (hf.comp (sphereChartCoordMap_smooth p.val).continuous)).mul (hG p)).integrable_of_hasCompactSupport
        (hGc p).mul_left
    calc
      _ ≤ ∫ x, ‖roundCoordDensity x*f (sphereChartCoordMap p.val x)*G p x‖ := norm_integral_le_integral_norm _
      _ ≤ ∫ x, K p*(roundCoordDensity x*|f (sphereChartCoordMap p.val x)|) := by
        apply integral_mono hi.norm ((hI p).const_mul (K p))
        intro x
        simp only [norm_mul,Real.norm_eq_abs,abs_of_pos (roundCoordDensity_pos x)]
        nlinarith [mul_le_mul_of_nonneg_left (hKb p x)
          (mul_nonneg (roundCoordDensity_pos x).le (abs_nonneg (f (sphereChartCoordMap p.val x))))]
      _ = _ := by
        rw [integral_const_mul,sphereReferenceMeasure_integral_chart p.val]
        simp only [roundChartDensity_coord_eq]
  have hg := hgreen f (SphereEnergySmooth.toSmooth d v) (SphereEnergySmooth.toSmooth d u).property
    (SphereEnergySmooth.toSmooth d v).property
  rw [hg,abs_neg]
  calc
    _ = |∑ p : I, ∫ x, roundCoordDensity x*f (sphereChartCoordMap p.val x)*G p x| := by
      congr 1
      apply Finset.sum_congr rfl
      intro p _
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun x ↦ by dsimp [G] <;> ring)
    _ ≤ ∑ p : I, |∫ x, roundCoordDensity x*f (sphereChartCoordMap p.val x)*G p x| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ p : I, K p*(∫ x, |f x| ∂sphereReferenceMeasure) :=
      Finset.sum_le_sum (fun p _ ↦ hterm p)
    _ = _ := by rw [Finset.sum_mul]

theorem sphere_smooth_dirichlet_L2_bound (d : SphereEnergyData) (v : SphereEnergySmooth d) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u : SphereEnergySmooth d,
      |sphereDirichletForm d.tensor (SphereEnergySmooth.toSmooth d u) (SphereEnergySmooth.toSmooth d v)| ≤
        C*‖sphereEnergyL2Linear d u‖ := by
  obtain ⟨C,hC,hb⟩ := sphere_smooth_dirichlet_L1_bound d v
  obtain ⟨B,hB,hL⟩ := sphere_reference_L1_bound d
  refine ⟨C*B,mul_nonneg hC hB,fun u ↦ ?_⟩
  exact (hb u).trans ((mul_le_mul_of_nonneg_left (hL u) hC).trans_eq (mul_assoc C B _).symm)

end
end Yau.Target

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

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_RealEllipticLinearity
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open scoped ContDiff
noncomputable section

lemma real_partial_linear_combination (u v : Yau.Jets.Coord → ℝ)
    (hu : ContDiff ℝ ∞ u) (hv : ContDiff ℝ ∞ v) (c : ℝ) (x : Yau.Jets.Coord) (i : Fin 4) :
    Yau.coordPartial (fun y ↦ c*u y+v y) x i = c*Yau.coordPartial u x i+Yau.coordPartial v x i := by
  rw [Yau.real_coordPartial_add _ _ (contDiff_const.mul hu) hv,Yau.real_coordPartial_const_mul u hu]

lemma realWeightedElliptic_linear_combination (gamma : Yau.Jets.Coord → ℝ)
    (B : Yau.Jets.Coord → Matrix (Fin 4) (Fin 4) ℝ)
    (u v : Yau.Jets.Coord → ℝ) (hg : ContDiff ℝ ∞ gamma)
    (hB : ∀ i j, ContDiff ℝ ∞ (fun x ↦ B x i j))
    (hu : ContDiff ℝ ∞ u) (hv : ContDiff ℝ ∞ v) (c : ℝ) (x : Yau.Jets.Coord) :
    realWeightedElliptic gamma B (fun y ↦ c*u y+v y) x =
      c*realWeightedElliptic gamma B u x+realWeightedElliptic gamma B v x := by
  have he (i : Fin 4) : (fun y ↦ gamma y*realMatrixFlux B (fun z ↦ c*u z+v z) y i) =
      fun y ↦ c*(gamma y*realMatrixFlux B u y i)+gamma y*realMatrixFlux B v y i := by
    funext y
    simp only [realMatrixFlux,real_partial_linear_combination u v hu hv,mul_add,Finset.sum_add_distrib,Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl; intro j _; ring
  unfold realWeightedElliptic Yau.weightedDiv Yau.coordDiv
  simp_rw [he,real_partial_linear_combination _ _
    (hg.mul (realMatrixFlux_smooth B u hB hu _)) (hg.mul (realMatrixFlux_smooth B v hB hv _))]
  rw [Finset.sum_add_distrib,← Finset.mul_sum]
  ring

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Charts_SphereSmoothL2Density
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Manifold MeasureTheory
open scoped ContDiff
noncomputable section
attribute [local instance] OAI.Yau.Target.sphereSmoothL2DensityMeasurable
local instance sphereSmoothL2DensityBorel : BorelSpace Base := ⟨rfl⟩

theorem sphereSmoothToContinuous_dense (d : SphereEnergyData) : DenseRange (sphereSmoothToContinuous d) := by
  rw [Metric.denseRange_iff]
  intro f eps heps
  obtain ⟨g,hg,-⟩ := f.continuous.exists_contMDiff_approx (𝓡 4) (⊤ : ℕ∞)
    (continuous_const : Continuous (fun _ : Base ↦ eps/2)) (fun _ ↦ half_pos heps)
  let u : SphereEnergySmooth d := (⟨g,g.contMDiff⟩ : sphereSmoothFunctions)
  refine ⟨u,lt_of_le_of_lt ?_ (half_lt_self heps)⟩
  apply (ContinuousMap.dist_le (half_pos heps).le).mpr
  intro x
  change dist (f x) (g x) ≤ eps/2
  rw [dist_comm]
  exact (hg x).le

theorem sphereEnergyL2Linear_dense (d : SphereEnergyData) : DenseRange (sphereEnergyL2Linear d) := by
  let := sphereWeightedMeasure_finite d.density d.continuous (fun x ↦ (d.positive x).le)
  have hd := (ContinuousMap.toLp_denseRange (E := ℝ) (μ := sphereWeightedMeasure d.density) (𝕜 := ℝ) (p := 2) (by simp)).comp
    (sphereSmoothToContinuous_dense d) (ContinuousMap.toLp 2 (sphereWeightedMeasure d.density) ℝ).continuous
  have heq : (ContinuousMap.toLp 2 (sphereWeightedMeasure d.density) ℝ) ∘ sphereSmoothToContinuous d =
      sphereEnergyL2Linear d := by
    funext u
    apply Lp.ext
    exact ((sphereSmoothToContinuous d u).coeFn_toLp (sphereWeightedMeasure d.density)).trans
      (sphereWeighted_memLp d.density d.continuous (fun x ↦ (d.positive x).le)
        (SphereEnergySmooth.toSmooth d u) (SphereEnergySmooth.toSmooth d u).property.continuous).coeFn_toLp.symm
  rwa [heq] at hd

theorem sphereEnergyL2Map_dense (d : SphereEnergyData) : DenseRange (sphereEnergyL2Map d) := by
  apply (sphereEnergyL2Linear_dense d).mono
  rintro _ ⟨u,rfl⟩
  exact ⟨sphereEnergyToCompletion d u,sphereEnergyL2Map_coe d u⟩

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Spectral_SphereWeakResolvent
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open MeasureTheory Filter
open scoped InnerProduct
noncomputable section

local instance sphereWeakResolventMeasurable_r689318_1 : MeasurableSpace Base := borel Base
local instance sphereWeakResolventBorel_r689318_1 : BorelSpace Base := ⟨rfl⟩
theorem sphereCompletedDirichlet_coe (d : SphereEnergyData) (u v : SphereEnergySmooth d) :
    sphereCompletedDirichlet d (sphereEnergyToCompletion d u) (sphereEnergyToCompletion d v) =
      sphereDirichletForm d.tensor (SphereEnergySmooth.toSmooth d u) (SphereEnergySmooth.toSmooth d v) := by
  rw [sphereCompletedDirichlet,sphereEnergyL2Map_coe,sphereEnergyL2Map_coe]
  have hinner : inner ℝ (sphereEnergyL2Linear d u) (sphereEnergyL2Linear d v) =
      sphereWeightedPairing d.density (SphereEnergySmooth.toSmooth d u) (SphereEnergySmooth.toSmooth d v) :=
    sphereWeightedToLp_inner d.density d.continuous (fun x ↦ (d.positive x).le) _ _
      (SphereEnergySmooth.toSmooth d u).property.continuous (SphereEnergySmooth.toSmooth d v).property.continuous
  rw [hinner,(sphereEnergyToCompletion d).inner_map_map]
  change (sphereWeightedPairing d.density (SphereEnergySmooth.toSmooth d u) (SphereEnergySmooth.toSmooth d v)+
    sphereDirichletForm d.tensor (SphereEnergySmooth.toSmooth d u) (SphereEnergySmooth.toSmooth d v))-
    sphereWeightedPairing d.density (SphereEnergySmooth.toSmooth d u) (SphereEnergySmooth.toSmooth d v) = _
  ring

theorem sphereCompletedDirichlet_nonneg (d : SphereEnergyData) (u : SphereEnergyHilbert d) :
    0 ≤ sphereCompletedDirichlet d u u := by
  rw [sphereCompletedDirichlet,real_inner_self_eq_norm_sq,real_inner_self_eq_norm_sq]
  nlinarith [sphereEnergyL2Map_apply_norm_le d u,norm_nonneg u,norm_nonneg (sphereEnergyL2Map d u)]

theorem sphereWeakSolution_spec (d : SphereEnergyData) (f : SphereWeightedL2 d) (v : SphereEnergyHilbert d) :
    inner ℝ (sphereWeakSolution d f) v = inner ℝ f (sphereEnergyL2Map d v) :=
  (sphereEnergyL2Map d).adjoint_inner_left v f

theorem sphereWeakSolution_eq_zero_iff (d : SphereEnergyData) (f : SphereWeightedL2 d) :
    sphereWeakSolution d f = 0 ↔ f = 0 := by
  constructor
  · intro hf
    apply (inner_self_eq_zero (𝕜 := ℝ)).mp
    have hclosed : IsClosed {v : SphereWeightedL2 d | inner ℝ f v = 0} :=
      isClosed_eq (by fun_prop) continuous_const
    exact (sphereEnergyL2Map_dense d).induction_on (p := fun v ↦ inner ℝ f v = 0) f hclosed (fun u ↦ by
      rw [← sphereWeakSolution_spec,hf,inner_zero_left])
  · rintro rfl
    exact map_zero _

theorem sphereL2Resolvent_inner (d : SphereEnergyData) (f g : SphereWeightedL2 d) :
    inner ℝ (sphereL2Resolvent d f) g = inner ℝ (sphereWeakSolution d f) (sphereWeakSolution d g) := by
  exact ((sphereEnergyL2Map d).adjoint_inner_right (sphereWeakSolution d f) g).symm

theorem sphereL2Resolvent_symmetric (d : SphereEnergyData) : (sphereL2Resolvent d).IsSymmetric := by
  intro f g
  change inner ℝ (sphereL2Resolvent d f) g = inner ℝ f (sphereL2Resolvent d g)
  calc
    _ = inner ℝ (sphereWeakSolution d f) (sphereWeakSolution d g) := sphereL2Resolvent_inner d f g
    _ = inner ℝ (sphereWeakSolution d g) (sphereWeakSolution d f) := real_inner_comm _ _
    _ = inner ℝ (sphereL2Resolvent d g) f := (sphereL2Resolvent_inner d g f).symm
    _ = _ := real_inner_comm _ _

theorem sphereL2Resolvent_positive (d : SphereEnergyData) (f : SphereWeightedL2 d) (hf : f ≠ 0) :
    0 < inner ℝ (sphereL2Resolvent d f) f := by
  rw [sphereL2Resolvent_inner,real_inner_self_eq_norm_sq]
  exact sq_pos_of_pos (norm_pos_iff.mpr (fun h ↦ hf ((sphereWeakSolution_eq_zero_iff d f).mp h)))

theorem sphereL2Resolvent_norm_le (d : SphereEnergyData) : ‖sphereL2Resolvent d‖ ≤ 1 := by
  have ha : ‖sphereWeakSolution d‖ = ‖sphereEnergyL2Map d‖ :=
    ContinuousLinearMap.adjoint.norm_map (sphereEnergyL2Map d)
  have h := ContinuousLinearMap.opNorm_comp_le (sphereEnergyL2Map d) (sphereWeakSolution d)
  rw [ha] at h
  apply h.trans
  nlinarith [sphereEnergyL2Map_norm_le d,norm_nonneg (sphereEnergyL2Map d)]

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Charts_SphereEnergyL2Injective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open MeasureTheory
noncomputable section

local instance sphereEnergyL2InjectiveMeasurable_r689318_1 : MeasurableSpace Base := borel Base
local instance sphereEnergyL2InjectiveBorel_r689318_1 : BorelSpace Base := ⟨rfl⟩
theorem sphere_completed_dirichlet_test_bound (d : SphereEnergyData) (v : SphereEnergySmooth d) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : SphereEnergyHilbert d,
      |sphereCompletedDirichlet d z (sphereEnergyToCompletion d v)| ≤ C*‖sphereEnergyL2Map d z‖ := by
  obtain ⟨C,hC,hb⟩ := sphere_smooth_dirichlet_L2_bound d v
  refine ⟨C,hC,?_⟩
  intro z
  apply (sphereEnergyToCompletion_dense d).induction_on
    (p := fun z ↦ |sphereCompletedDirichlet d z (sphereEnergyToCompletion d v)| ≤ C*‖sphereEnergyL2Map d z‖) z
  · apply isClosed_le
    · exact ((continuous_id.inner continuous_const).sub
        ((sphereEnergyL2Map d).continuous.inner continuous_const)).abs
    · fun_prop
  · intro u
    rw [sphereCompletedDirichlet_coe,sphereEnergyL2Map_coe]
    exact hb u

theorem sphereEnergyL2Map_eq_zero_iff (d : SphereEnergyData) (z : SphereEnergyHilbert d) :
    sphereEnergyL2Map d z = 0 ↔ z = 0 := by
  constructor
  · intro hz
    apply (inner_self_eq_zero (𝕜 := ℝ)).mp
    apply (sphereEnergyToCompletion_dense d).induction_on (p := fun v ↦ inner ℝ z v = 0) z
    · exact isClosed_eq (by fun_prop) continuous_const
    · intro v
      obtain ⟨C,_,hC⟩ := sphere_completed_dirichlet_test_bound d v
      have h := hC z
      rw [hz,norm_zero,mul_zero] at h
      have hd := abs_eq_zero.mp (le_antisymm h (abs_nonneg _))
      simpa only [sphereCompletedDirichlet,hz,inner_zero_left,sub_zero] using hd
  · rintro rfl
    exact map_zero _

theorem sphereEnergyL2Map_injective (d : SphereEnergyData) : Function.Injective (sphereEnergyL2Map d) := by
  apply (LinearMap.ker_eq_bot).mp
  ext z
  exact sphereEnergyL2Map_eq_zero_iff d z

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Spectral_FiniteEigenframeCaptureLemmas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Yau.Analysis

theorem real_symmetric_distinct_eigenvectors_orthogonal {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (T : E →L[ℝ] E) (hs : T.IsSymmetric) (u v : E) (a b : ℝ)
    (hu : T u=a • u) (hv : T v=b • v) (hab : a ≠ b) : inner ℝ u v=0 := by
  have h : inner ℝ (T u) v = inner ℝ u (T v) := hs u v
  rw [hu,hv,inner_smul_left_eq_smul,smul_eq_mul,inner_smul_right] at h
  exact (mul_eq_zero.mp (show (a-b)*inner ℝ u v=0 by nlinarith)).resolve_left (sub_ne_zero.mpr hab)

theorem finite_eigenframe_captures_above_last {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] {N : ℕ}
    (T : E →L[ℝ] E) (hs : T.IsSymmetric) (e : Fin (N+1) → E) (mu : Fin (N+1) → ℝ)
    (he : ∀ i, T (e i)=mu i • e i)
    (hmax : ∀ i x, (∀ j, j < i → inner ℝ (e j) x=0) →
      inner ℝ (T x) x ≤ mu i*‖x‖^2)
    (f : E) (hf : f ≠ 0) (a : ℝ) (hfa : T f=a • f)
    (ha : mu (Fin.last N) < a) : ∃ i, mu i=a := by
  classical
  by_contra hn
  push Not at hn
  have horth (i) : inner ℝ (e i) f=0 :=
    real_symmetric_distinct_eigenvectors_orthogonal T hs (e i) f (mu i) a (he i) hfa (hn i)
  have hb := hmax (Fin.last N) f (fun j _ ↦ horth j)
  rw [hfa,inner_smul_left_eq_smul,smul_eq_mul,real_inner_self_eq_norm_sq] at hb
  have hnpos : 0 < ‖f‖^2 := sq_pos_of_pos (norm_pos_iff.mpr hf)
  exact (not_le_of_gt ha) ((mul_le_mul_iff_left₀ hnpos).mp hb)

theorem finite_frame_maximum_restrict {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] {M N : ℕ} (hMN : M ≤ N)
    (T : E →L[ℝ] E) (e : Fin N → E) (mu : Fin N → ℝ)
    (hmax : ∀ i x, (∀ j, j < i → inner ℝ (e j) x = 0) →
      inner ℝ (T x) x ≤ mu i * ‖x‖^2) :
    ∀ i : Fin M, ∀ x,
      (∀ j : Fin M, j < i → inner ℝ (e (Fin.castLE hMN j)) x = 0) →
      inner ℝ (T x) x ≤ mu (Fin.castLE hMN i) * ‖x‖^2 := by
  intro i x hx
  apply hmax
  intro j hj
  have hji : j.val < i.val := hj
  exact hx ⟨j.val,lt_trans hji i.isLt⟩ hji

end Yau.Analysis

end

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_FiniteLinearConstraints
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Analysis
noncomputable section

theorem subspace_nonzero_linear_constraints {S : Type*} [AddCommGroup S] [Module ℝ S]
    {N : ℕ} (V : Submodule ℝ S) [FiniteDimensional ℝ V]
    (hV : N < Module.finrank ℝ V) (ell : Fin N → S →ₗ[ℝ] ℝ) :
    ∃ x : S, x ∈ V ∧ x ≠ 0 ∧ ∀ i, ell i x = 0 := by
  let L : V →ₗ[ℝ] (Fin N → ℝ) := LinearMap.pi (fun i ↦ (ell i).comp V.subtype)
  have hk : LinearMap.ker L ≠ ⊥ := LinearMap.ker_ne_bot_of_finrank_lt (by simpa using hV)
  obtain ⟨x,hx,hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hk
  exact ⟨x,x.property,fun h ↦ hx0 (Subtype.ext h),fun i ↦ congrFun (LinearMap.mem_ker.mp hx) i⟩

end
end Yau.Analysis

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Spectral_SphereResolventSpectrum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open MeasureTheory
noncomputable section

local instance sphereResolventSpectrumMeasurable_r689318_1 : MeasurableSpace Base := borel Base
local instance sphereResolventSpectrumBorel_r689318_1 : BorelSpace Base := ⟨rfl⟩
theorem sphereL2Resolvent_eigenvalue_bounds (d : SphereEnergyData) (mu : ℝ) (f : SphereWeightedL2 d)
    (hf : f ≠ 0) (he : sphereL2Resolvent d f = mu • f) : 0 < mu ∧ mu ≤ 1 := by
  have hpos := sphereL2Resolvent_positive d f hf
  rw [he,inner_smul_left_eq_smul,real_inner_self_eq_norm_sq,smul_eq_mul] at hpos
  have hn : 0 < ‖f‖ := norm_pos_iff.mpr hf
  have hm : 0 < mu := (mul_pos_iff_of_pos_right (sq_pos_of_pos hn)).mp hpos
  refine ⟨hm,?_⟩
  have h := (sphereL2Resolvent d).le_opNorm f
  have hb := mul_le_mul_of_nonneg_right (sphereL2Resolvent_norm_le d) (norm_nonneg f)
  rw [he,norm_smul,Real.norm_eq_abs,abs_of_pos hm] at h
  nlinarith

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Spectral_SphereVariationalResolvent
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open MeasureTheory Manifold
open scoped ContDiff
noncomputable section

local instance sphereVariationalResolventMeasurable_r689318_1 : MeasurableSpace Base := borel Base
local instance sphereVariationalResolventBorel_r689318_1 : BorelSpace Base := ⟨rfl⟩
theorem sphere_variational_eigenvalue_nonneg (d : SphereEnergyData) (lam : ℝ)
    (z : SphereEnergyHilbert d) (hz : sphereEnergyL2Map d z ≠ 0)
    (he : ∀ v, sphereCompletedDirichlet d z v =
      lam*inner ℝ (sphereEnergyL2Map d z) (sphereEnergyL2Map d v)) : 0 ≤ lam := by
  have h := sphereCompletedDirichlet_nonneg d z
  rw [he z,real_inner_self_eq_norm_sq] at h
  exact (mul_nonneg_iff_of_pos_right (sq_pos_of_pos (norm_pos_iff.mpr hz))).mp h

theorem sphere_variational_eigen_to_resolvent (d : SphereEnergyData) (lam : ℝ)
    (z : SphereEnergyHilbert d) (hz : sphereEnergyL2Map d z ≠ 0)
    (he : ∀ v, sphereCompletedDirichlet d z v =
      lam*inner ℝ (sphereEnergyL2Map d z) (sphereEnergyL2Map d v)) :
    z = (lam+1) • sphereWeakSolution d (sphereEnergyL2Map d z) ∧
    sphereL2Resolvent d (sphereEnergyL2Map d z) = (lam+1)⁻¹ • sphereEnergyL2Map d z := by
  have hlam : 0 < lam+1 := by linarith [sphere_variational_eigenvalue_nonneg d lam z hz he]
  have heq : z = (lam+1) • sphereWeakSolution d (sphereEnergyL2Map d z) := by
    apply ext_inner_right ℝ
    intro v
    rw [inner_smul_left_eq_smul,smul_eq_mul,sphereWeakSolution_spec]
    have h := he v
    dsimp [sphereCompletedDirichlet] at h
    linarith
  refine ⟨heq,?_⟩
  have h := congrArg (sphereEnergyL2Map d) heq
  rw [map_smul] at h
  change sphereEnergyL2Map d z = (lam+1) • sphereL2Resolvent d (sphereEnergyL2Map d z) at h
  conv_rhs => rw [h,smul_smul,inv_mul_cancel₀ hlam.ne',one_smul]

theorem sphere_smooth_intrinsic_eigen_to_variational (d : SphereEnergyData)
    (hr : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ d.density) (u : SphereEnergySmooth d) (lam : ℝ)
    (he : ∀ p z, -intrinsicWeightedChartOperator d.tensor d.density (SphereEnergySmooth.toSmooth d u) p z =
      lam*((SphereEnergySmooth.toSmooth d u : Base → ℝ)) ((extChartAt (𝓡 4) p).symm z)) :
    ∀ v : SphereEnergyHilbert d,
      sphereCompletedDirichlet d (sphereEnergyToCompletion d u) v =
        lam*inner ℝ (sphereEnergyL2Map d (sphereEnergyToCompletion d u)) (sphereEnergyL2Map d v) := by
  intro v
  apply (sphereEnergyToCompletion_dense d).induction_on
    (p := fun v ↦ sphereCompletedDirichlet d (sphereEnergyToCompletion d u) v =
      lam*inner ℝ (sphereEnergyL2Map d (sphereEnergyToCompletion d u)) (sphereEnergyL2Map d v)) v
  · apply isClosed_eq
    · exact (continuous_const.inner continuous_id).sub
        (continuous_const.inner (sphereEnergyL2Map d).continuous)
    · fun_prop
  · intro w
    rw [sphereCompletedDirichlet_coe,sphereEnergyL2Map_coe,sphereEnergyL2Map_coe]
    have hinner : inner ℝ (sphereEnergyL2Linear d u) (sphereEnergyL2Linear d w) =
        sphereWeightedPairing d.density (SphereEnergySmooth.toSmooth d u) (SphereEnergySmooth.toSmooth d w) :=
      sphereWeightedToLp_inner _ d.continuous (fun x ↦ (d.positive x).le) _ _
        (SphereEnergySmooth.toSmooth d u).property.continuous (SphereEnergySmooth.toSmooth d w).property.continuous
    rw [hinner,sphereDirichletForm_symm d.tensor d.symm]
    have h := (intrinsic_green_eigenfunction_test d.tensor d.smooth d.symm d.pos d.density hr d.positive
      (SphereEnergySmooth.toSmooth d w) (SphereEnergySmooth.toSmooth d u)
      (SphereEnergySmooth.toSmooth d w).property (SphereEnergySmooth.toSmooth d u).property lam he).2.2
    simpa only [sphereDirichletForm,sphereWeightedPairing_symm d.density (SphereEnergySmooth.toSmooth d w)
      (SphereEnergySmooth.toSmooth d u)] using h

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Spectral_SphereSmoothResolventBridge
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Manifold MeasureTheory
open scoped ContDiff
noncomputable section

local instance sphereSmoothResolventBridgeMeasurable_r689318_1 : MeasurableSpace Base := borel Base
local instance sphereSmoothResolventBridgeBorel_r689318_1 : BorelSpace Base := ⟨rfl⟩
theorem sphereEnergyL2Linear_eq_zero_iff (d : SphereEnergyData) (u : SphereEnergySmooth d) :
    sphereEnergyL2Linear d u = 0 ↔ u = 0 := by
  constructor
  · intro hu
    by_contra hn
    have hfun : (SphereEnergySmooth.toSmooth d u : Base → ℝ) ≠ 0 := by
      intro hf
      apply hn
      exact Subtype.ext hf
    have hp := sphereWeightedPairing_self_pos d.density (SphereEnergySmooth.toSmooth d u)
      d.continuous d.positive (SphereEnergySmooth.toSmooth d u).property.continuous hfun
    have he := sphereEnergyL2Linear_norm_sq d u
    rw [hu,norm_zero,zero_pow (by decide : 2 ≠ 0)] at he
    exact (ne_of_gt hp) he.symm
  · rintro rfl
    exact map_zero _

theorem sphere_smooth_intrinsic_eigen_to_resolvent (d : SphereEnergyData)
    (hr : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ d.density) (u : SphereEnergySmooth d) (hu : u ≠ 0) (lam : ℝ)
    (he : ∀ p z, -intrinsicWeightedChartOperator d.tensor d.density (SphereEnergySmooth.toSmooth d u) p z =
      lam*(SphereEnergySmooth.toSmooth d u : Base → ℝ) ((extChartAt (𝓡 4) p).symm z)) :
    0 ≤ lam ∧ sphereEnergyL2Linear d u ≠ 0 ∧
      sphereL2Resolvent d (sphereEnergyL2Linear d u) = (lam+1)⁻¹ • sphereEnergyL2Linear d u := by
  have hn : sphereEnergyL2Map d (sphereEnergyToCompletion d u) ≠ 0 := by
    rw [sphereEnergyL2Map_coe]
    exact fun h ↦ hu ((sphereEnergyL2Linear_eq_zero_iff d u).mp h)
  have hw := sphere_smooth_intrinsic_eigen_to_variational d hr u lam he
  have hb := sphere_variational_eigenvalue_nonneg d lam (sphereEnergyToCompletion d u) hn hw
  have h := (sphere_variational_eigen_to_resolvent d lam (sphereEnergyToCompletion d u) hn hw).2
  rw [sphereEnergyL2Map_coe] at h hn
  exact ⟨hb,hn,h⟩

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Spectral_SphereResolventFormBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open MeasureTheory
noncomputable section

local instance sphereFormBoundsMeasurable_r689318_1 : MeasurableSpace Base := borel Base
local instance sphereFormBoundsBorel_r689318_1 : BorelSpace Base := ⟨rfl⟩
theorem sphere_resolvent_smooth_variational (d : SphereEnergyData)
    (mu : ℝ) (hmu : mu ≠ 0) (u : SphereEnergySmooth d)
    (he : sphereL2Resolvent d (sphereEnergyL2Linear d u) = mu • sphereEnergyL2Linear d u) :
    ∀ v : SphereEnergyHilbert d,
      inner ℝ (sphereEnergyToCompletion d u) v =
        mu⁻¹ * inner ℝ (sphereEnergyL2Linear d u) (sphereEnergyL2Map d v) := by
  have hz : sphereEnergyToCompletion d u = mu⁻¹ • sphereWeakSolution d (sphereEnergyL2Linear d u) := by
    apply sphereEnergyL2Map_injective d
    rw [sphereEnergyL2Map_coe,map_smul]
    change sphereEnergyL2Linear d u = mu⁻¹ • sphereL2Resolvent d (sphereEnergyL2Linear d u)
    rw [he,smul_smul,inv_mul_cancel₀ hmu,one_smul]
  intro v
  rw [hz,inner_smul_left_eq_smul,smul_eq_mul,sphereWeakSolution_spec]

theorem sphere_resolvent_quadratic_to_form_lower (d : SphereEnergyData)
    (mu : ℝ) (hmu : 0 < mu) (z : SphereEnergyHilbert d)
    (hz : sphereEnergyL2Map d z ≠ 0)
    (hb : inner ℝ (sphereL2Resolvent d (sphereEnergyL2Map d z)) (sphereEnergyL2Map d z) ≤
      mu * ‖sphereEnergyL2Map d z‖^2) :
    (mu⁻¹-1)*‖sphereEnergyL2Map d z‖^2 ≤ sphereCompletedDirichlet d z z := by
  let f := sphereEnergyL2Map d z
  have hweak : ‖sphereWeakSolution d f‖^2 ≤ mu*‖f‖^2 := by
    simpa only [sphereL2Resolvent_inner,real_inner_self_eq_norm_sq] using hb
  have hc := real_inner_le_norm (sphereWeakSolution d f) z
  rw [sphereWeakSolution_spec,real_inner_self_eq_norm_sq] at hc
  have hsq := mul_self_le_mul_self (sq_nonneg ‖f‖) hc
  have hprod := mul_le_mul_of_nonneg_right hweak (sq_nonneg ‖z‖)
  have hn : 0 < ‖f‖^2 := sq_pos_of_pos (norm_pos_iff.mpr hz)
  have hmain : ‖f‖^2 ≤ mu*‖z‖^2 := (mul_le_mul_iff_left₀ hn).mp (by nlinarith)
  have hdiv : ‖f‖^2 / mu ≤ ‖z‖^2 := (div_le_iff₀ hmu).mpr (by nlinarith [hmain])
  rw [sphereCompletedDirichlet,real_inner_self_eq_norm_sq,real_inner_self_eq_norm_sq]
  change (mu⁻¹-1)*‖f‖^2 ≤ ‖z‖^2-‖f‖^2
  rw [div_eq_mul_inv] at hdiv
  nlinarith

theorem sphere_smooth_rayleigh_of_resolvent_bound (d : SphereEnergyData)
    (mu : ℝ) (hmu : 0 < mu) (u : SphereEnergySmooth d) (hu : u ≠ 0)
    (hb : inner ℝ (sphereL2Resolvent d (sphereEnergyL2Linear d u)) (sphereEnergyL2Linear d u) ≤
      mu * ‖sphereEnergyL2Linear d u‖^2) :
    mu⁻¹-1 ≤ sphereRayleighQuotient d.tensor d.density (SphereEnergySmooth.toSmooth d u) := by
  have hn : sphereEnergyL2Linear d u ≠ 0 := fun h ↦ hu ((sphereEnergyL2Linear_eq_zero_iff d u).mp h)
  have h := sphere_resolvent_quadratic_to_form_lower d mu hmu (sphereEnergyToCompletion d u)
    (by simpa only [sphereEnergyL2Map_coe] using hn) (by simpa only [sphereEnergyL2Map_coe] using hb)
  rw [sphereEnergyL2Map_coe,sphereCompletedDirichlet_coe,sphereEnergyL2Linear_norm_sq] at h
  apply (le_div_iff₀ _).mpr h
  rw [← sphereEnergyL2Linear_norm_sq]
  exact sq_pos_of_pos (norm_pos_iff.mpr hn)

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Spectral_SphereSmoothFrameRayleigh
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open MeasureTheory Set Yau.Analysis
noncomputable section

local instance sphereFrameRayleighMeasurable_r689318_1 : MeasurableSpace Base := borel Base
local instance sphereFrameRayleighBorel_r689318_1 : BorelSpace Base := ⟨rfl⟩
theorem sphere_smooth_frame_rayleigh_upper (d : SphereEnergyData) {N : ℕ}
    (u : Fin (N+1) → SphereEnergySmooth d) (mu : Fin (N+1) → ℝ)
    (ho : Orthonormal ℝ (fun i ↦ sphereEnergyL2Linear d (u i)))
    (hmu : ∀ i, 0 < mu i)
    (he : ∀ i, sphereL2Resolvent d (sphereEnergyL2Linear d (u i)) = mu i • sphereEnergyL2Linear d (u i))
    (hanti : Antitone mu) (x : SphereEnergySmooth d)
    (hx : x ∈ Submodule.span ℝ (range u)) (hx0 : x ≠ 0) :
    sphereRayleighQuotient d.tensor d.density (SphereEnergySmooth.toSmooth d x) ≤
      (mu (Fin.last N))⁻¹-1 := by
  classical
  let J := sphereEnergyL2Linear d
  let C := sphereEnergyToCompletion d
  have hvar (i) (v : SphereEnergySmooth d) :
      inner ℝ (C (u i)) (C v) = (mu i)⁻¹ * inner ℝ (J (u i)) (J v) := by
    simpa only [C,J,sphereEnergyL2Map_coe] using
      sphere_resolvent_smooth_variational d (mu i) (hmu i).ne' (u i) (he i) (C v)
  obtain ⟨c,hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).mp hx
  have hcoef (i) : inner ℝ (J (u i)) (J x) = c i := by
    rw [← hc,map_sum]
    simp only [map_smul]
    exact ho.inner_right_fintype c i
  have hnorm : ‖J x‖^2 = ∑ i, c i^2 := by
    rw [← real_inner_self_eq_norm_sq]
    nth_rw 1 [← hc]
    rw [map_sum]
    simp only [map_smul,sum_inner,inner_smul_left_eq_smul,smul_eq_mul,hcoef,pow_two]
  have henergy : ‖C x‖^2 = ∑ i, (mu i)⁻¹*c i^2 := by
    rw [← real_inner_self_eq_norm_sq]
    nth_rw 1 [← hc]
    rw [map_sum]
    simp only [map_smul,sum_inner,inner_smul_left_eq_smul,smul_eq_mul,hvar,hcoef]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hb : ‖C x‖^2 ≤ (mu (Fin.last N))⁻¹*‖J x‖^2 := by
    rw [hnorm,henergy,Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    exact mul_le_mul_of_nonneg_right (inv_anti₀ (hmu (Fin.last N)) (hanti (Fin.le_last i)))
      (sq_nonneg (c i))
  have hpos : 0 < ‖J x‖^2 := sq_pos_of_pos (norm_pos_iff.mpr
    (fun h ↦ hx0 ((sphereEnergyL2Linear_eq_zero_iff d x).mp h)))
  have hd : sphereDirichletForm d.tensor (SphereEnergySmooth.toSmooth d x) (SphereEnergySmooth.toSmooth d x) =
      ‖C x‖^2-‖J x‖^2 := by
    rw [← sphereCompletedDirichlet_coe,sphereCompletedDirichlet,sphereEnergyL2Map_coe,
      real_inner_self_eq_norm_sq,real_inner_self_eq_norm_sq]
  rw [sphereRayleighQuotient,hd,← sphereEnergyL2Linear_norm_sq]
  exact (div_le_iff₀ hpos).mpr (by nlinarith [hb])

theorem sphere_smooth_frame_rayleigh_minmax (d : SphereEnergyData) {N : ℕ}
    (u : Fin (N+1) → SphereEnergySmooth d) (mu : Fin (N+1) → ℝ)
    (ho : Orthonormal ℝ (fun i ↦ sphereEnergyL2Linear d (u i)))
    (hmu : ∀ i, 0 < mu i)
    (he : ∀ i, sphereL2Resolvent d (sphereEnergyL2Linear d (u i)) = mu i • sphereEnergyL2Linear d (u i))
    (hanti : Antitone mu)
    (hmax : ∀ i x, (∀ j, j < i → inner ℝ (sphereEnergyL2Linear d (u j)) x = 0) →
      inner ℝ (sphereL2Resolvent d x) x ≤ mu i * ‖x‖^2) :
    (∃ V : Submodule ℝ (SphereEnergySmooth d), FiniteDimensional ℝ V ∧ Module.finrank ℝ V = N+1 ∧
      ∀ x ∈ V, x ≠ 0 → sphereRayleighQuotient d.tensor d.density (SphereEnergySmooth.toSmooth d x) ≤
        (mu (Fin.last N))⁻¹-1) ∧
    (∀ V : Submodule ℝ (SphereEnergySmooth d), FiniteDimensional ℝ V → Module.finrank ℝ V = N+1 →
      ∃ x : SphereEnergySmooth d, x ∈ V ∧ x ≠ 0 ∧
        (mu (Fin.last N))⁻¹-1 ≤ sphereRayleighQuotient d.tensor d.density (SphereEnergySmooth.toSmooth d x)) := by
  constructor
  · refine ⟨Submodule.span ℝ (range u),FiniteDimensional.span_of_finite ℝ (finite_range u),?_,?_⟩
    · have hli : LinearIndependent ℝ u := LinearIndependent.of_comp (sphereEnergyL2Linear d) ho.linearIndependent
      simpa using finrank_span_eq_card hli
    · exact sphere_smooth_frame_rayleigh_upper d u mu ho hmu he hanti
  · intro V hV hdim
    let := hV
    obtain ⟨x,hx,hx0,horth⟩ := subspace_nonzero_linear_constraints V (by omega)
      (fun i : Fin N ↦ (innerSL ℝ (sphereEnergyL2Linear d (u i.castSucc))).toLinearMap.comp (sphereEnergyL2Linear d))
    refine ⟨x,hx,hx0,sphere_smooth_rayleigh_of_resolvent_bound d _ (hmu _) x hx0 ?_⟩
    apply hmax
    intro j hj
    exact horth ⟨j.val,hj⟩

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Spectral_SphereIndexedRayleigh
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open MeasureTheory Manifold Set
open scoped ContDiff
noncomputable section

local instance sphereIndexedRayleighMeasurable_r689318_1 : MeasurableSpace Base := borel Base
local instance sphereIndexedRayleighBorel_r689318_1 : BorelSpace Base := ⟨rfl⟩
theorem sphereIndexedEigenvalue_eq_of_minmax (d : SphereEnergyData) (N : ℕ) (a : ℝ)
    (hupper : a ∈ sphereRayleighUpperLevels d N)
    (hlower : ∀ V : Submodule ℝ sphereSmoothFunctions,
      FiniteDimensional ℝ V → Module.finrank ℝ V = N+1 →
      ∃ x : sphereSmoothFunctions, x ∈ V ∧ x ≠ 0 ∧ a ≤ sphereRayleighQuotient d.tensor d.density x) :
    sphereIndexedEigenvalue d N = a := by
  have hbelow : ∀ b ∈ sphereRayleighUpperLevels d N, a ≤ b := by
    rintro b ⟨V,hV,hdim,hb⟩
    obtain ⟨x,hx,hx0,hlo⟩ := hlower V hV hdim
    exact hlo.trans (hb x hx hx0)
  exact le_antisymm (csInf_le ⟨a,hbelow⟩ hupper) (le_csInf ⟨a,hupper⟩ hbelow)

theorem sphereIndexedEigenvalue_eq_frame (d : SphereEnergyData) {N : ℕ}
    (u : Fin (N+1) → SphereEnergySmooth d) (mu : Fin (N+1) → ℝ)
    (ho : Orthonormal ℝ (fun i ↦ sphereEnergyL2Linear d (u i)))
    (hmu : ∀ i, 0 < mu i)
    (he : ∀ i, sphereL2Resolvent d (sphereEnergyL2Linear d (u i)) = mu i • sphereEnergyL2Linear d (u i))
    (hanti : Antitone mu)
    (hmax : ∀ i x, (∀ j, j < i → inner ℝ (sphereEnergyL2Linear d (u j)) x = 0) →
      inner ℝ (sphereL2Resolvent d x) x ≤ mu i * ‖x‖^2) :
    sphereIndexedEigenvalue d N = (mu (Fin.last N))⁻¹-1 := by
  obtain ⟨hup,hlo⟩ := sphere_smooth_frame_rayleigh_minmax d u mu ho hmu he hanti hmax
  exact sphereIndexedEigenvalue_eq_of_minmax d N _ hup hlo

theorem sphereIndexedEigenvalue_smooth_realization (d : SphereEnergyData)
    (hrho : ∀ p : Base, ContDiff ℝ ∞ (fun x ↦ d.density (sphereChartCoordMap p x))) (N : ℕ) :
    ∃ u : SphereEnergySmooth d, u ≠ 0 ∧ ‖sphereEnergyL2Linear d u‖=1 ∧
      sphereL2Resolvent d (sphereEnergyL2Linear d u) =
        (sphereIndexedEigenvalue d N+1)⁻¹ • sphereEnergyL2Linear d u ∧
      ∀ v : SphereEnergyHilbert d,
        sphereCompletedDirichlet d (sphereEnergyToCompletion d u) v =
          sphereIndexedEigenvalue d N * inner ℝ (sphereEnergyL2Linear d u) (sphereEnergyL2Map d v) := by
  obtain ⟨u,mu,ho,he,hanti,hmax⟩ := sphere_resolvent_finite_smooth_frame d hrho (N+1)
  have heq := sphereIndexedEigenvalue_eq_frame d u mu ho (fun i ↦ (he i).1)
    (fun i ↦ (he i).2.2) hanti hmax
  let i := Fin.last N
  refine ⟨u i,?_,ho.norm_eq_one i,?_,?_⟩
  · intro hz
    have hn := ho.ne_zero i
    exact hn (by rw [hz,map_zero])
  · rw [heq,sub_add_cancel,inv_inv]
    exact (he i).2.2
  · intro v
    rw [sphereCompletedDirichlet,sphereEnergyL2Map_coe,
      sphere_resolvent_smooth_variational d (mu i) (he i).1.ne' (u i) (he i).2.2 v,heq]
    ring

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Charts_SphereIndexedFrameConsistency
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open MeasureTheory Manifold Set Yau.Analysis
open scoped ContDiff
noncomputable section

local instance sphereFrameConsistencyMeasurable_r689318_1 : MeasurableSpace Base := borel Base
local instance sphereFrameConsistencyBorel_r689318_1 : BorelSpace Base := ⟨rfl⟩
theorem sphereIndexedEigenvalue_eq_frame_index (d : SphereEnergyData) {N : ℕ}
    (u : Fin N → SphereEnergySmooth d) (mu : Fin N → ℝ)
    (ho : Orthonormal ℝ (fun i ↦ sphereEnergyL2Linear d (u i)))
    (hmu : ∀ i, 0 < mu i)
    (he : ∀ i, sphereL2Resolvent d (sphereEnergyL2Linear d (u i)) = mu i • sphereEnergyL2Linear d (u i))
    (hanti : Antitone mu)
    (hmax : ∀ i x, (∀ j, j < i → inner ℝ (sphereEnergyL2Linear d (u j)) x = 0) →
      inner ℝ (sphereL2Resolvent d x) x ≤ mu i * ‖x‖^2) (i : Fin N) :
    sphereIndexedEigenvalue d i.val = (mu i)⁻¹-1 := by
  have hle : i.val+1 ≤ N := i.isLt
  let c := Fin.castLE hle
  have h := sphereIndexedEigenvalue_eq_frame d (fun j ↦ u (c j)) (fun j ↦ mu (c j))
    (ho.comp c (Fin.castLE_injective hle)) (fun j ↦ hmu (c j)) (fun j ↦ he (c j))
    (fun j k hjk ↦ hanti hjk)
    (finite_frame_maximum_restrict hle (sphereL2Resolvent d) _ mu hmax)
  exact h

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Spectral_CompactEigenframeCardBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Analysis
open Set Metric
noncomputable section

theorem compact_eigenframe_card_bound {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (T : E →L[ℝ] E) (hT : IsCompactOperator T)
    (c : ℝ) (hc : 0 < c) :
    ∃ K : ℕ, ∀ (N : ℕ) (e : Fin N → E) (mu : Fin N → ℝ),
      Orthonormal ℝ e → (∀ i, T (e i)=mu i • e i) →
      (∀ i, c ≤ mu i) → N ≤ K := by
  classical
  have hcomp := hT.isCompact_closure_image_closedBall (f := T.toLinearMap) 1
  obtain ⟨t,ht,hcover⟩ := Metric.totallyBounded_iff.mp hcomp.totallyBounded (c/2) (half_pos hc)
  let := ht.fintype
  refine ⟨Fintype.card t,?_⟩
  intro N e mu ho he hmu
  have hnear (i : Fin N) : ∃ a : t, dist (T (e i)) a < c/2 := by
    have hx : T (e i) ∈ closure (T '' closedBall 0 1) :=
      subset_closure ⟨e i,by simpa using (ho.norm_eq_one i).le,rfl⟩
    have hxcover := hcover hx
    simp only [mem_iUnion,mem_ball] at hxcover
    obtain ⟨a,ha,hai⟩ := hxcover
    exact ⟨⟨a,ha⟩,hai⟩
  choose f hf using hnear
  have hinj : Function.Injective f := by
    intro i j hij
    by_contra hne
    have hinner : inner ℝ (e i) (T (e i)-T (e j)) = mu i := by
      rw [he i,he j,inner_sub_right,inner_smul_right,inner_smul_right,
        real_inner_self_eq_norm_sq,ho.norm_eq_one i,ho.inner_eq_zero hne]
      simp
    have hdist := real_inner_le_norm (e i) (T (e i)-T (e j))
    rw [ho.norm_eq_one i,one_mul,hinner,← dist_eq_norm] at hdist
    have hd : dist (T (e i)) (T (e j)) < c := by
      have h1 := hf i
      have h2 := hf j
      rw [← hij] at h2
      have hh := dist_triangle (T (e i)) (f i : E) (T (e j))
      rw [dist_comm (f i : E) (T (e j))] at hh
      linarith
    exact (not_lt_of_ge ((hmu i).trans hdist)) hd
  simpa using Fintype.card_le_of_injective f hinj

end
end Yau.Analysis

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Charts_SphereIndexedDivergence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open MeasureTheory Manifold Set Filter Yau.Analysis
open scoped ContDiff Topology
noncomputable section

local instance sphereIndexedDivergenceMeasurable_r689318_1 : MeasurableSpace Base := borel Base
local instance sphereIndexedDivergenceBorel_r689318_1 : BorelSpace Base := ⟨rfl⟩
theorem sphereIndexedEigenvalue_tendsto_atTop (d : SphereEnergyData)
    (hrho : ∀ p : Base, ContDiff ℝ ∞ (fun x ↦ d.density (sphereChartCoordMap p x))) :
    Tendsto (sphereIndexedEigenvalue d) atTop atTop := by
  apply tendsto_atTop.mpr
  intro a
  let b := max a 0+1
  have hb : 0 < b := by dsimp [b] <;> positivity
  obtain ⟨K,hK⟩ := compact_eigenframe_card_bound (sphereL2Resolvent d)
    (sphereL2Resolvent_compact d) (b+1)⁻¹ (inv_pos.mpr (by linarith))
  filter_upwards [eventually_ge_atTop K] with N hN
  obtain ⟨u,mu,ho,he,hanti,hmax⟩ := sphere_resolvent_finite_smooth_frame d hrho (N+1)
  have heq := sphereIndexedEigenvalue_eq_frame d u mu ho (fun i ↦ (he i).1)
    (fun i ↦ (he i).2.2) hanti hmax
  have hsmall : mu (Fin.last N) < (b+1)⁻¹ := by
    by_contra h
    have hlast : (b+1)⁻¹ ≤ mu (Fin.last N) := le_of_not_gt h
    have hcard := hK (N+1) (fun i ↦ sphereEnergyL2Linear d (u i)) mu ho
      (fun i ↦ (he i).2.2) (fun i ↦ hlast.trans (hanti (Fin.le_last i)))
    omega
  have hrecip : b+1 < (mu (Fin.last N))⁻¹ := by
    have h := inv_strictAnti₀ (he (Fin.last N)).1 hsmall
    simpa using h
  rw [heq]
  have hab : a < b := by dsimp [b] <;> linarith [le_max_left a 0]
  linarith

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Charts_SphereSmoothVariationalStrong
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Manifold Yau.Geometry MeasureTheory
open scoped ContDiff
noncomputable section

local instance sphereSmoothStrongMeasurable_r689318_1 : MeasurableSpace Base := borel Base
local instance sphereSmoothStrongBorel_r689318_1 : BorelSpace Base := ⟨rfl⟩
theorem sphere_smooth_variational_to_intrinsic
    (d : SphereEnergyData) (u : SphereEnergySmooth d) (lam : ℝ)
    (hweak : ∀ v : SphereEnergyHilbert d,
      sphereCompletedDirichlet d (sphereEnergyToCompletion d u) v =
        lam * inner ℝ (sphereEnergyL2Linear d u) (sphereEnergyL2Map d v)) :
    ∀ p z,
      -intrinsicWeightedChartOperator d.tensor d.density
          (SphereEnergySmooth.toSmooth d u) p z =
        lam * (SphereEnergySmooth.toSmooth d u : Base → ℝ)
          ((extChartAt (𝓡 4) p).symm z) := by
  let f : Base → ℝ := SphereEnergySmooth.toSmooth d u
  have hf : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ f := (SphereEnergySmooth.toSmooth d u).property
  intro p z
  let D := Yau.weightedDiv roundCoordDensity (sphereChartFlux d.tensor f p)
  have hD : Continuous D :=
    (Yau.weightedDiv_smooth roundCoordDensity_smooth (fun x ↦ (roundCoordDensity_pos x).ne')
      (intrinsicRealVector_smooth d.tensor d.smooth d.symm d.pos f hf p)).continuous
  let R : Yau.Jets.Coord → ℝ := fun x ↦ roundCoordDensity x *
    (D x + lam * d.density (sphereChartCoordMap p x) * f (sphereChartCoordMap p x))
  have hR : Continuous R := roundCoordDensity_smooth.continuous.mul
    (hD.add ((continuous_const.mul (d.continuous.comp (sphereChartCoordMap_smooth p).continuous)).mul
      (spherePullback_smooth f hf p).continuous))
  have htest : ∀ phi : Yau.Jets.Coord → ℝ, ContDiff ℝ ∞ phi → HasCompactSupport phi →
      (∫ x, phi x • R x) = 0 := by
    intro phi hphi hc
    obtain ⟨F,hF,_,hval⟩ := sphere_chart_scalar_extension p phi hphi hc
    let v : SphereEnergySmooth d := (⟨F,hF⟩ : sphereSmoothFunctions)
    have hcomp : F ∘ sphereChartCoordMap p = phi := funext hval
    have hgreen := (sphere_smooth_green_compact_chart d.tensor d.smooth d.symm d.pos
      F f hF hf p (hcomp ▸ hc)).2
    have hw := hweak (sphereEnergyToCompletion d v)
    rw [sphereCompletedDirichlet_coe,sphereEnergyL2Map_coe] at hw
    have hi : inner ℝ (sphereEnergyL2Linear d u) (sphereEnergyL2Linear d v) =
        sphereWeightedPairing d.density f F :=
      sphereWeightedToLp_inner d.density d.continuous (fun x ↦ (d.positive x).le) f F
        hf.continuous hF.continuous
    rw [hi] at hw
    change sphereDirichletForm d.tensor f F = _ at hw
    rw [sphereDirichletForm_symm d.tensor d.symm,hgreen] at hw
    simp only [hval] at hw
    rw [sphereWeightedPairing,sphereReferenceMeasure_integral_chart p] at hw
    simp only [roundChartDensity_coord_eq,hval] at hw
    have hI : Integrable (fun x ↦ roundCoordDensity x * phi x * D x) :=
      ((roundCoordDensity_smooth.continuous.mul hphi.continuous).mul hD).integrable_of_hasCompactSupport
        (hc.mul_left.mul_right)
    have hJ : Integrable (fun x ↦ roundCoordDensity x *
        (d.density (sphereChartCoordMap p x) * f (sphereChartCoordMap p x) * phi x)) :=
      (roundCoordDensity_smooth.continuous.mul
        (((d.continuous.comp (sphereChartCoordMap_smooth p).continuous).mul
          (spherePullback_smooth f hf p).continuous).mul hphi.continuous)).integrable_of_hasCompactSupport
            (hc.mul_left.mul_left)
    calc
      _ = ∫ x, (roundCoordDensity x * phi x * D x) +
          lam * (roundCoordDensity x *
            (d.density (sphereChartCoordMap p x) * f (sphereChartCoordMap p x) * phi x)) := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall (fun x ↦ by dsimp [R] <;> ring)
      _ = (∫ x, roundCoordDensity x * phi x * D x) +
          lam * (∫ x, roundCoordDensity x *
            (d.density (sphereChartCoordMap p x) * f (sphereChartCoordMap p x) * phi x)) := by
        rw [integral_add hI (hJ.const_mul lam),integral_const_mul]
      _ = 0 := by linarith
  have hae := ae_eq_zero_of_integral_contDiff_smul_eq_zero hR.locallyIntegrable htest
  have hzero : R = 0 := Measure.eq_of_ae_eq hae hR continuous_const
  let x := seedCoordEquiv.symm z
  have hx : seedCoordEquiv x = z := seedCoordEquiv.apply_symm_apply z
  have hres : D x + lam * d.density (sphereChartCoordMap p x) * f (sphereChartCoordMap p x) = 0 :=
    (mul_eq_zero.mp (congrFun hzero x)).resolve_left (roundCoordDensity_pos x).ne'
  rw [← hx,intrinsicRealOperator_pullback]
  change -((d.density (sphereChartCoordMap p x))⁻¹ * D x) = lam * f (sphereChartCoordMap p x)
  apply (mul_left_cancel₀ (d.positive (sphereChartCoordMap p x)).ne')
  rw [mul_neg,← mul_assoc,mul_inv_cancel₀ (d.positive (sphereChartCoordMap p x)).ne',one_mul]
  nlinarith

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Charts_SphereIndexedIntrinsic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Manifold MeasureTheory
open scoped ContDiff
noncomputable section

local instance sphereIndexedIntrinsicMeasurable_r689318_1 : MeasurableSpace Base := borel Base
local instance sphereIndexedIntrinsicBorel_r689318_1 : BorelSpace Base := ⟨rfl⟩
theorem sphereIndexedEigenvalue_intrinsic_realization (d : SphereEnergyData)
    (hrho : ∀ p : Base, ContDiff ℝ ∞ (fun x ↦ d.density (sphereChartCoordMap p x))) (N : ℕ) :
    ∃ u : Base → ℝ, ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ u ∧ u ≠ 0 ∧
      sphereWeightedPairing d.density u u = 1 ∧
      ∀ p z, -intrinsicWeightedChartOperator d.tensor d.density u p z =
        sphereIndexedEigenvalue d N * u ((extChartAt (𝓡 4) p).symm z) := by
  obtain ⟨u,hu,hn,_,hw⟩ := sphereIndexedEigenvalue_smooth_realization d hrho N
  refine ⟨SphereEnergySmooth.toSmooth d u,(SphereEnergySmooth.toSmooth d u).property,?_,?_,
    sphere_smooth_variational_to_intrinsic d u _ hw⟩
  · intro hz
    exact hu (Subtype.ext hz)
  · rw [← sphereEnergyL2Linear_norm_sq,hn,one_pow]

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Charts_SupportedFiniteAtlasBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Manifold Yau.Geometry Yau.Jets Set Metric
open scoped ContDiff Topology
noncomputable section
attribute [local instance] clmTopology clmAdd clmModule
attribute [local instance] intrinsicRoundPerturbationLocalInst3 intrinsicRoundPerturbationLocalInst4 intrinsicRoundPerturbationLocalInst5 intrinsicRoundPerturbationLocalInst6 intrinsicRoundPerturbationLocalInst7 intrinsicRoundPerturbationLocalInst8 intrinsicRoundPerturbationLocalInst9 intrinsicRoundPerturbationLocalInst10 intrinsicRoundPerturbationLocalInst11 intrinsicRoundPerturbationLocalInst12 intrinsicRoundPerturbationLocalInst13 intrinsicRoundPerturbationLocalInst14 intrinsicRoundPerturbationLocalInst15 intrinsicRoundPerturbationLocalInst16 intrinsicRoundPerturbationLocalInst17 intrinsicRoundPerturbationLocalInst18

lemma sphereAtlasCore_compact : IsCompact sphereAtlasCore :=
  (isCompact_closedBall _ _).image seedCoordEquiv.continuous

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Coefficients_SphereCoefficientDistanceLaws
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Manifold Yau.Geometry Set
open scoped ContDiff
noncomputable section
attribute [local instance] clmTopology clmAdd clmModule
attribute [local instance] intrinsicRoundPerturbationLocalInst3 intrinsicRoundPerturbationLocalInst4 intrinsicRoundPerturbationLocalInst5 intrinsicRoundPerturbationLocalInst6 intrinsicRoundPerturbationLocalInst7 intrinsicRoundPerturbationLocalInst8 intrinsicRoundPerturbationLocalInst9 intrinsicRoundPerturbationLocalInst10 intrinsicRoundPerturbationLocalInst11 intrinsicRoundPerturbationLocalInst12 intrinsicRoundPerturbationLocalInst13 intrinsicRoundPerturbationLocalInst14 intrinsicRoundPerturbationLocalInst15 intrinsicRoundPerturbationLocalInst16 intrinsicRoundPerturbationLocalInst17 intrinsicRoundPerturbationLocalInst18

lemma intrinsic_coefficient_chart_smooth (A : IntrinsicTensor) (hA : IntrinsicTensorSmooth A)
    (hs : ∀ x v w, A x v w = A x w v) (hp : ∀ x v, v ≠ 0 → 0 < A x v v)
    (rho : Base → ℝ) (hr : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ rho) (p : Base) :
    ContDiff ℝ ∞ (intrinsicChartCoefficient A rho p) :=
  contDiff_iff_contDiffAt.mpr (fun z ↦ intrinsicChartCoefficient_smoothAt A hA hs hp rho hr p
    (by rw [centeredSphereChart_target]; trivial))

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Spectral_SphereIndexedSpectralCoverage
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open MeasureTheory Manifold Set Filter Yau.Analysis
open scoped ContDiff Topology
noncomputable section

local instance sphereCoverageMeasurable_r689318_1 : MeasurableSpace Base := borel Base
local instance sphereCoverageBorel_r689318_1 : BorelSpace Base := ⟨rfl⟩
theorem sphere_resolvent_eigenvalue_index (d : SphereEnergyData)
    (hrho : ∀ p : Base, ContDiff ℝ ∞ (fun x ↦ d.density (sphereChartCoordMap p x)))
    (f : SphereWeightedL2 d) (hf : f ≠ 0) (a : ℝ) (hfa : sphereL2Resolvent d f=a • f) :
    ∃ N : ℕ, sphereIndexedEigenvalue d N = a⁻¹-1 := by
  have ha := (sphereL2Resolvent_eigenvalue_bounds d a f hf hfa).1
  obtain ⟨N,hN⟩ := ((sphereIndexedEigenvalue_tendsto_atTop d hrho).eventually
    (eventually_gt_atTop (a⁻¹-1))).exists
  obtain ⟨u,mu,ho,he,hanti,hmax⟩ := sphere_resolvent_finite_smooth_frame d hrho (N+1)
  have heq := sphereIndexedEigenvalue_eq_frame d u mu ho (fun i ↦ (he i).1)
    (fun i ↦ (he i).2.2) hanti hmax
  rw [heq] at hN
  have hlt : mu (Fin.last N) < a := (inv_lt_inv₀ ha (he (Fin.last N)).1).mp (by linarith)
  obtain ⟨i,hi⟩ := finite_eigenframe_captures_above_last (sphereL2Resolvent d)
    (sphereL2Resolvent_symmetric d) (fun i ↦ sphereEnergyL2Linear d (u i)) mu
    (fun i ↦ (he i).2.2) hmax f hf a hfa hlt
  refine ⟨i.val,?_⟩
  rw [sphereIndexedEigenvalue_eq_frame_index d u mu ho (fun i ↦ (he i).1)
    (fun i ↦ (he i).2.2) hanti hmax i,hi]

theorem sphere_smooth_intrinsic_eigenvalue_index (d : SphereEnergyData)
    (hr : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ d.density)
    (u : SphereEnergySmooth d) (hu : u ≠ 0) (lam : ℝ)
    (he : ∀ p z, -intrinsicWeightedChartOperator d.tensor d.density (SphereEnergySmooth.toSmooth d u) p z =
      lam*(SphereEnergySmooth.toSmooth d u : Base → ℝ) ((extChartAt (𝓡 4) p).symm z)) :
    ∃ N : ℕ, sphereIndexedEigenvalue d N=lam := by
  obtain ⟨hlam,hun,heu⟩ := sphere_smooth_intrinsic_eigen_to_resolvent d hr u hu lam he
  obtain ⟨N,hN⟩ := sphere_resolvent_eigenvalue_index d
    (fun p ↦ (hr.comp (sphereChartCoordMap_smooth p)).contDiff) _ hun (lam+1)⁻¹ heu
  exact ⟨N,by simpa using hN⟩

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Charts_SphereNormalizedSimpleUniqueness
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Manifold
open scoped ContDiff
noncomputable section

lemma sphereWeightedPairing_smul_self (rho u : Base → ℝ) (c : ℝ) :
    sphereWeightedPairing rho (c • u) (c • u)=c^2*sphereWeightedPairing rho u u := by
  rw [sphereWeightedPairing_smul_left,sphereWeightedPairing_symm rho u (c • u),sphereWeightedPairing_smul_left]
  ring

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Charts_SpherePositiveNormalization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Manifold
open scoped ContDiff
noncomputable section

theorem sphere_positive_normalization (d : SphereEnergyData) (u : Base → ℝ)
    (hu : Continuous u) (hne : u ≠ 0) :
    ∃ c : ℝ, 0 < c ∧ sphereWeightedPairing d.density (c • u) (c • u)=1 := by
  have hQ := sphereWeightedPairing_self_pos d.density u d.continuous d.positive hu hne
  let c := (Real.sqrt (sphereWeightedPairing d.density u u))⁻¹
  have hc : 0 < c := inv_pos.mpr (Real.sqrt_pos.mpr hQ)
  refine ⟨c,hc,?_⟩
  rw [sphereWeightedPairing_smul_self]
  dsimp [c]
  rw [inv_pow,Real.sq_sqrt hQ.le,inv_mul_cancel₀ hQ.ne']

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Coefficients_SphereCoefficientNormConvergence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Manifold Yau.Geometry Filter
open scoped ContDiff Topology
noncomputable section

theorem sphereCoefficientDistance_mono_order (P : Finset Base) (d b : SphereEnergyData)
    (hd : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ d.density) (hb : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ b.density)
    (J K : ℕ) (hJK : J ≤ K) :
    sphereCoefficientDistance P J d.tensor d.density b.tensor b.density ≤
      sphereCoefficientDistance P K d.tensor d.density b.tensor b.density :=
  finiteChartDerivativeSize_mono_order P sphereAtlasCore_compact hJK _
    (fun p _ ↦ (intrinsic_coefficient_chart_smooth b.tensor b.smooth b.symm b.pos b.density hb p).sub
      (intrinsic_coefficient_chart_smooth d.tensor d.smooth d.symm d.pos d.density hd p))

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Spectral_IntrinsicEigenfunctionLinearity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Manifold Yau.Geometry
open scoped ContDiff
noncomputable section

lemma intrinsicWeightedChartOperator_linear_combination (A : IntrinsicTensor)
    (hA : IntrinsicTensorSmooth A) (hs : ∀ p v w, A p v w = A p w v)
    (hp : ∀ p v, v ≠ 0 → 0 < A p v v) (rho : Base → ℝ)
    (u v : Base → ℝ) (hu : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ u) (hv : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ v)
    (c : ℝ) (p : Base) (z : BaseModel) :
    intrinsicWeightedChartOperator A rho (fun q ↦ c*u q+v q) p z =
      c*intrinsicWeightedChartOperator A rho u p z+intrinsicWeightedChartOperator A rho v p z := by
  obtain ⟨x,rfl⟩ := seedCoordEquiv.surjective z
  rw [intrinsicRealOperator_pullback,intrinsicRealOperator_pullback,intrinsicRealOperator_pullback]
  change (rho (sphereChartCoordMap p x))⁻¹ *
    realWeightedElliptic roundCoordDensity (intrinsicRealPrincipal A p)
      (fun y ↦ c*(u ∘ sphereChartCoordMap p) y+(v ∘ sphereChartCoordMap p) y) x =
    c*((rho (sphereChartCoordMap p x))⁻¹ * realWeightedElliptic roundCoordDensity
      (intrinsicRealPrincipal A p) (u ∘ sphereChartCoordMap p) x)+
    (rho (sphereChartCoordMap p x))⁻¹ * realWeightedElliptic roundCoordDensity
      (intrinsicRealPrincipal A p) (v ∘ sphereChartCoordMap p) x
  rw [realWeightedElliptic_linear_combination _ _ _ _ roundCoordDensity_smooth
    (intrinsicRealPrincipal_smooth A hA hs hp p) (spherePullback_smooth u hu p) (spherePullback_smooth v hv p)]
  ring

theorem intrinsic_eigenfunction_linear_combination (A : IntrinsicTensor)
    (hA : IntrinsicTensorSmooth A) (hs : ∀ p v w, A p v w = A p w v)
    (hp : ∀ p v, v ≠ 0 → 0 < A p v v) (rho : Base → ℝ)
    (u v : Base → ℝ) (hu : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ u) (hv : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ v)
    (lam : ℝ)
    (heu : ∀ p z, -intrinsicWeightedChartOperator A rho u p z = lam*u ((extChartAt (𝓡 4) p).symm z))
    (hev : ∀ p z, -intrinsicWeightedChartOperator A rho v p z = lam*v ((extChartAt (𝓡 4) p).symm z))
    (c : ℝ) : ∀ p z, -intrinsicWeightedChartOperator A rho (fun q ↦ c*u q+v q) p z =
      lam*(c*u ((extChartAt (𝓡 4) p).symm z)+v ((extChartAt (𝓡 4) p).symm z)) := by
  intro p z
  rw [intrinsicWeightedChartOperator_linear_combination A hA hs hp rho u v hu hv]
  linear_combination c*heu p z+hev p z

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Spectral_SphereOrthogonalEigenfunction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Manifold Yau.Geometry
open scoped ContDiff
noncomputable section

lemma intrinsic_eigenfunction_smul (A : IntrinsicTensor) (hA : IntrinsicTensorSmooth A)
    (hs : ∀ x alpha beta, A x alpha beta = A x beta alpha)
    (hp : ∀ x alpha, alpha ≠ 0 → 0 < A x alpha alpha) (rho : Base → ℝ)
    (u : Base → ℝ) (hu : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ u) (lam c : ℝ)
    (he : ∀ p z, -intrinsicWeightedChartOperator A rho u p z =
      lam*u ((extChartAt (𝓡 4) p).symm z)) :
    ∀ p z, -intrinsicWeightedChartOperator A rho (c • u) p z =
      lam*(c • u) ((extChartAt (𝓡 4) p).symm z) := by
  have hc := intrinsic_eigenfunction_linear_combination A hA hs hp rho u u hu hu lam he he (c-1)
  have heq : (fun q ↦ (c-1)*u q+u q) = c • u := by
    funext q
    simp only [Pi.smul_apply,smul_eq_mul]
    ring
  intro p z
  rw [← heq]
  exact hc p z

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Persistence_SphereSimpleOrientedPersistence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Manifold MeasureTheory Filter Metric Yau.Geometry
open scoped ContDiff Topology
noncomputable section

theorem sphere_finite_norm_simple_oriented_persistence_oai (d : SphereEnergyData)
    (hd : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ d.density)
    (u : Base → ℝ) (hu : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ u) (hu0 : u ≠ 0)
    (lam : ℝ) (hlam : 0 < lam)
    (he : ∀ p y, -intrinsicWeightedChartOperator d.tensor d.density u p y =
      lam*u ((extChartAt (𝓡 4) p).symm y))
    (hsimple : ∀ v : Base → ℝ, ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ v →
      (∀ p y, -intrinsicWeightedChartOperator d.tensor d.density v p y =
        lam*v ((extChartAt (𝓡 4) p).symm y)) → ∃ c : ℝ, v=c • u) :
    ∃ N : ℕ, sphereIndexedEigenvalue d N=lam ∧
      ∃ P : Finset Base,
        (∀ x : Base, ∃ p ∈ P, ∃ y ∈ sphereAtlasCore, (extChartAt (𝓡 4) p).symm y=x) ∧
        ∀ eps > 0, ∃ eta > 0, ∀ b : SphereEnergyData,
          ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ b.density →
          sphereCoefficientDistance P 8 d.tensor d.density b.tensor b.density < eta →
          sphereIndexedEigenvalue b N ∈ Set.Icc (lam/2) (2*lam) ∧
          ∃ v : Base → ℝ, ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ v ∧ v ≠ 0 ∧
            (∀ p y, -intrinsicWeightedChartOperator b.tensor b.density v p y =
              sphereIndexedEigenvalue b N*v ((extChartAt (𝓡 4) p).symm y)) ∧
            ∀ x, |v x-u x| < eps := by
  let U : SphereEnergySmooth d := (⟨u,hu⟩ : sphereSmoothFunctions)
  have hU : U ≠ 0 := fun h ↦ hu0 (congrArg (fun w : SphereEnergySmooth d ↦
    (SphereEnergySmooth.toSmooth d w : Base → ℝ)) h)
  obtain ⟨N,hN⟩ := sphere_smooth_intrinsic_eigenvalue_index d hd U hU lam he
  obtain ⟨c,hc,hcn⟩ := sphere_positive_normalization d u hu.continuous hu0
  have hS : ∀ v : Base → ℝ, ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ v →
      (∀ p y, -intrinsicWeightedChartOperator d.tensor d.density v p y =
        sphereIndexedEigenvalue d N*v ((extChartAt (𝓡 4) p).symm y)) →
      ∃ a : ℝ, v=a • (c • u) := by
    intro v hv hve
    obtain ⟨a,ha⟩ := hsimple v hv (by simpa only [hN] using hve)
    refine ⟨a/c,?_⟩
    rw [smul_smul,div_mul_cancel₀ a hc.ne']
    exact ha
  obtain ⟨P,hP,H⟩ := sphere_finite_norm_simple_uniform_persistence d hd N (c • u) hcn hS
  have hcore : ∀ x : Base, ∃ p ∈ P, ∃ y ∈ sphereAtlasCore, (extChartAt (𝓡 4) p).symm y=x := by
    intro x
    obtain ⟨p,hp,y,hy,hyx⟩ := hP x
    exact ⟨p,hp,seedCoordEquiv y,⟨y,(closedBall_subset_closedBall (by norm_num : (1:ℝ)/512 ≤ 1))
      (ball_subset_closedBall hy),rfl⟩,hyx⟩
  refine ⟨N,hN,P,hcore,?_⟩
  intro eps heps
  obtain ⟨eta₀,h₀,H₀⟩ := H (eps*c) (mul_pos heps hc)
  obtain ⟨eta₁,h₁,H₁⟩ := sphere_finite_norm_indexed_eigenvalue_continuity P hcore d hd N
    (lam/2) (by positivity)
  refine ⟨min eta₀ eta₁,lt_min h₀ h₁,?_⟩
  intro b hb hdist
  have hdist0 := (sphereCoefficientDistance_mono_order P d b hd hb 0 8 (by omega)).trans_lt
    (hdist.trans_le (min_le_right _ _))
  have hval := H₁ b hb hdist0
  rw [hN] at hval
  have hinterval : sphereIndexedEigenvalue b N ∈ Set.Icc (lam/2) (2*lam) :=
    ⟨by linarith [(abs_lt.mp hval).1],by linarith [(abs_lt.mp hval).2]⟩
  obtain ⟨v,hv,hv0,hvn,hve⟩ := sphereIndexedEigenvalue_intrinsic_realization b
    (fun p ↦ (hb.comp (sphereChartCoordMap_smooth p)).contDiff) N
  have hclose := H₀ b hb (hdist.trans_le (min_le_left _ _)) v hv hvn hve
  have hbranch : ∃ w : Base → ℝ, ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ w ∧ w ≠ 0 ∧
      (∀ p y, -intrinsicWeightedChartOperator b.tensor b.density w p y =
        sphereIndexedEigenvalue b N*w ((extChartAt (𝓡 4) p).symm y)) ∧
      ∀ x, |w x-(c • u) x| < eps*c := by
    rcases hclose with hp | hm
    · exact ⟨v,hv,hv0,hve,hp⟩
    · refine ⟨-v,hv.neg,neg_ne_zero.mpr hv0,?_,?_⟩
      · simpa only [neg_one_smul] using intrinsic_eigenfunction_smul b.tensor b.smooth b.symm b.pos
          b.density v hv (sphereIndexedEigenvalue b N) (-1) hve
      · intro x
        change |-v x-(c • u) x| < eps*c
        rw [show -v x-(c • u) x=-(v x+(c • u) x) by ring,abs_neg]
        exact hm x
  obtain ⟨w,hw,hw0,hwe,hwclose⟩ := hbranch
  refine ⟨hinterval,c⁻¹ • w,(contMDiff_const (c := c⁻¹)).mul hw,
    smul_ne_zero (inv_ne_zero hc.ne') hw0,
    intrinsic_eigenfunction_smul b.tensor b.smooth b.symm b.pos b.density w hw
      (sphereIndexedEigenvalue b N) c⁻¹ hwe,?_⟩
  intro x
  have hid : (c⁻¹ • w) x-u x=c⁻¹*(w x-(c • u) x) := by
    simp only [Pi.smul_apply,smul_eq_mul]
    field_simp
  rw [hid,abs_mul,abs_of_pos (inv_pos.mpr hc)]
  calc
    c⁻¹*|w x-(c • u) x| < c⁻¹*(eps*c) := mul_lt_mul_of_pos_left (hwclose x) (inv_pos.mpr hc)
    _ = eps := by field_simp

end
end Yau.Target

end OAI
end

theorem solution : type_of% @OAI.Yau.Target.sphere_finite_norm_simple_oriented_persistence_oai := @OAI.Yau.Target.sphere_finite_norm_simple_oriented_persistence_oai
