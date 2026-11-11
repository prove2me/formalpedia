-- Prove2me | solution 1 for OAI.Yau.Target.sphere_finite_norm_C1_intrinsic_limit
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T00:34:16.424831+00:00
-- url     : https://prove2.me/submissions/d57bc4aa-b9f7-48c3-a1bd-759ffade67ce

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
import Theorems.Thm_OAI_Yau_Target_sphere_eigen_global_representative

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

theorem compact_matrix_uniform_ellipticity (B : _root_.OAI.Yau.Jets.Coord → Matrix (Fin 4) (Fin 4) ℝ)
    (hB : ∀ i j, Continuous (fun x ↦ B x i j))
    (hp : ∀ x, (B x).PosDef) {K : Set _root_.OAI.Yau.Jets.Coord} (hK : IsCompact K) :
    ∃ c > 0, ∃ C > 0, ∀ x ∈ K, ∀ v : _root_.OAI.Yau.Jets.Coord,
      c*(∑ i, v i^2) ≤ (∑ i, ∑ j, v i*B x i j*v j) ∧
      (∑ i, ∑ j, v i*B x i j*v j) ≤ C*(∑ i, v i^2) := by
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let g : K → _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ := fun x ↦ coordMatrixForm (B x)
  obtain ⟨c,hc,C,hC,hbound⟩ := uniform_metric_coercivity g
    ((coordMatrixForm_continuous B hB).comp continuous_subtype_val)
    (fun x v hv ↦ coordMatrixForm_positive (B x) (hp x) v hv)
  refine ⟨c/4,by positivity,C,hC,?_⟩
  intro x hx v
  have hb := hbound ⟨x,hx⟩
  have hlo := hb.2 v
  have hhi : g ⟨x,hx⟩ v v ≤ C*‖v‖^2 := calc
    g ⟨x,hx⟩ v v ≤ |g ⟨x,hx⟩ v v| := le_abs_self _
    _ ≤ ‖g ⟨x,hx⟩‖*‖v‖*‖v‖ := bilinear_pairing_bound _ v v
    _ ≤ C*‖v‖^2 := by nlinarith [mul_le_mul_of_nonneg_right hb.1 (sq_nonneg ‖v‖)]
  change c*‖v‖^2 ≤ coordMatrixForm (B x) v v at hlo
  change coordMatrixForm (B x) v v ≤ C*‖v‖^2 at hhi
  rw [coordMatrixForm_apply] at hlo hhi
  constructor
  · nlinarith [mul_le_mul_of_nonneg_left (coord_sum_sq_le_four_norm_sq v) hc.le]
  · exact hhi.trans (mul_le_mul_of_nonneg_left (coord_norm_sq_le_sum_sq v) hC.le)

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Coefficients_MatrixCoefficientMap
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

lemma intrinsicRealPrincipal_posDef (A : IntrinsicTensor)
    (hs : ∀ p v w, A p v w = A p w v) (hp : ∀ p v, v ≠ 0 → 0 < A p v v)
    (p : Base) (x : Yau.Jets.Coord) : (intrinsicRealPrincipal A p x).PosDef :=
  intrinsicSphereChartTensor_posDef A hs hp p (by rw [centeredSphereChart_target]; trivial)

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
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_IntrinsicRealEllipticity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Manifold Matrix Yau.Geometry
open scoped ContDiff
noncomputable section

theorem intrinsic_real_uniform_ellipticity (A : IntrinsicTensor) (hA : IntrinsicTensorSmooth A)
    (hs : ∀ p v w, A p v w = A p w v) (hp : ∀ p v, v ≠ 0 → 0 < A p v v)
    (p : Base) {K : Set Yau.Jets.Coord} (hK : IsCompact K) :
    ∃ c > 0, ∃ C > 0, ∀ x ∈ K, ∀ xi : Fin 4 → ℝ,
      c*(∑ i, xi i^2) ≤ (∑ i, ∑ j, xi i*intrinsicRealPrincipal A p x i j*xi j) ∧
      (∑ i, ∑ j, xi i*intrinsicRealPrincipal A p x i j*xi j) ≤ C*(∑ i, xi i^2) :=
  compact_matrix_uniform_ellipticity (intrinsicRealPrincipal A p)
    (fun i j ↦ (intrinsicRealPrincipal_smooth A hA hs hp p i j).continuous)
    (intrinsicRealPrincipal_posDef A hs hp p) hK

end
end Yau.Target

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
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_RealPartialJetLinearity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Analysis
open scoped ContDiff
noncomputable section

theorem partialJet_sub {I : Type*} [Fintype I] [DecidableEq I]
    (f g : (I → ℝ) → ℝ) (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (ds : List I) (x : I → ℝ) :
    partialJet (fun y ↦ f y-g y) ds x = partialJet f ds x-partialJet g ds x := by
  rw [partialJet_eq_iterated _ (hf.sub hg),partialJet_eq_iterated f hf,partialJet_eq_iterated g hg]
  rw [fun_iteratedFDeriv_sub_apply (hf.of_le (by exact_mod_cast
    (show (ds.length:ℕ∞) ≤ ⊤ from le_top))).contDiffAt
    (hg.of_le (by exact_mod_cast (show (ds.length:ℕ∞) ≤ ⊤ from le_top))).contDiffAt]
  rfl

end
end Yau.Analysis

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Charts_SphereFiniteChartEnergyUpper
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Manifold Yau.Geometry Yau.Analysis MeasureTheory Metric Set
open scoped ContDiff
noncomputable section

local instance sphereEnergyUpperMeasurable_r706c04_1 : MeasurableSpace Base := borel Base
local instance sphereEnergyUpperBorel_r706c04_1 : BorelSpace Base := ⟨rfl⟩
theorem sphere_finite_chart_energy_upper (d : SphereEnergyData) (P : Finset Base) (r : ℝ)
    (hcover : ∀ x : Base, ∃ p ∈ P, ∃ z ∈ ball (0 : Yau.Jets.Coord) r, sphereChartCoordMap p z=x) :
    ∃ K > 0, ∀ (u : SphereEnergySmooth d) (eps : ℝ), 0 ≤ eps →
      (∀ x : Base, |(SphereEnergySmooth.toSmooth d u : Base → ℝ) x| ≤ eps) →
      (∀ p ∈ P, ∀ x ∈ ball (0 : Yau.Jets.Coord) r, ∀ i : Fin 4,
        |partialJet ((SphereEnergySmooth.toSmooth d u : Base → ℝ) ∘ sphereChartCoordMap p) [i] x| ≤ eps) →
      ‖u‖^2 ≤ K*eps^2 := by
  choose c hc C hC hCb using (fun p : P ↦ intrinsic_real_uniform_ellipticity
    d.tensor d.smooth d.symm d.pos p (isCompact_closedBall (0 : Yau.Jets.Coord) r))
  obtain ⟨B,hB,hBC⟩ := Yau.real_finite_positive_majorant C
  obtain ⟨R,hR,hRb⟩ := (isCompact_univ.image d.continuous).isBounded.exists_pos_norm_le
  let I := ∫ _x : Base, (1 : ℝ) ∂sphereReferenceMeasure
  have hI : 0 ≤ I := integral_nonneg (fun _ ↦ zero_le_one)
  let K := (R+4*B)*I+1
  have hK : 0 < K := by dsimp [K] <;> positivity
  refine ⟨K,hK,?_⟩
  intro u eps heps hu hdu
  let f : Base → ℝ := SphereEnergySmooth.toSmooth d u
  have hf : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ f := (SphereEnergySmooth.toSmooth d u).property
  have hm (x : Base) : d.density x*f x*f x ≤ R*eps^2 := by
    have hx : d.density x ≤ R := (le_abs_self _).trans (hRb _ ⟨x,mem_univ x,rfl⟩)
    have hf2 : f x^2 ≤ eps^2 := by simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) heps).mpr (hu x)
    nlinarith [mul_le_mul hx hf2 (sq_nonneg (f x)) hR.le]
  have he (x : Base) : d.tensor x (sphereDifferential f x) (sphereDifferential f x) ≤ 4*B*eps^2 := by
    obtain ⟨p,hp,z,hz,rfl⟩ := hcover x
    rw [intrinsic_differential_pair_chart d.tensor f f hf hf]
    have hs : (∑ i : Fin 4, (Yau.coordPartial (f ∘ sphereChartCoordMap p) z i)^2) ≤ 4*eps^2 := by
      calc
        _ ≤ ∑ _i : Fin 4, eps^2 := Finset.sum_le_sum (fun i _ ↦ by
          simpa only [sq_abs,partialJet,Yau.coordPartial,f] using (sq_le_sq₀ (abs_nonneg _) heps).mpr (hdu p hp z hz i))
        _ = _ := by simp
    have hb := (hCb ⟨p,hp⟩ z (ball_subset_closedBall hz) (fun i ↦ Yau.coordPartial (f ∘ sphereChartCoordMap p) z i)).2
    exact hb.trans ((mul_le_mul (hBC ⟨p,hp⟩) hs
      (Finset.sum_nonneg (fun _ _ ↦ sq_nonneg _)) hB.le).trans_eq (by ring))
  have hiM := sphereWeightedPairing_integrable d.density f f d.continuous hf.continuous hf.continuous
  have hiE := intrinsic_differential_pair_integrable d.tensor d.smooth d.symm d.pos f f hf hf
  let := sphereReferenceMeasure_finite
  calc
    ‖u‖^2 = ∫ x, d.density x*f x*f x+d.tensor x (sphereDifferential f x) (sphereDifferential f x)
        ∂sphereReferenceMeasure := by
      rw [SphereEnergySmooth.norm_sq,sphereWeightedPairing,sphereDirichletForm,integral_add hiM hiE]
    _ ≤ ∫ _x : Base, ((R+4*B)*eps^2)*1 ∂sphereReferenceMeasure := by
      apply integral_mono (hiM.add hiE) (integrable_const _)
      intro x
      change d.density x*f x*f x+d.tensor x (sphereDifferential f x) (sphereDifferential f x) ≤ (R+4*B)*eps^2*1
      nlinarith [hm x,he x]
    _ = ((R+4*B)*eps^2)*I := by rw [integral_const_mul]
    _ ≤ K*eps^2 := by dsimp [K] <;> nlinarith [sq_nonneg eps]

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Charts_SphereC1EnergyConvergence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Manifold Yau.Geometry Yau.Analysis Filter Metric
open scoped ContDiff Topology
noncomputable section

theorem sphere_C1_energy_cauchy (d : SphereEnergyData) (P : Finset Base) (r : ℝ)
    (hcover : ∀ x : Base, ∃ p ∈ P, ∃ z ∈ ball (0 : Yau.Jets.Coord) r, sphereChartCoordMap p z=x)
    (u : ℕ → SphereEnergySmooth d) (v : Base → ℝ)
    (ht : TendstoUniformly (fun j ↦ (SphereEnergySmooth.toSmooth d (u j) : Base → ℝ)) v atTop)
    (hjet : ∀ p ∈ P, ∀ i : Fin 4,
      TendstoUniformlyOn
        (fun j ↦ partialJet ((SphereEnergySmooth.toSmooth d (u j) : Base → ℝ) ∘ sphereChartCoordMap p) [i])
        (partialJet (v ∘ sphereChartCoordMap p) [i]) atTop (ball 0 r)) :
    CauchySeq u := by
  obtain ⟨K,hK,H⟩ := sphere_finite_chart_energy_upper d P r hcover
  apply Metric.cauchySeq_iff.mpr
  intro eps heps
  obtain ⟨a,ha,haeps⟩ := exists_pos_mul_lt (sq_pos_of_pos heps) K
  let delta := min a 1
  have hdelta : 0 < delta := lt_min ha zero_lt_one
  have hd1 : delta ≤ 1 := min_le_right _ _
  have hda : delta ≤ a := min_le_left _ _
  have hsmall : K*delta^2 < eps^2 := by
    have hs : delta^2 ≤ delta := by nlinarith
    exact ((mul_le_mul_of_nonneg_left hs hK.le).trans
      (mul_le_mul_of_nonneg_left hda hK.le)).trans_lt haeps
  have hvals := Metric.tendstoUniformly_iff.mp ht (delta/2) (by positivity)
  have hder (p : P) (i : Fin 4) := Metric.tendstoUniformlyOn_iff.mp
    (hjet p p.property i) (delta/2) (by positivity)
  have hall : ∀ᶠ j in atTop, (∀ x, dist (v x) ((SphereEnergySmooth.toSmooth d (u j) : Base → ℝ) x) < delta/2) ∧
      ∀ p : P, ∀ i : Fin 4, ∀ x ∈ ball (0 : Yau.Jets.Coord) r,
        dist (partialJet (v ∘ sphereChartCoordMap p) [i] x)
          (partialJet ((SphereEnergySmooth.toSmooth d (u j) : Base → ℝ) ∘ sphereChartCoordMap p) [i] x) < delta/2 :=
    hvals.and (Filter.eventually_all.mpr (fun p ↦ Filter.eventually_all.mpr (hder p)))
  obtain ⟨M,hM⟩ := eventually_atTop.mp hall
  refine ⟨M,fun j hj k hk ↦ ?_⟩
  have hv : ∀ x : Base, |(SphereEnergySmooth.toSmooth d (u j-u k) : Base → ℝ) x| ≤ delta := by
    intro x
    have h1 := abs_lt.mp (by simpa only [Real.dist_eq] using (hM j hj).1 x)
    have h2 := abs_lt.mp (by simpa only [Real.dist_eq] using (hM k hk).1 x)
    change |(SphereEnergySmooth.toSmooth d (u j) : Base → ℝ) x-
      (SphereEnergySmooth.toSmooth d (u k) : Base → ℝ) x| ≤ delta
    exact abs_le.mpr ⟨by linarith,by linarith⟩
  have hderiv : ∀ p ∈ P, ∀ x ∈ ball (0 : Yau.Jets.Coord) r, ∀ i : Fin 4,
      |partialJet ((SphereEnergySmooth.toSmooth d (u j-u k) : Base → ℝ) ∘ sphereChartCoordMap p) [i] x| ≤ delta := by
    intro p hp x hx i
    have h1 := abs_lt.mp (by simpa only [Real.dist_eq] using (hM j hj).2 ⟨p,hp⟩ i x hx)
    have h2 := abs_lt.mp (by simpa only [Real.dist_eq] using (hM k hk).2 ⟨p,hp⟩ i x hx)
    change |partialJet (fun y ↦ ((SphereEnergySmooth.toSmooth d (u j) : Base → ℝ) ∘ sphereChartCoordMap p) y-
      ((SphereEnergySmooth.toSmooth d (u k) : Base → ℝ) ∘ sphereChartCoordMap p) y) [i] x| ≤ delta
    rw [partialJet_sub _ _ (spherePullback_smooth _ (SphereEnergySmooth.toSmooth d (u j)).property p)
      (spherePullback_smooth _ (SphereEnergySmooth.toSmooth d (u k)).property p)]
    exact abs_le.mpr ⟨by linarith,by linarith⟩
  have hnorm := (H (u j-u k) delta hdelta.le hv hderiv).trans_lt hsmall
  rw [dist_eq_norm]
  nlinarith [norm_nonneg (u j-u k)]

theorem sphere_C1_energy_completion_limit (d : SphereEnergyData) (P : Finset Base) (r : ℝ)
    (hcover : ∀ x : Base, ∃ p ∈ P, ∃ z ∈ ball (0 : Yau.Jets.Coord) r, sphereChartCoordMap p z=x)
    (u : ℕ → SphereEnergySmooth d) (v : Base → ℝ)
    (ht : TendstoUniformly (fun j ↦ (SphereEnergySmooth.toSmooth d (u j) : Base → ℝ)) v atTop)
    (hjet : ∀ p ∈ P, ∀ i : Fin 4,
      TendstoUniformlyOn
        (fun j ↦ partialJet ((SphereEnergySmooth.toSmooth d (u j) : Base → ℝ) ∘ sphereChartCoordMap p) [i])
        (partialJet (v ∘ sphereChartCoordMap p) [i]) atTop (ball 0 r)) :
    ∃ z : SphereEnergyHilbert d, Tendsto (fun j ↦ sphereEnergyToCompletion d (u j)) atTop (𝓝 z) := by
  apply cauchySeq_tendsto_of_complete
  exact (sphereEnergyToCompletion d).isometry.uniformContinuous.comp_cauchySeq
    (sphere_C1_energy_cauchy d P r hcover u v ht hjet)

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
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_CompactContravariantComparison
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Set Yau.Jets
noncomputable section
variable {T E : Type*} [TopologicalSpace T] [CompactSpace T]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

lemma compact_contravariant_margin (c : T → CoefficientPoint E) (hc : Continuous c)
    (hp : ∀ t (alpha : E →L[ℝ] ℝ), alpha ≠ 0 → 0 < alpha ((c t).1 alpha))
    (hr : ∀ t, 0 < (c t).2) :
    ∃ m > 0, (∀ t (alpha : E →L[ℝ] ℝ), m*‖alpha‖^2 ≤ alpha ((c t).1 alpha)) ∧ ∀ t, m ≤ (c t).2 := by
  have hcont : Continuous (fun z : T × (E →L[ℝ] ℝ) ↦ z.2 ((c z.1).1 z.2)) :=
    continuous_snd.clm_apply ((hc.fst.comp continuous_fst).clm_apply continuous_snd)
  obtain ⟨a,ha,_,_,hbound⟩ := compact_positive_bounds
    (isCompact_univ.prod (isCompact_sphere (0 : E →L[ℝ] ℝ) 1)) _ hcont.continuousOn
    (fun z hz ↦ hp z.1 z.2 (by intro he; simpa [he] using hz.2))
  have hco (t : T) (alpha : E →L[ℝ] ℝ) : a*‖alpha‖^2 ≤ alpha ((c t).1 alpha) := by
    by_cases hz : alpha=0
    · simp [hz]
    have hn : 0 < ‖alpha‖ := norm_pos_iff.mpr hz
    have hu : ‖(‖alpha‖⁻¹:ℝ) • alpha‖=1 := by
      rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hn),inv_mul_cancel₀ hn.ne']
    have hh := (hbound (t,(‖alpha‖⁻¹:ℝ) • alpha)
      ⟨mem_univ _,by simpa only [Metric.mem_sphere,dist_zero_right] using hu⟩).1
    simp only [map_smul,smul_apply,smul_eq_mul] at hh
    have hmul := mul_le_mul_of_nonneg_left hh (sq_nonneg ‖alpha‖)
    have he : ‖alpha‖^2*(‖alpha‖⁻¹*(‖alpha‖⁻¹*alpha ((c t).1 alpha))) =
        alpha ((c t).1 alpha) := by field_simp
    rw [he] at hmul
    nlinarith
  obtain ⟨b,hb,_,_,hbr⟩ := compact_positive_bounds isCompact_univ _ hc.snd.continuousOn
    (fun t _ ↦ hr t)
  exact ⟨min a b,lt_min ha hb,
    fun t alpha ↦ (mul_le_mul_of_nonneg_right (min_le_left _ _) (sq_nonneg ‖alpha‖)).trans (hco t alpha),
    fun t ↦ (min_le_right _ _).trans (hbr t (mem_univ t)).1⟩

omit [FiniteDimensional ℝ E] in
lemma coefficient_relative_comparison (c d : CoefficientPoint E) {m eps : ℝ}
    (_hm : 0 < m) (heps : 0 ≤ eps)
    (hc : ∀ alpha : E →L[ℝ] ℝ, m*‖alpha‖^2 ≤ alpha (c.1 alpha)) (hr : m ≤ c.2)
    (hd : ‖d-c‖ ≤ eps*m) :
    (∀ alpha : E →L[ℝ] ℝ, |alpha (d.1 alpha)-alpha (c.1 alpha)| ≤ eps*alpha (c.1 alpha)) ∧
    |d.2-c.2| ≤ eps*c.2 := by
  have hop : ‖d.1-c.1‖ ≤ eps*m := (norm_fst_le (d-c)).trans hd
  constructor
  · intro alpha
    have hn : |alpha (d.1 alpha)-alpha (c.1 alpha)| ≤ ‖d.1-c.1‖*‖alpha‖^2 := by
      calc
        _ = ‖alpha ((d.1-c.1) alpha)‖ := by rw [sub_apply,map_sub,Real.norm_eq_abs]
        _ ≤ ‖alpha‖*‖(d.1-c.1) alpha‖ := alpha.le_opNorm _
        _ ≤ ‖alpha‖*(‖d.1-c.1‖*‖alpha‖) :=
          mul_le_mul_of_nonneg_left ((d.1-c.1).le_opNorm alpha) (norm_nonneg alpha)
        _ = _ := by ring
    exact hn.trans ((mul_le_mul_of_nonneg_right hop (sq_nonneg ‖alpha‖)).trans
      (by nlinarith [mul_le_mul_of_nonneg_left (hc alpha) heps]))
  · exact (show |d.2-c.2| ≤ eps*m by
      have h := (norm_snd_le (d-c)).trans hd
      change ‖d.2-c.2‖ ≤ eps*m at h
      rwa [Real.norm_eq_abs] at h).trans
      (mul_le_mul_of_nonneg_left hr heps)

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Coefficients_SphereCoefficientFormComparison
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
attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace normedSpaceTangentSpaceVectorSpace

lemma sphere_finite_atlas_coercivity (P : Finset Base)
    (A : IntrinsicTensor) (hA : IntrinsicTensorSmooth A)
    (hs : ∀ x alpha beta, A x alpha beta = A x beta alpha)
    (hp : ∀ x alpha, alpha ≠ 0 → 0 < A x alpha alpha)
    (rho : Base → ℝ) (hr : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ rho) (hrp : ∀ x, 0 < rho x) :
    ∃ m > 0, ∀ p ∈ P, ∀ z ∈ sphereAtlasCore,
      (∀ alpha : BaseModel →L[ℝ] ℝ,
        m*‖alpha‖^2 ≤ alpha ((intrinsicChartCoefficient A rho p z).1 alpha)) ∧
      m ≤ (intrinsicChartCoefficient A rho p z).2 := by
  classical
  let : CompactSpace sphereAtlasCore := isCompact_iff_compactSpace.mp sphereAtlasCore_compact
  let c : {p // p ∈ P} × sphereAtlasCore → CoefficientPoint BaseModel :=
    fun t ↦ intrinsicChartCoefficient A rho t.1.val t.2.val
  have hc : Continuous c := continuous_prod_of_discrete_left.mpr
    (fun p ↦ (intrinsic_coefficient_chart_smooth A hA hs hp rho hr p.val).continuous.comp continuous_subtype_val)
  obtain ⟨m,hm,hbound,hrbound⟩ := compact_contravariant_margin c hc
    (fun t alpha hn ↦ intrinsicChartCoefficient_positive A hs hp rho t.1.val
      (by rw [centeredSphereChart_target]; trivial) alpha hn)
    (fun t ↦ hrp ((extChartAt (𝓡 4) t.1.val).symm t.2.val))
  exact ⟨m,hm,fun p hp z hz ↦ ⟨hbound (⟨p,hp⟩,⟨z,hz⟩),hrbound (⟨p,hp⟩,⟨z,hz⟩)⟩⟩

lemma sphereCoefficientDistance_value_bound (P : Finset Base) (J : ℕ)
    (A B : IntrinsicTensor) (rho sigma : Base → ℝ)
    (hA : ∀ p ∈ P, ContDiff ℝ ∞ (intrinsicChartCoefficient A rho p))
    (hB : ∀ p ∈ P, ContDiff ℝ ∞ (intrinsicChartCoefficient B sigma p))
    (p : Base) (hp : p ∈ P) (z : BaseModel) (hz : z ∈ sphereAtlasCore) :
    ‖intrinsicChartCoefficient B sigma p z-intrinsicChartCoefficient A rho p z‖ ≤
      sphereCoefficientDistance P J A rho B sigma := by
  simpa only [sphereCoefficientDistance,norm_iteratedFDeriv_zero] using norm_le_finiteChartDerivativeSize P sphereAtlasCore_compact J
    (fun p z ↦ intrinsicChartCoefficient B sigma p z-intrinsicChartCoefficient A rho p z)
    (fun p hp ↦ (hB p hp).sub (hA p hp)) p hp 0 (Nat.zero_le _) z hz

theorem sphere_coefficient_relative_form_comparison (P : Finset Base)
    (hcover : ∀ x : Base, ∃ p ∈ P, ∃ z ∈ sphereAtlasCore, (extChartAt (𝓡 4) p).symm z = x)
    (A : IntrinsicTensor) (hA : IntrinsicTensorSmooth A)
    (hs : ∀ x alpha beta, A x alpha beta = A x beta alpha)
    (hp : ∀ x alpha, alpha ≠ 0 → 0 < A x alpha alpha)
    (rho : Base → ℝ) (hr : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ rho) (hrp : ∀ x, 0 < rho x)
    (eps : ℝ) (heps : 0 < eps) :
    ∃ eta > 0, ∀ (B : IntrinsicTensor) (sigma : Base → ℝ),
      IntrinsicTensorSmooth B → (∀ x alpha beta, B x alpha beta = B x beta alpha) →
      (∀ x alpha, alpha ≠ 0 → 0 < B x alpha alpha) →
      ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ sigma →
      sphereCoefficientDistance P 0 A rho B sigma < eta →
      ∀ x : Base, (∀ alpha : SphereCotangent x,
        |B x alpha alpha-A x alpha alpha| ≤ eps*A x alpha alpha) ∧
        |sigma x-rho x| ≤ eps*rho x := by
  obtain ⟨m,hm,hmargin⟩ := sphere_finite_atlas_coercivity P A hA hs hp rho hr hrp
  refine ⟨eps*m,mul_pos heps hm,?_⟩
  intro B sigma hB hBs hBp hsig hdist x
  obtain ⟨p,hpP,z,hz,rfl⟩ := hcover x
  have hcmp := coefficient_relative_comparison (intrinsicChartCoefficient A rho p z)
    (intrinsicChartCoefficient B sigma p z) hm heps.le (hmargin p hpP z hz).1 (hmargin p hpP z hz).2
    ((sphereCoefficientDistance_value_bound P 0 A B rho sigma
      (fun p _ ↦ intrinsic_coefficient_chart_smooth A hA hs hp rho hr p)
      (fun p _ ↦ intrinsic_coefficient_chart_smooth B hB hBs hBp sigma hsig p) p hpP z hz).trans hdist.le)
  refine ⟨?_,hcmp.2⟩
  intro alpha
  let beta : BaseModel →L[ℝ] ℝ := alpha.comp
    (mfderiv 𝓘(ℝ,BaseModel) (𝓡 4) (extChartAt (𝓡 4) p).symm z)
  have hrep : sphereCoordinateCovector p z (baseCovectorCoordinates beta) = alpha := by
    symm
    apply sphereCoordinateCovector_unique p (by rw [centeredSphereChart_target]; trivial)
    intro w
    change beta (WithLp.toLp 2 w) = _
    exact baseCovectorCoordinates_apply beta _
  have h := hcmp.1 beta
  rw [intrinsicChartCoefficient_pair B sigma,intrinsicChartCoefficient_pair A rho,hrep] at h
  exact h

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Charts_SphereIntegratedFormComparison
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Manifold Yau.Geometry MeasureTheory
open scoped ContDiff
noncomputable section

theorem sphere_integrated_form_comparison
    (A B : IntrinsicTensor) (hA : IntrinsicTensorSmooth A) (hB : IntrinsicTensorSmooth B)
    (hAs : ∀ x alpha beta, A x alpha beta = A x beta alpha)
    (hBs : ∀ x alpha beta, B x alpha beta = B x beta alpha)
    (hAp : ∀ x alpha, alpha ≠ 0 → 0 < A x alpha alpha)
    (hBp : ∀ x alpha, alpha ≠ 0 → 0 < B x alpha alpha)
    (rho sigma : Base → ℝ) (hr : Continuous rho) (hsig : Continuous sigma)
    (eps : ℝ)
    (hcomp : ∀ x : Base, (∀ alpha : SphereCotangent x,
      |B x alpha alpha-A x alpha alpha| ≤ eps*A x alpha alpha) ∧
      |sigma x-rho x| ≤ eps*rho x)
    (u : Base → ℝ) (hu : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ u) :
    (1-eps)*sphereDirichletForm A u u ≤ sphereDirichletForm B u u ∧
    sphereDirichletForm B u u ≤ (1+eps)*sphereDirichletForm A u u ∧
    (1-eps)*sphereWeightedPairing rho u u ≤ sphereWeightedPairing sigma u u ∧
    sphereWeightedPairing sigma u u ≤ (1+eps)*sphereWeightedPairing rho u u := by
  have hIA := intrinsic_differential_pair_integrable A hA hAs hAp u u hu hu
  have hIB := intrinsic_differential_pair_integrable B hB hBs hBp u u hu hu
  have hIr := sphereWeightedPairing_integrable rho u u hr hu.continuous hu.continuous
  have hIs := sphereWeightedPairing_integrable sigma u u hsig hu.continuous hu.continuous
  have hE (x : Base) := abs_le.mp ((hcomp x).1 (sphereDifferential u x))
  have hD (x : Base) :
      (1-eps)*(rho x*u x*u x) ≤ sigma x*u x*u x ∧
      sigma x*u x*u x ≤ (1+eps)*(rho x*u x*u x) := by
    have hh := abs_le.mp (hcomp x).2
    have hlo := mul_le_mul_of_nonneg_right hh.1 (sq_nonneg (u x))
    have hhi := mul_le_mul_of_nonneg_right hh.2 (sq_nonneg (u x))
    constructor <;> nlinarith
  refine ⟨?_,?_,?_,?_⟩
  · unfold sphereDirichletForm
    rw [← integral_const_mul]
    exact integral_mono (hIA.const_mul (1-eps)) hIB (fun x ↦ by nlinarith [hE x])
  · unfold sphereDirichletForm
    rw [← integral_const_mul]
    exact integral_mono hIB (hIA.const_mul (1+eps)) (fun x ↦ by nlinarith [hE x])
  · unfold sphereWeightedPairing
    rw [← integral_const_mul]
    exact integral_mono (hIr.const_mul (1-eps)) hIs (fun x ↦ (hD x).1)
  · unfold sphereWeightedPairing
    rw [← integral_const_mul]
    exact integral_mono hIs (hIr.const_mul (1+eps)) (fun x ↦ (hD x).2)

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

local instance sphereEnergyL2MapMeasurable_r706c04_1 : MeasurableSpace Base := borel Base
local instance sphereEnergyL2MapBorel_r706c04_1 : BorelSpace Base := ⟨rfl⟩
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

local instance sphereWeightedL1BoundMeasurable_r706c04_1 : MeasurableSpace Base := borel Base
local instance sphereWeightedL1BoundBorel_r706c04_1 : BorelSpace Base := ⟨rfl⟩
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

local instance sphereSmoothGreenBoundMeasurable_r706c04_1 : MeasurableSpace Base := borel Base
local instance sphereSmoothGreenBoundBorel_r706c04_1 : BorelSpace Base := ⟨rfl⟩
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

local instance sphereWeakResolventMeasurable_r706c04_1 : MeasurableSpace Base := borel Base
local instance sphereWeakResolventBorel_r706c04_1 : BorelSpace Base := ⟨rfl⟩
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

local instance sphereEnergyL2InjectiveMeasurable_r706c04_1 : MeasurableSpace Base := borel Base
local instance sphereEnergyL2InjectiveBorel_r706c04_1 : BorelSpace Base := ⟨rfl⟩
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

local instance sphereVariationalResolventMeasurable_r706c04_1 : MeasurableSpace Base := borel Base
local instance sphereVariationalResolventBorel_r706c04_1 : BorelSpace Base := ⟨rfl⟩
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
-- module Solutions.OAIQ237_NY.NodalSets_Spectral_SphereResolventFormBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open MeasureTheory
noncomputable section

local instance sphereFormBoundsMeasurable_r706c04_1 : MeasurableSpace Base := borel Base
local instance sphereFormBoundsBorel_r706c04_1 : BorelSpace Base := ⟨rfl⟩
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

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Charts_SphereFiniteNormQuadraticLimit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Manifold Yau.Geometry Filter MeasureTheory
open scoped ContDiff Topology
noncomputable section

lemma tendsto_of_eventually_relative_comparison (a b : ℕ → ℝ) (A : ℝ)
    (ha : Tendsto a atTop (𝓝 A))
    (hcmp : ∀ eps > 0, ∀ᶠ j in atTop,
      (1-eps)*a j ≤ b j ∧ b j ≤ (1+eps)*a j) :
    Tendsto b atTop (𝓝 A) := by
  rw [Metric.tendsto_nhds]
  intro eps heps
  let K := |A|+1
  have hK : 0 < K := by dsimp [K] <;> positivity
  have hAK : A < K := by dsimp [K] <;> linarith [le_abs_self A]
  have hd : 0 < eps/(2*K) := div_pos heps (mul_pos (by norm_num) hK)
  filter_upwards [hcmp (eps/(2*K)) hd, ha.eventually (gt_mem_nhds hAK),
    (Metric.tendsto_nhds.mp ha) (eps/2) (by positivity)] with j hj hbound hclose
  have herr : |b j-a j| ≤ (eps/(2*K))*a j := by
    rw [abs_le]
    constructor <;> nlinarith [hj.1,hj.2]
  have hscale : (eps/(2*K))*K=eps/2 := by field_simp
  have hsmall : |b j-a j| < eps/2 :=
    herr.trans_lt (by rw [← hscale]; exact mul_lt_mul_of_pos_left hbound hd)
  rw [Real.dist_eq] at hclose ⊢
  calc
    |b j-A| ≤ |b j-a j|+|a j-A| := abs_sub_le _ _ _
    _ < eps := by linarith

local instance sphereQuadraticLimitMeasurable_r706c04_1 : MeasurableSpace Base := borel Base
local instance sphereQuadraticLimitBorel_r706c04_1 : BorelSpace Base := ⟨rfl⟩
theorem sphere_finite_norm_quadratic_limit
    (P : Finset Base)
    (hcover : ∀ x : Base, ∃ p ∈ P, ∃ y ∈ sphereAtlasCore,
      (extChartAt (𝓡 4) p).symm y=x)
    (d : SphereEnergyData) (hd : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ d.density)
    (b : ℕ → SphereEnergyData)
    (hb : ∀ j, ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ (b j).density)
    (u : ℕ → SphereEnergySmooth d) (z : SphereEnergyHilbert d)
    (hz : Tendsto (fun j ↦ sphereEnergyToCompletion d (u j)) atTop (𝓝 z))
    (hcoeff : Tendsto (fun j ↦ sphereCoefficientDistance P 0
      d.tensor d.density (b j).tensor (b j).density) atTop (𝓝 0)) :
    Tendsto (fun j ↦ sphereDirichletForm (b j).tensor
      (SphereEnergySmooth.toSmooth d (u j)) (SphereEnergySmooth.toSmooth d (u j)))
      atTop (𝓝 (sphereCompletedDirichlet d z z)) ∧
    Tendsto (fun j ↦ sphereWeightedPairing (b j).density
      (SphereEnergySmooth.toSmooth d (u j)) (SphereEnergySmooth.toSmooth d (u j)))
      atTop (𝓝 (inner ℝ (sphereEnergyL2Map d z) (sphereEnergyL2Map d z))) := by
  have hL := ((sphereEnergyL2Map d).continuous.tendsto z).comp hz
  change Tendsto (fun j ↦ sphereEnergyL2Map d (sphereEnergyToCompletion d (u j)))
    atTop (𝓝 (sphereEnergyL2Map d z)) at hL
  have hW : Tendsto (fun j ↦ sphereWeightedPairing d.density
      (SphereEnergySmooth.toSmooth d (u j)) (SphereEnergySmooth.toSmooth d (u j)))
      atTop (𝓝 (inner ℝ (sphereEnergyL2Map d z) (sphereEnergyL2Map d z))) := by
    have h := hL.inner (𝕜 := ℝ) hL
    simp only [sphereEnergyL2Map_coe] at h
    convert h using 1
    all_goals try with_reducible_and_instances rfl
    funext j
    exact (sphereWeightedToLp_inner d.density d.continuous (fun x ↦ (d.positive x).le)
      _ _ (SphereEnergySmooth.toSmooth d (u j)).property.continuous
      (SphereEnergySmooth.toSmooth d (u j)).property.continuous).symm
  have hD : Tendsto (fun j ↦ sphereDirichletForm d.tensor
      (SphereEnergySmooth.toSmooth d (u j)) (SphereEnergySmooth.toSmooth d (u j)))
      atTop (𝓝 (sphereCompletedDirichlet d z z)) := by
    have h := (hz.inner (𝕜 := ℝ) hz).sub (hL.inner (𝕜 := ℝ) hL)
    change Tendsto (fun j ↦ sphereCompletedDirichlet d
      (sphereEnergyToCompletion d (u j)) (sphereEnergyToCompletion d (u j)))
      atTop (𝓝 (sphereCompletedDirichlet d z z)) at h
    simpa only [sphereCompletedDirichlet_coe] using h
  have hcomp (eps : ℝ) (heps : 0 < eps) : ∀ᶠ j in atTop,
      (1-eps)*sphereDirichletForm d.tensor (SphereEnergySmooth.toSmooth d (u j)) (SphereEnergySmooth.toSmooth d (u j)) ≤
        sphereDirichletForm (b j).tensor (SphereEnergySmooth.toSmooth d (u j)) (SphereEnergySmooth.toSmooth d (u j)) ∧
      sphereDirichletForm (b j).tensor (SphereEnergySmooth.toSmooth d (u j)) (SphereEnergySmooth.toSmooth d (u j)) ≤
        (1+eps)*sphereDirichletForm d.tensor (SphereEnergySmooth.toSmooth d (u j)) (SphereEnergySmooth.toSmooth d (u j)) ∧
      (1-eps)*sphereWeightedPairing d.density (SphereEnergySmooth.toSmooth d (u j)) (SphereEnergySmooth.toSmooth d (u j)) ≤
        sphereWeightedPairing (b j).density (SphereEnergySmooth.toSmooth d (u j)) (SphereEnergySmooth.toSmooth d (u j)) ∧
      sphereWeightedPairing (b j).density (SphereEnergySmooth.toSmooth d (u j)) (SphereEnergySmooth.toSmooth d (u j)) ≤
        (1+eps)*sphereWeightedPairing d.density (SphereEnergySmooth.toSmooth d (u j)) (SphereEnergySmooth.toSmooth d (u j)) := by
    obtain ⟨eta,heta,H⟩ := sphere_coefficient_relative_form_comparison P hcover
      d.tensor d.smooth d.symm d.pos d.density hd d.positive eps heps
    filter_upwards [hcoeff.eventually (gt_mem_nhds heta)] with j hj
    exact sphere_integrated_form_comparison d.tensor (b j).tensor d.smooth (b j).smooth
      d.symm (b j).symm d.pos (b j).pos d.density (b j).density d.continuous (b j).continuous eps
      (H (b j).tensor (b j).density (b j).smooth (b j).symm (b j).pos (hb j) hj)
      (SphereEnergySmooth.toSmooth d (u j)) (SphereEnergySmooth.toSmooth d (u j)).property
  constructor
  · apply tendsto_of_eventually_relative_comparison _ _ _ hD
    intro eps heps
    exact (hcomp eps heps).mono (fun j hj ↦ ⟨hj.1,hj.2.1⟩)
  · apply tendsto_of_eventually_relative_comparison _ _ _ hW
    intro eps heps
    exact (hcomp eps heps).mono (fun j hj ↦ hj.2.2)

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Charts_SphereFormPolarization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Manifold MeasureTheory
open scoped ContDiff
noncomputable section

lemma symmetric_additive_polarization {V : Type*} [Add V] (B : V → V → ℝ)
    (hs : ∀ u v, B u v=B v u) (ha : ∀ u v w, B (u+v) w=B u w+B v w)
    (u v : V) : (B (u+v) (u+v)-B u u-B v v)/2=B u v := by
  rw [ha u v (u+v),hs u (u+v),hs v (u+v),ha u v u,ha u v v,hs v u]
  ring

lemma sphereDirichletForm_polarization (d : SphereEnergyData) (u v : sphereSmoothFunctions) :
    (sphereDirichletForm d.tensor (u+v) (u+v)-sphereDirichletForm d.tensor u u-
      sphereDirichletForm d.tensor v v)/2=sphereDirichletForm d.tensor u v :=
  symmetric_additive_polarization (fun u v : sphereSmoothFunctions ↦ sphereDirichletForm d.tensor u v)
    (fun u v ↦ sphereDirichletForm_symm d.tensor d.symm u v)
    (fun u v w ↦ sphereDirichletForm_add_left d.tensor d.smooth d.symm d.pos
      u v w u.property v.property w.property) u v

lemma sphereWeightedPairing_polarization (d : SphereEnergyData) (u v : sphereSmoothFunctions) :
    (sphereWeightedPairing d.density (u+v) (u+v)-sphereWeightedPairing d.density u u-
      sphereWeightedPairing d.density v v)/2=sphereWeightedPairing d.density u v :=
  symmetric_additive_polarization (fun u v : sphereSmoothFunctions ↦ sphereWeightedPairing d.density u v)
    (fun u v ↦ sphereWeightedPairing_symm d.density u v)
    (fun u v w ↦ sphereWeightedPairing_add_left d.density u v w d.continuous
      u.property.continuous v.property.continuous w.property.continuous) u v

lemma sphereCompletedDirichlet_polarization (d : SphereEnergyData) (u v : SphereEnergyHilbert d) :
    (sphereCompletedDirichlet d (u+v) (u+v)-sphereCompletedDirichlet d u u-
      sphereCompletedDirichlet d v v)/2=sphereCompletedDirichlet d u v := by
  apply symmetric_additive_polarization
  · intro u v
    simp only [sphereCompletedDirichlet,real_inner_comm u v,
      real_inner_comm (sphereEnergyL2Map d u) (sphereEnergyL2Map d v)]
  · intro u v w
    simp only [sphereCompletedDirichlet,map_add,inner_add_left]
    ring

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Charts_SphereFiniteNormMixedLimit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Manifold Yau.Geometry Filter MeasureTheory
open scoped ContDiff Topology
noncomputable section

local instance sphereMixedLimitMeasurable_r706c04_1 : MeasurableSpace Base := borel Base
local instance sphereMixedLimitBorel_r706c04_1 : BorelSpace Base := ⟨rfl⟩
theorem sphere_finite_norm_mixed_limit
    (P : Finset Base)
    (hcover : ∀ x : Base, ∃ p ∈ P, ∃ y ∈ sphereAtlasCore,
      (extChartAt (𝓡 4) p).symm y=x)
    (d : SphereEnergyData) (hd : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ d.density)
    (b : ℕ → SphereEnergyData)
    (hb : ∀ j, ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ (b j).density)
    (u v : ℕ → SphereEnergySmooth d) (z w : SphereEnergyHilbert d)
    (hz : Tendsto (fun j ↦ sphereEnergyToCompletion d (u j)) atTop (𝓝 z))
    (hw : Tendsto (fun j ↦ sphereEnergyToCompletion d (v j)) atTop (𝓝 w))
    (hcoeff : Tendsto (fun j ↦ sphereCoefficientDistance P 0
      d.tensor d.density (b j).tensor (b j).density) atTop (𝓝 0)) :
    Tendsto (fun j ↦ sphereDirichletForm (b j).tensor
      (SphereEnergySmooth.toSmooth d (u j)) (SphereEnergySmooth.toSmooth d (v j)))
      atTop (𝓝 (sphereCompletedDirichlet d z w)) ∧
    Tendsto (fun j ↦ sphereWeightedPairing (b j).density
      (SphereEnergySmooth.toSmooth d (u j)) (SphereEnergySmooth.toSmooth d (v j)))
      atTop (𝓝 (inner ℝ (sphereEnergyL2Map d z) (sphereEnergyL2Map d w))) := by
  have hsum : Tendsto (fun j ↦ sphereEnergyToCompletion d (u j+v j)) atTop (𝓝 (z+w)) := by
    simpa only [map_add] using hz.add hw
  have hU := sphere_finite_norm_quadratic_limit P hcover d hd b hb u z hz hcoeff
  have hV := sphere_finite_norm_quadratic_limit P hcover d hd b hb v w hw hcoeff
  have hS := sphere_finite_norm_quadratic_limit P hcover d hd b hb (fun j ↦ u j+v j) (z+w) hsum hcoeff
  have hD := ((hS.1.sub hU.1).sub hV.1).div_const 2
  have hW := ((hS.2.sub hU.2).sub hV.2).div_const 2
  have hpol := symmetric_additive_polarization (inner ℝ : SphereWeightedL2 d → SphereWeightedL2 d → ℝ)
    (fun u v ↦ real_inner_comm v u) (fun u v w ↦ inner_add_left u v w) (sphereEnergyL2Map d z) (sphereEnergyL2Map d w)
  constructor
  · rw [sphereCompletedDirichlet_polarization] at hD
    convert hD using 1
    all_goals try with_reducible_and_instances rfl
    funext j
    exact (sphereDirichletForm_polarization (b j)
      (SphereEnergySmooth.toSmooth d (u j)) (SphereEnergySmooth.toSmooth d (v j))).symm
  · simp only [map_add,hpol] at hW
    convert hW using 1
    all_goals try with_reducible_and_instances rfl
    funext j
    exact (sphereWeightedPairing_polarization (b j)
      (SphereEnergySmooth.toSmooth d (u j)) (SphereEnergySmooth.toSmooth d (v j))).symm

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Charts_SphereFiniteNormVariationalLimit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Manifold Yau.Geometry Filter MeasureTheory
open scoped ContDiff Topology
noncomputable section

local instance sphereVariationalLimitMeasurable_r706c04_1 : MeasurableSpace Base := borel Base
local instance sphereVariationalLimitBorel_r706c04_1 : BorelSpace Base := ⟨rfl⟩
theorem sphere_finite_norm_variational_limit
    (P : Finset Base)
    (hcover : ∀ x : Base, ∃ p ∈ P, ∃ y ∈ sphereAtlasCore,
      (extChartAt (𝓡 4) p).symm y = x)
    (d₀ : SphereEnergyData)
    (hd₀ : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ d₀.density)
    (b : ℕ → SphereEnergyData)
    (hb : ∀ j, ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ (b j).density)
    (u : ℕ → SphereEnergySmooth d₀) (z : SphereEnergyHilbert d₀)
    (hz : Tendsto (fun j ↦ sphereEnergyToCompletion d₀ (u j)) atTop (𝓝 z))
    (hcoeff : Tendsto (fun j ↦ sphereCoefficientDistance P 0
      d₀.tensor d₀.density (b j).tensor (b j).density) atTop (𝓝 0))
    (lam : ℕ → ℝ) (lam₀ : ℝ) (hlam : Tendsto lam atTop (𝓝 lam₀))
    (he : ∀ j p y, -intrinsicWeightedChartOperator (b j).tensor (b j).density
      (SphereEnergySmooth.toSmooth d₀ (u j)) p y =
        lam j * (SphereEnergySmooth.toSmooth d₀ (u j) : Base → ℝ)
          ((extChartAt (𝓡 4) p).symm y)) :
    ∀ w : SphereEnergyHilbert d₀,
      sphereCompletedDirichlet d₀ z w =
        lam₀ * inner ℝ (sphereEnergyL2Map d₀ z) (sphereEnergyL2Map d₀ w) := by
  have htest (w : SphereEnergySmooth d₀) :
      sphereCompletedDirichlet d₀ z (sphereEnergyToCompletion d₀ w) =
        lam₀ * inner ℝ (sphereEnergyL2Map d₀ z)
          (sphereEnergyL2Map d₀ (sphereEnergyToCompletion d₀ w)) := by
    have hlim := sphere_finite_norm_mixed_limit P hcover d₀ hd₀ b hb u (fun _ ↦ w)
      z (sphereEnergyToCompletion d₀ w) hz tendsto_const_nhds hcoeff
    have hident : (fun j ↦ sphereDirichletForm (b j).tensor
        (SphereEnergySmooth.toSmooth d₀ (u j)) (SphereEnergySmooth.toSmooth d₀ w)) =
        (fun j ↦ lam j * sphereWeightedPairing (b j).density
          (SphereEnergySmooth.toSmooth d₀ (u j)) (SphereEnergySmooth.toSmooth d₀ w)) := by
      funext j
      rw [sphereDirichletForm_symm (b j).tensor (b j).symm]
      have h := (intrinsic_green_eigenfunction_test (b j).tensor (b j).smooth (b j).symm
        (b j).pos (b j).density (hb j) (b j).positive
        (SphereEnergySmooth.toSmooth d₀ w) (SphereEnergySmooth.toSmooth d₀ (u j))
        (SphereEnergySmooth.toSmooth d₀ w).property (SphereEnergySmooth.toSmooth d₀ (u j)).property
        (lam j) (he j)).2.2
      simpa only [sphereDirichletForm,sphereWeightedPairing_symm (b j).density
        (SphereEnergySmooth.toSmooth d₀ w) (SphereEnergySmooth.toSmooth d₀ (u j))] using h
    apply tendsto_nhds_unique hlim.1
    rw [hident]
    exact hlam.mul hlim.2
  intro w
  apply (sphereEnergyToCompletion_dense d₀).induction_on
    (p := fun w ↦ sphereCompletedDirichlet d₀ z w =
      lam₀ * inner ℝ (sphereEnergyL2Map d₀ z) (sphereEnergyL2Map d₀ w)) w
  · apply isClosed_eq
    · exact (continuous_const.inner continuous_id).sub
        (continuous_const.inner (sphereEnergyL2Map d₀).continuous)
    · fun_prop
  · exact htest

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
local instance sphereWeightedPairingLimitBorel_r706c04_1 : BorelSpace Base := ⟨rfl⟩
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

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Charts_SphereUniformEnergyRepresentative
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Manifold Yau.Geometry Yau.Analysis MeasureTheory Filter Metric
open scoped ContDiff Topology
noncomputable section

local instance sphereUniformEnergyMeasurable_r706c04_1 : MeasurableSpace Base := borel Base
local instance sphereUniformEnergyBorel_r706c04_1 : BorelSpace Base := ⟨rfl⟩
theorem sphere_uniform_weighted_L2_convergence (d : SphereEnergyData)
    (w : ℕ → Base → ℝ) (v : Base → ℝ) (hw : ∀ j, Continuous (w j)) (hv : Continuous v)
    (ht : TendstoUniformly w v atTop) :
    Tendsto (fun j ↦ sphereWeightedToLp d.density d.continuous (fun x ↦ (d.positive x).le) (w j) (hw j))
      atTop (𝓝 (sphereWeightedToLp d.density d.continuous (fun x ↦ (d.positive x).le) v hv)) := by
  have hconst : TendstoUniformly (fun _j : ℕ ↦ v) v atTop := by
    intro s hs
    exact Eventually.of_forall (fun _ _ ↦ refl_mem_uniformity hs)
  have hrho : TendstoUniformly (fun _j : ℕ ↦ d.density) d.density atTop := by
    intro s hs
    exact Eventually.of_forall (fun _ _ ↦ refl_mem_uniformity hs)
  have hdiff : TendstoUniformly (fun j x ↦ w j x-v x) (fun _x ↦ (0:ℝ)) atTop := by
    have hh := ht.sub hconst
    change TendstoUniformly (fun j x ↦ w j x-v x) (fun x ↦ v x-v x) atTop at hh
    simpa only [sub_self] using hh
  have hp := sphereWeightedPairing_uniform_density_limit (fun _j : ℕ ↦ d.density) d.density
    (fun _ ↦ d.continuous) d.continuous hrho
    (fun j x ↦ w j x-v x) (fun j x ↦ w j x-v x) (fun _ ↦ 0) (fun _ ↦ 0)
    (fun j ↦ (hw j).sub hv) (fun j ↦ (hw j).sub hv) continuous_const continuous_const hdiff hdiff
  have hp0 : sphereWeightedPairing d.density (fun _ ↦ 0) (fun _ ↦ 0)=0 := by
    simp only [sphereWeightedPairing,mul_zero,integral_zero]
  rw [hp0] at hp
  rw [Metric.tendsto_nhds]
  intro eps heps
  filter_upwards [hp.eventually (gt_mem_nhds (sq_pos_of_pos heps))] with j hj
  have heq : sphereWeightedToLp d.density d.continuous (fun x ↦ (d.positive x).le)
      (fun x ↦ w j x-v x) ((hw j).sub hv) =
      sphereWeightedToLp d.density d.continuous (fun x ↦ (d.positive x).le) (w j) (hw j)-
      sphereWeightedToLp d.density d.continuous (fun x ↦ (d.positive x).le) v hv :=
    MemLp.toLp_sub (sphereWeighted_memLp d.density d.continuous (fun x ↦ (d.positive x).le) (w j) (hw j))
      (sphereWeighted_memLp d.density d.continuous (fun x ↦ (d.positive x).le) v hv)
  have hn := sphereWeightedToLp_norm_sq d.density d.continuous (fun x ↦ (d.positive x).le)
    (fun x ↦ w j x-v x) ((hw j).sub hv)
  rw [heq] at hn
  rw [dist_eq_norm]
  nlinarith [norm_nonneg (sphereWeightedToLp d.density d.continuous (fun x ↦ (d.positive x).le) (w j) (hw j)-
    sphereWeightedToLp d.density d.continuous (fun x ↦ (d.positive x).le) v hv)]

theorem sphere_C1_energy_limit_representative (d : SphereEnergyData) (P : Finset Base) (r : ℝ)
    (hcover : ∀ x : Base, ∃ p ∈ P, ∃ z ∈ ball (0 : Yau.Jets.Coord) r, sphereChartCoordMap p z=x)
    (u : ℕ → SphereEnergySmooth d) (v : Base → ℝ) (hv : Continuous v)
    (ht : TendstoUniformly (fun j ↦ (SphereEnergySmooth.toSmooth d (u j) : Base → ℝ)) v atTop)
    (hjet : ∀ p ∈ P, ∀ i : Fin 4,
      TendstoUniformlyOn
        (fun j ↦ partialJet ((SphereEnergySmooth.toSmooth d (u j) : Base → ℝ) ∘ sphereChartCoordMap p) [i])
        (partialJet (v ∘ sphereChartCoordMap p) [i]) atTop (ball 0 r)) :
    ∃ z : SphereEnergyHilbert d, Tendsto (fun j ↦ sphereEnergyToCompletion d (u j)) atTop (𝓝 z) ∧
      sphereEnergyL2Map d z=sphereWeightedToLp d.density d.continuous (fun x ↦ (d.positive x).le) v hv ∧
      v =ᵐ[sphereWeightedMeasure d.density] (sphereEnergyL2Map d z : Base → ℝ) := by
  obtain ⟨z,hz⟩ := sphere_C1_energy_completion_limit d P r hcover u v ht hjet
  have hmap := ((sphereEnergyL2Map d).continuous.tendsto z).comp hz
  change Tendsto (fun j ↦ sphereEnergyL2Map d (sphereEnergyToCompletion d (u j))) atTop (𝓝 (sphereEnergyL2Map d z)) at hmap
  simp only [sphereEnergyL2Map_coe] at hmap
  have hLp := sphere_uniform_weighted_L2_convergence d
    (fun j ↦ (SphereEnergySmooth.toSmooth d (u j) : Base → ℝ)) v
    (fun j ↦ (SphereEnergySmooth.toSmooth d (u j)).property.continuous) hv ht
  have heq : sphereEnergyL2Map d z=sphereWeightedToLp d.density d.continuous (fun x ↦ (d.positive x).le) v hv :=
    tendsto_nhds_unique hmap hLp
  refine ⟨z,hz,heq,?_⟩
  rw [heq]
  exact (sphereWeighted_memLp d.density d.continuous (fun x ↦ (d.positive x).le) v hv).coeFn_toLp.symm

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

local instance sphereSmoothStrongMeasurable_r706c04_1 : MeasurableSpace Base := borel Base
local instance sphereSmoothStrongBorel_r706c04_1 : BorelSpace Base := ⟨rfl⟩
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

local instance sphereIndexedIntrinsicMeasurable_r706c04_1 : MeasurableSpace Base := borel Base
local instance sphereIndexedIntrinsicBorel_r706c04_1 : BorelSpace Base := ⟨rfl⟩
theorem sphere_smooth_resolvent_to_intrinsic (d : SphereEnergyData)
    (u : SphereEnergySmooth d) (mu : ℝ) (hmu : mu ≠ 0)
    (he : sphereL2Resolvent d (sphereEnergyL2Linear d u) = mu • sphereEnergyL2Linear d u) :
    ∀ p z, -intrinsicWeightedChartOperator d.tensor d.density
      (SphereEnergySmooth.toSmooth d u) p z =
        (mu⁻¹-1) * (SphereEnergySmooth.toSmooth d u : Base → ℝ)
          ((extChartAt (𝓡 4) p).symm z) := by
  apply sphere_smooth_variational_to_intrinsic d u (mu⁻¹-1)
  intro v
  rw [sphereCompletedDirichlet,sphereEnergyL2Map_coe,
    sphere_resolvent_smooth_variational d mu hmu u he v]
  ring

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Charts_SphereVariationalContinuousRegularity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Manifold MeasureTheory Filter
open scoped ContDiff Topology
noncomputable section

local instance sphereContinuousRegularityMeasurable_r706c04_1 : MeasurableSpace Base := borel Base
local instance sphereContinuousRegularityBorel_r706c04_1 : BorelSpace Base := ⟨rfl⟩
lemma sphere_continuous_eq_of_weighted_ae (d : SphereEnergyData) (u v : Base → ℝ)
    (hu : Continuous u) (hv : Continuous v)
    (ha : u =ᵐ[sphereWeightedMeasure d.density] v) : u=v := by
  let := sphereReferenceMeasure_openPos
  exact Measure.eq_of_ae_eq ((sphereWeightedMeasure_ae_iff d _).mp ha) hu hv

theorem sphere_variational_continuous_regularity
    (d : SphereEnergyData) (hd : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ d.density)
    (z : SphereEnergyHilbert d) (lam : ℝ)
    (v : Base → ℝ) (hv : Continuous v) (hne : v ≠ 0)
    (ha : v =ᵐ[sphereWeightedMeasure d.density] (sphereEnergyL2Map d z : Base → ℝ))
    (he : ∀ w : SphereEnergyHilbert d,
      sphereCompletedDirichlet d z w = lam * inner ℝ (sphereEnergyL2Map d z) (sphereEnergyL2Map d w)) :
    ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ v ∧
      ∀ p y, -intrinsicWeightedChartOperator d.tensor d.density v p y =
        lam * v ((extChartAt (𝓡 4) p).symm y) := by
  have hmapne : sphereEnergyL2Map d z ≠ 0 := by
    intro hz
    apply hne
    apply sphere_continuous_eq_of_weighted_ae d v 0 hv continuous_const
    rw [hz] at ha
    exact ha.trans (Lp.coeFn_zero ℝ 2 (sphereWeightedMeasure d.density))
  have hlam : 0 < lam+1 := by
    linarith [sphere_variational_eigenvalue_nonneg d lam z hmapne he]
  have hres := (sphere_variational_eigen_to_resolvent d lam z hmapne he).2
  obtain ⟨u,hu,hua,_⟩ := sphere_eigen_global_representative d
    (fun p ↦ (hd.comp (sphereChartCoordMap_smooth p)).contDiff)
    (lam+1)⁻¹ (inv_ne_zero hlam.ne') (sphereEnergyL2Map d z) hres
  have huv : u=v := sphere_continuous_eq_of_weighted_ae d u v hu.continuous hv (hua.trans ha.symm)
  subst u
  let w : SphereEnergySmooth d := (⟨v,hu⟩ : sphereSmoothFunctions)
  have hL : sphereEnergyL2Linear d w=sphereEnergyL2Map d z := by
    apply Lp.ext
    exact (sphereWeighted_memLp d.density d.continuous (fun x ↦ (d.positive x).le)
      v hu.continuous).coeFn_toLp.trans ha
  refine ⟨hu,?_⟩
  have hp := sphere_smooth_resolvent_to_intrinsic d w (lam+1)⁻¹ (inv_ne_zero hlam.ne')
    (by rw [hL]; exact hres)
  simpa only [inv_inv,add_sub_cancel_right,w,SphereEnergySmooth.toSmooth] using hp

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Charts_SphereC1IntrinsicLimit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Manifold MeasureTheory Filter Metric Yau.Geometry Yau.Analysis
open scoped ContDiff Topology
noncomputable section

local instance sphereC1IntrinsicMeasurable_r706c04_1 : MeasurableSpace Base := borel Base
local instance sphereC1IntrinsicBorel_r706c04_1 : BorelSpace Base := ⟨rfl⟩
theorem sphere_finite_norm_C1_intrinsic_limit_oai
    (P : Finset Base) (r : ℝ) (hr : r ≤ 1)
    (hcover : ∀ x : Base, ∃ p ∈ P, ∃ y ∈ ball (0 : Yau.Jets.Coord) r,
      sphereChartCoordMap p y=x)
    (d : SphereEnergyData) (hd : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ d.density)
    (b : ℕ → SphereEnergyData)
    (hb : ∀ j, ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ (b j).density)
    (u : ℕ → SphereEnergySmooth d) (v : Base → ℝ) (hv : Continuous v) (hne : v ≠ 0)
    (ht : TendstoUniformly (fun j ↦ (SphereEnergySmooth.toSmooth d (u j) : Base → ℝ)) v atTop)
    (hjet : ∀ p ∈ P, ∀ i : Fin 4,
      TendstoUniformlyOn
        (fun j ↦ partialJet ((SphereEnergySmooth.toSmooth d (u j) : Base → ℝ) ∘ sphereChartCoordMap p) [i])
        (partialJet (v ∘ sphereChartCoordMap p) [i]) atTop (ball 0 r))
    (hcoeff : Tendsto (fun j ↦ sphereCoefficientDistance P 0
      d.tensor d.density (b j).tensor (b j).density) atTop (𝓝 0))
    (lam : ℕ → ℝ) (lam₀ : ℝ) (hlam : Tendsto lam atTop (𝓝 lam₀))
    (he : ∀ j p y, -intrinsicWeightedChartOperator (b j).tensor (b j).density
      (SphereEnergySmooth.toSmooth d (u j)) p y =
        lam j * (SphereEnergySmooth.toSmooth d (u j) : Base → ℝ)
          ((extChartAt (𝓡 4) p).symm y)) :
    ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ v ∧
      ∀ p y, -intrinsicWeightedChartOperator d.tensor d.density v p y =
        lam₀ * v ((extChartAt (𝓡 4) p).symm y) := by
  have hcore : ∀ x : Base, ∃ p ∈ P, ∃ y ∈ sphereAtlasCore,
      (extChartAt (𝓡 4) p).symm y=x := by
    intro x
    obtain ⟨p,hp,y,hy,hyx⟩ := hcover x
    exact ⟨p,hp,seedCoordEquiv y,⟨y,(closedBall_subset_closedBall hr) (ball_subset_closedBall hy),rfl⟩,hyx⟩
  obtain ⟨z,hz,_,ha⟩ := sphere_C1_energy_limit_representative d P r hcover u v hv ht hjet
  exact sphere_variational_continuous_regularity d hd z lam₀ v hv hne ha
    (sphere_finite_norm_variational_limit P hcore d hd b hb u z hz hcoeff lam lam₀ hlam he)

end
end Yau.Target

end OAI
end

theorem solution : type_of% @OAI.Yau.Target.sphere_finite_norm_C1_intrinsic_limit_oai := @OAI.Yau.Target.sphere_finite_norm_C1_intrinsic_limit_oai
