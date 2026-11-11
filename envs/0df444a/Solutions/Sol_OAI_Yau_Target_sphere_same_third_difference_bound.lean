-- Prove2me | solution 1 for OAI.Yau.Target.sphere_same_third_difference_bound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T00:38:38.577204+00:00
-- url     : https://prove2.me/submissions/e78c36d1-a332-40e6-b999-7a36e743f9fb

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
import Theorems.Thm_OAI_Yau_Target_sphere_same_second_differentiated_equation

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

lemma intrinsicRealPrincipal_posDef (A : IntrinsicTensor)
    (hs : ∀ p v w, A p v w = A p w v) (hp : ∀ p v, v ≠ 0 → 0 < A p v v)
    (p : Base) (x : Yau.Jets.Coord) : (intrinsicRealPrincipal A p x).PosDef :=
  intrinsicSphereChartTensor_posDef A hs hp p (by rw [centeredSphereChart_target]; trivial)

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
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_RealFinCubeFubini
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open MeasureTheory Set Function
noncomputable section

lemma realFinCube_integrable (n : ℕ) (F : (Fin n → ℝ) → ℝ) (hF : Continuous F) :
    IntegrableOn F (realFinCube n) :=
  hF.continuousOn.integrableOn_compact (isCompact_univ_pi (fun _ ↦ isCompact_Icc))

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Charts_SphereChartEnergyBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Manifold Yau.Geometry MeasureTheory Set
open scoped ContDiff
noncomputable section

lemma sphere_chart_cube_lower_integral (p : Base) (f : Base → ℝ)
    (hf : Integrable f sphereReferenceMeasure) (hn : ∀ x, 0 ≤ f x)
    (G : Yau.Jets.Coord → ℝ) (hG : Continuous G) (a : ℝ)
    (hpt : ∀ x ∈ realFinCube 4, a*G x ≤ roundCoordDensity x*f (sphereChartCoordMap p x)) :
    a*(∫ x in realFinCube 4, G x) ≤ ∫ x, f x ∂sphereReferenceMeasure := by
  have hi : Integrable (fun x ↦ roundCoordDensity x*f (sphereChartCoordMap p x)) := by
    simpa only [roundChartDensity_coord_eq] using (sphereReferenceMeasure_integrable_chart p f).mp hf
  have h := setIntegral_mono_on (μ := volume)
    (realFinCube_integrable 4 _ (hG.const_mul a)) hi.integrableOn
    (realFinCube_isCompact 4).measurableSet hpt
  rw [integral_const_mul] at h
  rw [sphereReferenceMeasure_integral_chart p]
  simp only [roundChartDensity_coord_eq]
  exact h.trans (setIntegral_le_integral hi (Filter.Eventually.of_forall
    (fun x ↦ mul_nonneg (roundCoordDensity_pos x).le (hn _))))

theorem sphere_chart_cube_energy_bound (A : IntrinsicTensor) (hA : IntrinsicTensorSmooth A)
    (hs : ∀ x alpha beta, A x alpha beta = A x beta alpha)
    (hp : ∀ x alpha, alpha ≠ 0 → 0 < A x alpha alpha)
    (rho : Base → ℝ) (hr : Continuous rho) (hrp : ∀ x, 0 < rho x) (p : Base) :
    ∃ K > 0, ∀ u : Base → ℝ, ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ u →
      (∫ x in realFinCube 4, (u (sphereChartCoordMap p x))^2)+
        (∫ x in realFinCube 4, ∑ i, (Yau.coordPartial (u ∘ sphereChartCoordMap p) x i)^2) ≤
      K*(sphereWeightedPairing rho u u+sphereDirichletForm A u u) := by
  obtain ⟨q,hq,_,_,hqb⟩ := Yau.Jets.compact_positive_bounds (realFinCube_isCompact 4)
    (fun x ↦ roundCoordDensity x*rho (sphereChartCoordMap p x))
    ((roundCoordDensity_smooth.continuous.mul (hr.comp (sphereChartCoordMap_smooth p).continuous)).continuousOn)
    (fun x _ ↦ mul_pos (roundCoordDensity_pos x) (hrp _))
  obtain ⟨d,hd,_,_,hdb⟩ := Yau.Jets.compact_positive_bounds (realFinCube_isCompact 4)
    roundCoordDensity roundCoordDensity_smooth.continuous.continuousOn
    (fun x _ ↦ roundCoordDensity_pos x)
  obtain ⟨c,hc,_,_,hcb⟩ := intrinsic_real_uniform_ellipticity A hA hs hp p (realFinCube_isCompact 4)
  refine ⟨q⁻¹+(d*c)⁻¹,by positivity,?_⟩
  intro u hu
  have huc := spherePullback_smooth u hu p
  have hP : 0 ≤ sphereWeightedPairing rho u u := integral_nonneg (fun x ↦ by
    change 0 ≤ rho x*u x*u x
    nlinarith [mul_nonneg (hrp x).le (sq_nonneg (u x))])
  have hD : 0 ≤ sphereDirichletForm A u u := sphereDirichletForm_nonneg A hp u
  have hmass : q*(∫ x in realFinCube 4, (u (sphereChartCoordMap p x))^2) ≤
      sphereWeightedPairing rho u u := by
    apply sphere_chart_cube_lower_integral p (fun x ↦ rho x*u x*u x)
      (sphereWeightedPairing_integrable rho u u hr hu.continuous hu.continuous)
      (fun x ↦ by nlinarith [mul_nonneg (hrp x).le (sq_nonneg (u x))])
      _ (huc.continuous.pow 2) q
    intro x hx
    change q*(u (sphereChartCoordMap p x))^2 ≤
      roundCoordDensity x*(rho (sphereChartCoordMap p x)*u (sphereChartCoordMap p x)*u (sphereChartCoordMap p x))
    have h := mul_le_mul_of_nonneg_right (hqb x hx).1 (sq_nonneg (u (sphereChartCoordMap p x)))
    nlinarith only [h]
  have henergy : (d*c)*(∫ x in realFinCube 4, ∑ i,
      (Yau.coordPartial (u ∘ sphereChartCoordMap p) x i)^2) ≤ sphereDirichletForm A u u := by
    apply sphere_chart_cube_lower_integral p
      (fun x ↦ A x (sphereDifferential u x) (sphereDifferential u x))
      (intrinsic_differential_pair_integrable A hA hs hp u u hu hu)
      (fun x ↦ intrinsic_quadratic_nonneg A hp x _)
      _ (continuous_finsetSum _ (fun i _ ↦ (Yau.real_coordPartial_smooth _ huc i).continuous.pow 2)) (d*c)
    intro x hx
    rw [intrinsic_differential_pair_chart A u u hu hu]
    have h1 := mul_le_mul_of_nonneg_left (hcb x hx (fun i ↦ Yau.coordPartial (u ∘ sphereChartCoordMap p) x i)).1
      (roundCoordDensity_pos x).le
    have h2 := mul_le_mul_of_nonneg_right (hdb x hx).1
      (mul_nonneg hc.le (Finset.sum_nonneg (s := Finset.univ)
        (fun i _ ↦ sq_nonneg (Yau.coordPartial (u ∘ sphereChartCoordMap p) x i))))
    calc
      _ ≤ roundCoordDensity x*(c*∑ i, (Yau.coordPartial (u ∘ sphereChartCoordMap p) x i)^2) := by
        simpa only [mul_assoc,Pi.pow_apply] using h2
      _ ≤ _ := h1
  have hmass' := (le_div_iff₀ hq).mpr (by simpa only [mul_comm] using hmass)
  have henergy' : (∫ x in realFinCube 4, ∑ i,
      (Yau.coordPartial (u ∘ sphereChartCoordMap p) x i)^2) ≤ sphereDirichletForm A u u/(d*c) :=
    (le_div_iff₀ (mul_pos hd hc)).mpr (by simpa only [mul_comm] using henergy)
  calc
    _ ≤ sphereWeightedPairing rho u u/q+sphereDirichletForm A u u/(d*c) := add_le_add hmass' henergy'
    _ ≤ _ := by
      have h1 := mul_nonneg (inv_nonneg.mpr hq.le) hD
      have h2 := mul_nonneg (inv_nonneg.mpr (mul_pos hd hc).le) hP
      simp only [div_eq_mul_inv]
      nlinarith only [h1,h2]

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

local instance sphereEnergyL2MapMeasurable_r5c6d48_1 : MeasurableSpace Base := borel Base
local instance sphereEnergyL2MapBorel_r5c6d48_1 : BorelSpace Base := ⟨rfl⟩
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

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Charts_SphereWeightedChartL2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open MeasureTheory
noncomputable section

attribute [local instance] OAI.Yau.Target.sphereWeightedChartL2Measurable
attribute [local instance] OAI.Yau.Target.sphereWeightedChartL2Borel
theorem sphereWeightedL2_test_pairing (d : SphereEnergyData) (f : SphereWeightedL2 d)
    (h : Base → ℝ) (hh : Continuous h) :
    Integrable (fun x ↦ d.density x*f x*h x) sphereReferenceMeasure ∧
    inner ℝ f (sphereWeightedToLp d.density d.continuous (fun x ↦ (d.positive x).le) h hh) =
      ∫ x, d.density x*f x*h x ∂sphereReferenceMeasure := by
  let g := sphereWeightedToLp d.density d.continuous (fun x ↦ (d.positive x).le) h hh
  have hg : (g : Base → ℝ) =ᵐ[sphereWeightedMeasure d.density] h :=
    (sphereWeighted_memLp d.density d.continuous (fun x ↦ (d.positive x).le) h hh).coeFn_toLp
  have he : (fun x ↦ inner ℝ (f x) (g x)) =ᵐ[sphereWeightedMeasure d.density]
      (fun x ↦ f x*h x) := by
    filter_upwards [hg] with x hx
    rw [hx]
    change h x*f x = f x*h x
    ring
  have hi : Integrable (fun x ↦ f x*h x) (sphereWeightedMeasure d.density) :=
    (L2.integrable_inner f g).congr he
  refine ⟨?_,?_⟩
  · simpa only [mul_assoc] using (sphereWeightedMeasure_integrable_iff d _).mp hi
  · change inner ℝ f g = _
    rw [L2.inner_def,integral_congr_ae he,
      sphereWeightedMeasure_integral d.density d.continuous (fun x ↦ (d.positive x).le)]
    simp only [mul_assoc]

theorem sphereWeightedL2_test_chart (d : SphereEnergyData) (f : SphereWeightedL2 d)
    (h : Base → ℝ) (hh : Continuous h) (p : Base) :
    Integrable (fun y ↦ roundCoordDensity y*d.density (sphereChartCoordMap p y)*
      f (sphereChartCoordMap p y)*h (sphereChartCoordMap p y)) ∧
    inner ℝ f (sphereWeightedToLp d.density d.continuous (fun x ↦ (d.positive x).le) h hh) =
      ∫ y, roundCoordDensity y*d.density (sphereChartCoordMap p y)*
        f (sphereChartCoordMap p y)*h (sphereChartCoordMap p y) := by
  obtain ⟨hi,he⟩ := sphereWeightedL2_test_pairing d f h hh
  refine ⟨?_,?_⟩
  · simpa only [roundChartDensity_coord_eq,mul_assoc] using
      (sphereReferenceMeasure_integrable_chart p _).mp hi
  · rw [he,sphereReferenceMeasure_integral_chart p]
    simp only [roundChartDensity_coord_eq,mul_assoc]

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Charts_SphereChartDerivativeMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open MeasureTheory Yau.Geometry
noncomputable section

theorem sphereChartDerivativeLinear_norm_sq (d : SphereEnergyData) (p : Base) (i : Fin 4)
    (u : SphereEnergySmooth d) :
    ‖sphereChartDerivativeLinear d p i u‖^2 = ∫ x in realFinCube 4, (sphereSmoothChartPartial d p i u x)^2 :=
  Yau.real_toLp_norm_sq _ (sphereSmoothChartPartial_memLp d p i u)

theorem sphereChartDerivativeLinear_bound (d : SphereEnergyData) (p : Base) :
    ∃ C > 0, ∀ i (u : SphereEnergySmooth d), ‖sphereChartDerivativeLinear d p i u‖ ≤ C*‖u‖ := by
  obtain ⟨K,hK,hb⟩ := sphere_chart_cube_energy_bound d.tensor d.smooth d.symm d.pos
    d.density d.continuous d.positive p
  refine ⟨Real.sqrt K,Real.sqrt_pos.mpr hK,?_⟩
  intro i u
  have h := hb (SphereEnergySmooth.toSmooth d u) (SphereEnergySmooth.toSmooth d u).property
  rw [← SphereEnergySmooth.norm_sq] at h
  have hle : (∫ x in realFinCube 4, (sphereSmoothChartPartial d p i u x)^2) ≤
      ∫ x in realFinCube 4, ∑ j, (sphereSmoothChartPartial d p j u x)^2 := by
    apply integral_mono (sphereSmoothChartPartial_memLp d p i u).integrable_sq
      (integrable_finsetSum _ (fun j _ ↦ (sphereSmoothChartPartial_memLp d p j u).integrable_sq))
    intro x
    exact Finset.single_le_sum (fun j _ ↦ sq_nonneg (sphereSmoothChartPartial d p j u x)) (Finset.mem_univ i)
  have hsq : ‖sphereChartDerivativeLinear d p i u‖^2 ≤ K*‖u‖^2 := by
    rw [sphereChartDerivativeLinear_norm_sq]
    have hm : 0 ≤ ∫ x in realFinCube 4, ((SphereEnergySmooth.toSmooth d u : Base → ℝ) (sphereChartCoordMap p x))^2 :=
      integral_nonneg (fun _ ↦ sq_nonneg _)
    exact hle.trans (by unfold sphereSmoothChartPartial; linarith)
  have hroot : (Real.sqrt K*‖u‖)^2 = K*‖u‖^2 := by rw [mul_pow,Real.sq_sqrt hK.le]
  nlinarith [mul_nonneg (Real.sqrt_nonneg K) (norm_nonneg u),norm_nonneg (sphereChartDerivativeLinear d p i u)]

theorem sphereChartDerivativeMap_coe (d : SphereEnergyData) (p : Base) (i : Fin 4)
    (u : SphereEnergySmooth d) : sphereChartDerivativeMap d p i (sphereEnergyToCompletion d u) =
      sphereChartDerivativeLinear d p i u := by
  apply LinearMap.extendOfNorm_eq (sphereEnergyToCompletion_dense d)
  obtain ⟨C,_,hC⟩ := sphereChartDerivativeLinear_bound d p
  exact ⟨C,fun v ↦ by simpa using hC i v⟩

theorem sphereChartDerivativeMap_bound (d : SphereEnergyData) (p : Base) :
    ∃ C > 0, ∀ i (z : SphereEnergyHilbert d), ‖sphereChartDerivativeMap d p i z‖ ≤ C*‖z‖ := by
  obtain ⟨C,hC,hb⟩ := sphereChartDerivativeLinear_bound d p
  refine ⟨C,hC,fun i z ↦ ?_⟩
  have hn : ‖sphereChartDerivativeMap d p i‖ ≤ C :=
    LinearMap.opNorm_extendOfNorm_le (sphereEnergyToCompletion_dense d) hC.le
      (fun u ↦ by simpa using hb i u)
  exact ((sphereChartDerivativeMap d p i).le_opNorm z).trans
    (mul_le_mul_of_nonneg_right hn (norm_nonneg z))

end
end Yau.Target

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
-- module Solutions.OAIQ237_NY.NodalSets_Charts_SphereCompactChartTesting
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open MeasureTheory
open scoped ContDiff
noncomputable section

local instance sphereCompactChartTestingMeasurable_r5c6d48_1 : MeasurableSpace Base := borel Base
local instance sphereCompactChartTestingBorel_r5c6d48_1 : BorelSpace Base := ⟨rfl⟩
theorem sphere_compact_chart_testing (d : SphereEnergyData) (p : Base)
    (phi : Yau.Jets.Coord → ℝ) (hp : ContDiff ℝ ∞ phi) (hc : HasCompactSupport phi) :
    ∃ (h : Base → ℝ) (hh : Continuous h), ∀ f : SphereWeightedL2 d,
      Integrable (fun x ↦ f (sphereChartCoordMap p x)*phi x) ∧
      inner ℝ f (sphereWeightedToLp d.density d.continuous (fun x ↦ (d.positive x).le) h hh) =
        ∫ x, f (sphereChartCoordMap p x)*phi x := by
  have hpc : HasCompactSupport (fun x ↦ phi x/roundCoordDensity x) := by
    convert hc.mul_right (f' := fun x ↦ (roundCoordDensity x)⁻¹) using 1
    all_goals try with_reducible_and_instances rfl
    rfl
  obtain ⟨F,hF,_,hval⟩ := sphere_chart_scalar_extension p (fun x ↦ phi x/roundCoordDensity x)
    (hp.div roundCoordDensity_smooth (fun x ↦ (roundCoordDensity_pos x).ne')) hpc
  refine ⟨fun x ↦ F x/d.density x,hF.continuous.div d.continuous (fun x ↦ (d.positive x).ne'),?_⟩
  intro f
  have h := sphereWeightedL2_test_chart d f (fun x ↦ F x/d.density x)
    (hF.continuous.div d.continuous (fun x ↦ (d.positive x).ne')) p
  have he : (fun y ↦ roundCoordDensity y*d.density (sphereChartCoordMap p y)*
      f (sphereChartCoordMap p y)*(F (sphereChartCoordMap p y)/d.density (sphereChartCoordMap p y))) =
      (fun y ↦ f (sphereChartCoordMap p y)*phi y) := by
    funext y
    rw [hval]
    field_simp [(roundCoordDensity_pos y).ne',(d.positive (sphereChartCoordMap p y)).ne']
  rwa [he] at h

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
-- module Solutions.OAIQ237_NY.NodalSets_Charts_SphereChartWeakDerivative
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open MeasureTheory Yau.Geometry Set
open scoped ContDiff
noncomputable section

local instance sphereChartWeakDerivativeMeasurable_r5c6d48_1 : MeasurableSpace Base := borel Base
local instance sphereChartWeakDerivativeBorel_r5c6d48_1 : BorelSpace Base := ⟨rfl⟩
theorem sphere_chart_weak_derivative (d : SphereEnergyData) (p : Base) (i : Fin 4)
    (z : SphereEnergyHilbert d) (phi : Yau.Jets.Coord → ℝ) (hp : ContDiff ℝ ∞ phi)
    (hc : HasCompactSupport phi) (hs : tsupport phi ⊆ realFinCube 4) :
    IntegrableOn (fun x ↦ (sphereChartDerivativeMap d p i z) x*phi x) (realFinCube 4) ∧
    IntegrableOn (fun x ↦ (sphereEnergyL2Map d z) (sphereChartCoordMap p x)*Yau.coordPartial phi x i)
      (realFinCube 4) ∧
    (∫ x in realFinCube 4, (sphereChartDerivativeMap d p i z) x*phi x) =
      -(∫ x in realFinCube 4, (sphereEnergyL2Map d z) (sphereChartCoordMap p x)*Yau.coordPartial phi x i) := by
  have hd : ContDiff ℝ ∞ (fun x ↦ Yau.coordPartial phi x i) := Yau.real_coordPartial_smooth phi hp i
  have hdc : HasCompactSupport (fun x ↦ Yau.coordPartial phi x i) := hc.fderiv_apply ℝ (Pi.single i 1)
  obtain ⟨h,hh,ht⟩ := sphere_compact_chart_testing d p _ hd hdc
  let H := sphereWeightedToLp d.density d.continuous (fun x ↦ (d.positive x).le) h hh
  let hP := Yau.real_continuous_memLp_compact (realFinCube_isCompact 4) phi hp.continuous
  let P := hP.toLp phi
  have hz (w : SphereEnergyHilbert d) (x : Yau.Jets.Coord) (hx : x ∉ realFinCube 4) :
      (sphereEnergyL2Map d w) (sphereChartCoordMap p x)*Yau.coordPartial phi x i = 0 := by
    unfold Yau.coordPartial
    rw [fderiv_of_notMem_tsupport ℝ (fun h ↦ hx (hs h))]
    simp
  have hright (w : SphereEnergyHilbert d) : inner ℝ (sphereEnergyL2Map d w) H =
      ∫ x in realFinCube 4, (sphereEnergyL2Map d w) (sphereChartCoordMap p x)*Yau.coordPartial phi x i := by
    rw [(ht (sphereEnergyL2Map d w)).2]
    exact (setIntegral_eq_integral_of_forall_compl_eq_zero (hz w)).symm
  have hid (w : SphereEnergyHilbert d) : inner ℝ (sphereChartDerivativeMap d p i w) P =
      -inner ℝ (sphereEnergyL2Map d w) H := by
    apply (sphereEnergyToCompletion_dense d).induction_on
      (p := fun w ↦ inner ℝ (sphereChartDerivativeMap d p i w) P = -inner ℝ (sphereEnergyL2Map d w) H) w
    · exact isClosed_eq ((sphereChartDerivativeMap d p i).continuous.inner continuous_const)
        (((sphereEnergyL2Map d).continuous.inner continuous_const).neg)
    · intro u
      rw [hright,sphereEnergyL2Map_coe,sphereChartDerivativeMap_coe]
      change inner ℝ ((sphereSmoothChartPartial_memLp d p i u).toLp (sphereSmoothChartPartial d p i u))
        (hP.toLp phi) = _
      rw [Yau.real_toLp_inner]
      have hae : ∀ᵐ x, (sphereEnergyL2Linear d u) (sphereChartCoordMap p x) =
          (SphereEnergySmooth.toSmooth d u : Base → ℝ) (sphereChartCoordMap p x) := by
        apply (sphereWeightedMeasure_ae_chart_iff d p (fun y ↦ (sphereEnergyL2Linear d u) y =
          (SphereEnergySmooth.toSmooth d u : Base → ℝ) y)).mp
        exact (sphereWeighted_memLp d.density d.continuous (fun x ↦ (d.positive x).le)
          (SphereEnergySmooth.toSmooth d u) (SphereEnergySmooth.toSmooth d u).property.continuous).coeFn_toLp
      have he : (∫ x in realFinCube 4, (sphereEnergyL2Linear d u) (sphereChartCoordMap p x)*Yau.coordPartial phi x i) =
          ∫ x in realFinCube 4, (SphereEnergySmooth.toSmooth d u : Base → ℝ) (sphereChartCoordMap p x)*Yau.coordPartial phi x i := by
        apply integral_congr_ae
        filter_upwards [ae_restrict_of_ae hae] with x hx
        rw [hx]
      rw [he]
      exact (Yau.real_compact_test_derivative _ phi
        (spherePullback_smooth _ (SphereEnergySmooth.toSmooth d u).property p) hp hc i (realFinCube 4) hs).2.2
  obtain ⟨hLi,hLe⟩ := Yau.real_L2_test_pairing (sphereChartDerivativeMap d p i z) phi hP
  refine ⟨hLi,(ht (sphereEnergyL2Map d z)).1.integrableOn,?_⟩
  rw [← hLe,← hright]
  exact hid z

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

local instance sphereWeakResolventMeasurable_r5c6d48_1 : MeasurableSpace Base := borel Base
local instance sphereWeakResolventBorel_r5c6d48_1 : BorelSpace Base := ⟨rfl⟩
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

local instance sphereChartDivergenceDataMeasurable_r5c6d48_1 : MeasurableSpace Base := borel Base
local instance sphereChartDivergenceDataBorel_r5c6d48_1 : BorelSpace Base := ⟨rfl⟩
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
-- module Solutions.OAIQ237_NY.NodalSets_Charts_SphereInteriorJetBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open MeasureTheory Yau.Geometry Set
open scoped ContDiff
noncomputable section

theorem sphere_same_interior_jet_bound (d : SphereEnergyData) (p : Base)
    (C2 C3 : ℝ) (hC2 : 0 ≤ C2) (hC3 : 0 ≤ C3) :
    ∃ A > 0, ∀ (f : SphereWeightedL2 d)
      (H : Fin 4 → Fin 4 → Lp ℝ 2 (volume.restrict (Yau.realCenteredCube 4 (1/2))))
      (J : Fin 4 → Fin 4 → Fin 4 → Lp ℝ 2 (volume.restrict (Yau.realCenteredCube 4 (1/4)))),
      (∑ a, ∑ k, ‖H a k‖^2) ≤ C2*(‖f‖^2+‖sphereWeakSolution d f‖^2) →
      (∑ a, ∑ k, ∑ i, ‖J a k i‖^2) ≤ C3*(‖f‖^2+‖sphereWeakSolution d f‖^2) →
      let Q := Yau.realCenteredCube 4 (1/4)
      let E := ‖f‖^2+‖sphereWeakSolution d f‖^2
      (MemLp (fun x ↦ (sphereL2Resolvent d f) (sphereChartCoordMap p x)) 2 (volume.restrict Q) ∧
        (∫ x in Q, ((sphereL2Resolvent d f) (sphereChartCoordMap p x))^2) ≤ A*E) ∧
      (∀ a, MemLp (sphereChartDerivativeMap d p a (sphereWeakSolution d f)) 2 (volume.restrict Q) ∧
        (∫ x in Q, ((sphereChartDerivativeMap d p a (sphereWeakSolution d f)) x)^2) ≤ A*E) ∧
      (∀ a k, MemLp (H a k) 2 (volume.restrict Q) ∧ (∫ x in Q, (H a k x)^2) ≤ A*E) ∧
      (∀ a k i, MemLp (J a k i) 2 (volume.restrict Q) ∧ (∫ x in Q, (J a k i x)^2) ≤ A*E) := by
  let Q := Yau.realCenteredCube 4 (1/4)
  obtain ⟨W,hW,hwb⟩ := sphereWeightedL2_compact_chart_bound d p (Yau.realCenteredCube_isCompact 4 (1/4))
  obtain ⟨D,hD,hdb⟩ := sphereChartDerivativeMap_bound d p
  let A := W+D^2+C2+C3+1
  have hA : 0 < A := by dsimp [A] <;> positivity
  refine ⟨A,hA,fun f H J hH hJ ↦ ?_⟩
  dsimp only
  let E := ‖f‖^2+‖sphereWeakSolution d f‖^2
  have hE : 0 ≤ E := by dsimp [E] <;> positivity
  have hWle : W ≤ A := by dsimp [A] <;> nlinarith [sq_nonneg D]
  have hDle : D^2 ≤ A := by dsimp [A] <;> linarith
  have h2le : C2 ≤ A := by dsimp [A] <;> nlinarith [sq_nonneg D]
  have h3le : C3 ≤ A := by dsimp [A] <;> nlinarith [sq_nonneg D]
  have hfE : ‖f‖^2 ≤ E := by dsimp [E] <;> nlinarith [sq_nonneg ‖sphereWeakSolution d f‖]
  have hzE : ‖sphereWeakSolution d f‖^2 ≤ E := by dsimp [E] <;> nlinarith [sq_nonneg ‖f‖]
  have hsub : Q ⊆ realFinCube 4 := Yau.realCenteredCube_mono (by norm_num)
  have hsub2 : Q ⊆ Yau.realCenteredCube 4 (1/2) := Yau.realCenteredCube_mono (by norm_num)
  refine ⟨⟨(hwb (sphereL2Resolvent d f)).1,?_⟩,?_,?_,?_⟩
  · have hn : ‖sphereL2Resolvent d f‖ ≤ ‖f‖ :=
      ((sphereL2Resolvent d).le_opNorm f).trans (by
        simpa using mul_le_mul_of_nonneg_right (sphereL2Resolvent_norm_le d) (norm_nonneg f))
    have hn2 := (pow_le_pow_left₀ (norm_nonneg _) hn 2).trans hfE
    exact (hwb (sphereL2Resolvent d f)).2.trans
      ((mul_le_mul_of_nonneg_left hn2 hW.le).trans (mul_le_mul_of_nonneg_right hWle hE))
  · intro a
    have ht := Yau.real_Lp_restricted_square_le (Measure.restrict_mono hsub (le_refl volume))
      (sphereChartDerivativeMap d p a (sphereWeakSolution d f))
    refine ⟨ht.1,ht.2.trans ?_⟩
    have hb := pow_le_pow_left₀ (norm_nonneg _) (hdb a (sphereWeakSolution d f)) 2
    rw [mul_pow] at hb
    exact hb.trans ((mul_le_mul_of_nonneg_left hzE (sq_nonneg D)).trans
      (mul_le_mul_of_nonneg_right hDle hE))
  · intro a k
    have ht := Yau.real_Lp_restricted_square_le (Measure.restrict_mono hsub2 (le_refl volume)) (H a k)
    refine ⟨ht.1,ht.2.trans ?_⟩
    have hone : ‖H a k‖^2 ≤ ∑ b, ∑ c, ‖H b c‖^2 :=
      (Finset.single_le_sum (f := fun c ↦ ‖H a c‖^2) (fun c _ ↦ sq_nonneg _) (Finset.mem_univ k)).trans
      (Finset.single_le_sum (f := fun b ↦ ∑ c, ‖H b c‖^2)
        (fun b _ ↦ Finset.sum_nonneg (fun c _ ↦ sq_nonneg _)) (Finset.mem_univ a))
    exact (hone.trans hH).trans (mul_le_mul_of_nonneg_right h2le hE)
  · intro a k i
    have ht := Yau.real_Lp_restricted_square_le (le_refl (volume.restrict Q)) (J a k i)
    refine ⟨ht.1,ht.2.trans ?_⟩
    have hone : ‖J a k i‖^2 ≤ ∑ b, ∑ c, ∑ e, ‖J b c e‖^2 :=
      (Finset.single_le_sum (f := fun e ↦ ‖J a k e‖^2) (fun e _ ↦ sq_nonneg _) (Finset.mem_univ i)).trans
      ((Finset.single_le_sum (f := fun c ↦ ∑ e, ‖J a c e‖^2)
        (fun c _ ↦ Finset.sum_nonneg (fun e _ ↦ sq_nonneg _)) (Finset.mem_univ k)).trans
      (Finset.single_le_sum (f := fun b ↦ ∑ c, ∑ e, ‖J b c e‖^2)
        (fun b _ ↦ Finset.sum_nonneg (fun c _ ↦ Finset.sum_nonneg (fun e _ ↦ sq_nonneg _))) (Finset.mem_univ a)))
    exact (hone.trans hJ).trans (mul_le_mul_of_nonneg_right h3le hE)

end
end Yau.Target

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
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_RealWeakHessianSymmetry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau
open MeasureTheory Set
open scoped ContDiff
noncomputable section

theorem real_weak_hessian_symmetry {n : ℕ} {K : Set (Coord n)} (hK : IsCompact K)
    (w : Coord n → ℝ) (U : Fin n → Coord n → ℝ) (H : Fin n → Fin n → Coord n → ℝ)
    (hH : ∀ a i, MemLp (H a i) 2 (volume.restrict K))
    (hfirst : ∀ a psi, ContDiff ℝ ∞ psi → HasCompactSupport psi → tsupport psi ⊆ K →
      (∫ x in K, w x*coordPartial psi x a)=-(∫ x in K, U a x*psi x))
    (hsecond : ∀ a i psi, ContDiff ℝ ∞ psi → HasCompactSupport psi → tsupport psi ⊆ K →
      (∫ x in K, U a x*coordPartial psi x i)=-(∫ x in K, H a i x*psi x))
    (a i : Fin n) : H a i =ᵐ[volume.restrict (interior K)] H i a := by
  apply real_interior_L2_eq_of_test_pairings hK _ _ (hH a i) (hH i a)
  intro psi hp hc hs
  have hd (j : Fin n) := real_coordPartial_smooth psi hp j
  have hdc (j : Fin n) := hc.fderiv_apply ℝ (Pi.single j 1)
  have hds (j : Fin n) := (tsupport_fderiv_apply_subset ℝ (Pi.single j 1) (f := psi)).trans hs
  have h1 := hsecond a i psi hp hc hs
  have h2 := hsecond i a psi hp hc hs
  have h3 := hfirst a (fun x ↦ coordPartial psi x i) (hd i) (hdc i) (hds i)
  have h4 := hfirst i (fun x ↦ coordPartial psi x a) (hd a) (hdc a) (hds a)
  have hcomm : (fun x ↦ w x*coordPartial (fun y ↦ coordPartial psi y i) x a) =
      fun x ↦ w x*coordPartial (fun y ↦ coordPartial psi y a) x i := by
    funext x
    rw [real_coordPartial_commute psi hp x a i]
  rw [hcomm] at h3
  linarith only [h1,h2,h3,h4]

end
end Yau

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Charts_SphereWeakHessianSymmetry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open MeasureTheory Yau.Geometry Set
open scoped ContDiff
noncomputable section

theorem sphere_chart_weak_hessian_symmetric (d : SphereEnergyData) (p : Base)
    (z : SphereEnergyHilbert d)
    (H : Fin 4 → Fin 4 → Lp ℝ 2 (volume.restrict (Yau.realCenteredCube 4 (1/2))))
    (hsecond : ∀ a i psi, ContDiff ℝ ∞ psi → HasCompactSupport psi →
      tsupport psi ⊆ Yau.realCenteredCube 4 (1/2) →
      (∫ x in Yau.realCenteredCube 4 (1/2), (sphereChartDerivativeMap d p a z) x*Yau.coordPartial psi x i) =
        -(∫ x in Yau.realCenteredCube 4 (1/2), H a i x*psi x)) (a i : Fin 4) :
    (H a i : Yau.Jets.Coord → ℝ) =ᵐ[volume.restrict (interior (Yau.realCenteredCube 4 (1/2)))] H i a := by
  let w := fun x ↦ (sphereEnergyL2Map d z) (sphereChartCoordMap p x)
  have hK := Yau.realCenteredCube_isCompact 4 (1/2:ℝ)
  have hsub : Yau.realCenteredCube 4 (1/2) ⊆ realFinCube 4 := Yau.realCenteredCube_mono (by norm_num)
  obtain ⟨_,_,hb⟩ := sphereWeightedL2_compact_chart_bound d p (realFinCube_isCompact 4)
  have hfirst (j : Fin 4) := Yau.real_interior_weak_restrict hK (realFinCube_isCompact 4).measurableSet hsub
    w (sphereChartDerivativeMap d p j z) (hb (sphereEnergyL2Map d z)).1 (Lp.memLp _) j
    (fun psi hp hc hs ↦ by
      have hw := (sphere_chart_weak_derivative d p j z psi hp hc hs).2.2
      change (∫ x in realFinCube 4, (sphereChartDerivativeMap d p j z) x*psi x) =
        -(∫ x in realFinCube 4, w x*Yau.coordPartial psi x j) at hw
      linarith only [hw])
  exact Yau.real_weak_hessian_symmetry hK w (fun a ↦ sphereChartDerivativeMap d p a z)
    (fun a i ↦ H a i) (fun a i ↦ Lp.memLp (H a i))
    (fun a psi hp hc hs ↦ ((hfirst a).2.2 psi hp hc hs).2.2) hsecond a i

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_RealWeakThirdSymmetry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau
open MeasureTheory Set
open scoped ContDiff
noncomputable section

theorem real_weak_third_last_symmetry {n : ℕ} {K : Set (Coord n)} (hK : IsCompact K)
    (U : Fin n → Coord n → ℝ) (H : Fin n → Fin n → Coord n → ℝ)
    (J : Fin n → Fin n → Fin n → Coord n → ℝ)
    (hJ : ∀ a k i, MemLp (J a k i) 2 (volume.restrict K))
    (hH : ∀ a k psi, ContDiff ℝ ∞ psi → HasCompactSupport psi → tsupport psi ⊆ K →
      (∫ x in K, U a x*coordPartial psi x k)=-(∫ x in K, H a k x*psi x))
    (hthird : ∀ a k i psi, ContDiff ℝ ∞ psi → HasCompactSupport psi → tsupport psi ⊆ K →
      (∫ x in K, H a k x*coordPartial psi x i)=-(∫ x in K, J a k i x*psi x))
    (a k i : Fin n) : J a k i =ᵐ[volume.restrict (interior K)] J a i k :=
  real_weak_hessian_symmetry hK (U a) (H a) (J a) (hJ a) (hH a) (hthird a) k i

theorem real_weak_third_first_symmetry {n : ℕ} {K : Set (Coord n)} (hK : IsCompact K)
    (H : Fin n → Fin n → Coord n → ℝ) (J : Fin n → Fin n → Fin n → Coord n → ℝ)
    (hJ : ∀ a k i, MemLp (J a k i) 2 (volume.restrict K))
    (hsym : ∀ a k, H a k =ᵐ[volume.restrict K] H k a)
    (hthird : ∀ a k i psi, ContDiff ℝ ∞ psi → HasCompactSupport psi → tsupport psi ⊆ K →
      (∫ x in K, H a k x*coordPartial psi x i)=-(∫ x in K, J a k i x*psi x))
    (a k i : Fin n) : J a k i =ᵐ[volume.restrict (interior K)] J k a i := by
  apply real_interior_L2_eq_of_test_pairings hK _ _ (hJ a k i) (hJ k a i)
  intro psi hp hc hs
  have h1 := hthird a k i psi hp hc hs
  have h2 := hthird k a i psi hp hc hs
  have hid : (∫ x in K, H a k x*coordPartial psi x i)=∫ x in K, H k a x*coordPartial psi x i := by
    apply integral_congr_ae
    filter_upwards [hsym a k] with x hx
    rw [hx]
  linarith only [h1,h2,hid]

end
end Yau

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Charts_SphereWeakThirdSymmetry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open MeasureTheory Yau.Geometry Set
open scoped ContDiff
noncomputable section

theorem sphere_same_third_derivatives_symmetric (d : SphereEnergyData) (p : Base)
    (z : SphereEnergyHilbert d)
    (H : Fin 4 → Fin 4 → Lp ℝ 2 (volume.restrict (Yau.realCenteredCube 4 (1/2))))
    (J : Fin 4 → Fin 4 → Fin 4 → Lp ℝ 2 (volume.restrict (Yau.realCenteredCube 4 (1/4))))
    (hsecond : ∀ a k psi, ContDiff ℝ ∞ psi → HasCompactSupport psi →
      tsupport psi ⊆ Yau.realCenteredCube 4 (1/2) →
      (∫ x in Yau.realCenteredCube 4 (1/2), (sphereChartDerivativeMap d p a z) x*Yau.coordPartial psi x k)=
        -(∫ x in Yau.realCenteredCube 4 (1/2), H a k x*psi x))
    (hthird : ∀ a k i psi, ContDiff ℝ ∞ psi → HasCompactSupport psi →
      tsupport psi ⊆ Yau.realCenteredCube 4 (1/4) →
      (∫ x in Yau.realCenteredCube 4 (1/4), H a k x*Yau.coordPartial psi x i)=
        -(∫ x in Yau.realCenteredCube 4 (1/4), J a k i x*psi x)) :
    ∀ a k i,
      (J a k i : Yau.Jets.Coord → ℝ) =ᵐ[volume.restrict
        (interior (Yau.realCenteredCube 4 (1/4)))] J a i k ∧
      (J a k i : Yau.Jets.Coord → ℝ) =ᵐ[volume.restrict
        (interior (Yau.realCenteredCube 4 (1/4)))] J k a i := by
  let Q := Yau.realCenteredCube 4 (1/2)
  let Q0 := Yau.realCenteredCube 4 (1/4)
  have hQ : IsCompact Q := Yau.realCenteredCube_isCompact 4 (1/2)
  have hQ0 : IsCompact Q0 := Yau.realCenteredCube_isCompact 4 (1/4)
  have hsub : Q0 ⊆ Q := Yau.realCenteredCube_mono (by norm_num)
  have hsub0 : Q ⊆ realFinCube 4 := Yau.realCenteredCube_mono (by norm_num)
  have hfirst (a k : Fin 4) := Yau.real_interior_weak_restrict hQ0 hQ.measurableSet hsub
    (sphereChartDerivativeMap d p a z) (H a k)
    ((Lp.memLp _).mono_measure (Measure.restrict_mono hsub0 le_rfl)) (Lp.memLp _) k (hsecond a k)
  have hs : ∀ a k, (H a k : Yau.Jets.Coord → ℝ) =ᵐ[volume.restrict Q0] H k a := by
    intro a k
    have hsym := sphere_chart_weak_hessian_symmetric d p z H hsecond a k
    exact ae_mono (Measure.restrict_mono (Yau.realCenteredCube_subset_interior (by norm_num)) le_rfl) hsym
  intro a k i
  exact ⟨Yau.real_weak_third_last_symmetry hQ0 (fun a ↦ sphereChartDerivativeMap d p a z)
    (fun a k ↦ H a k) (fun a k i ↦ J a k i) (fun a k i ↦ Lp.memLp _)
    (fun a k psi hp hc hs ↦ ((hfirst a k).2.2 psi hp hc hs).2.2) hthird a k i,
    Yau.real_weak_third_first_symmetry hQ0 (fun a k ↦ H a k) (fun a k i ↦ J a k i)
      (fun a k i ↦ Lp.memLp _) hs hthird a k i⟩

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Charts_SphereThirdFluxSymmetry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open MeasureTheory Yau.Geometry Set
open scoped ContDiff
noncomputable section

theorem sphere_same_third_flux_symmetric (d : SphereEnergyData) (p : Base)
    (z : SphereEnergyHilbert d)
    (H : Fin 4 → Fin 4 → Lp ℝ 2 (volume.restrict (Yau.realCenteredCube 4 (1/2))))
    (J : Fin 4 → Fin 4 → Fin 4 → Lp ℝ 2 (volume.restrict (Yau.realCenteredCube 4 (1/4))))
    (hsecond : ∀ a k psi, ContDiff ℝ ∞ psi → HasCompactSupport psi →
      tsupport psi ⊆ Yau.realCenteredCube 4 (1/2) →
      (∫ x in Yau.realCenteredCube 4 (1/2), (sphereChartDerivativeMap d p a z) x*Yau.coordPartial psi x k)=
        -(∫ x in Yau.realCenteredCube 4 (1/2), H a k x*psi x))
    (hthird : ∀ a k i psi, ContDiff ℝ ∞ psi → HasCompactSupport psi →
      tsupport psi ⊆ Yau.realCenteredCube 4 (1/4) →
      (∫ x in Yau.realCenteredCube 4 (1/4), H a k x*Yau.coordPartial psi x i)=
        -(∫ x in Yau.realCenteredCube 4 (1/4), J a k i x*psi x)) :
    ∀ a k l, (J a k l : Yau.Jets.Coord → ℝ) =ᵐ[volume.restrict
      (interior (Yau.realCenteredCube 4 (1/4)))] J k l a := by
  have hs := sphere_same_third_derivatives_symmetric d p z H J hsecond hthird
  intro a k l
  exact (hs a k l).2.trans (hs k a l).1

end
end Yau.Target

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
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_RealSecondCommutatorBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau
open MeasureTheory Set
open scoped ContDiff
noncomputable section

theorem real_second_commutator_bound {n : ℕ} {K : Set (Coord n)} (hK : IsCompact K)
    (C : Coord n → Fin n → Fin n → ℝ)
    (hC : ∀ a j, ContDiff ℝ ∞ (fun x ↦ C x a j)) (k l j : Fin n) :
    ∃ D > 0, ∀ (U : Fin n → Coord n → ℝ) (H : Fin n → Fin n → Coord n → ℝ),
      (∀ a, MemLp (U a) 2 (volume.restrict K)) →
      (∀ a b, MemLp (H a b) 2 (volume.restrict K)) →
      ∀ E : ℝ, 0 ≤ E → (∀ a, (∫ x in K, (U a x)^2) ≤ E) →
      (∀ a b, (∫ x in K, (H a b x)^2) ≤ E) →
        MemLp (realSecondCommutator C U H k l j) 2 (volume.restrict K) ∧
        (∫ x in K, (realSecondCommutator C U H k l j x)^2) ≤ D*E := by
  let A : Coord n → (Fin n × Fin 3) → ℝ := fun x t ↦
    let a := t.1
    ![coordPartial (fun y ↦ C y a j) x l,coordPartial (fun y ↦ C y a j) x k,coordPartial (fun y ↦ coordPartial (fun z ↦ C z a j) y k) x l] t.2
  have hA (t : Fin n × Fin 3) : Continuous (fun x ↦ A x t) := by
    rcases t with ⟨a,b⟩
    fin_cases b
    · exact (real_coordPartial_smooth _ (hC a j) l).continuous
    · exact (real_coordPartial_smooth _ (hC a j) k).continuous
    · exact (real_coordPartial_smooth _ (real_coordPartial_smooth _ (hC a j) k) l).continuous
  obtain ⟨D,hD,hb⟩ := real_compact_fintype_coefficient_common_bound hK A hA
  refine ⟨D,hD,fun U H hU hH E hE hUE hHE ↦ ?_⟩
  let V : (Fin n × Fin 3) → Coord n → ℝ := fun t ↦
    let a := t.1
    ![H a k,H a l,U a] t.2
  have hV (t : Fin n × Fin 3) : MemLp (V t) 2 (volume.restrict K) := by
    rcases t with ⟨a,b⟩
    fin_cases b
    · exact hH a k
    · exact hH a l
    · exact hU a
  have hVE (t : Fin n × Fin 3) : (∫ x in K, (V t x)^2) ≤ E := by
    rcases t with ⟨a,b⟩
    fin_cases b
    · exact hHE a k
    · exact hHE a l
    · exact hUE a
  have h := hb V hV E hE hVE
  have heq : (fun x ↦ ∑ t, A x t*V t x)=realSecondCommutator C U H k l j := by
    funext x
    simp [A,V,realSecondCommutator,Fintype.sum_prod_type,Fin.sum_univ_succ,add_assoc]
  rw [heq] at h
  simp_rw [show ∀ x, _ = _ from fun x ↦ congrFun heq x] at h
  exact h

theorem real_second_commutator_derivative_bound {n : ℕ} {K : Set (Coord n)} (hK : IsCompact K)
    (C : Coord n → Fin n → Fin n → ℝ)
    (hC : ∀ a j, ContDiff ℝ ∞ (fun x ↦ C x a j)) (k l j i : Fin n) :
    ∃ D > 0, ∀ (U : Fin n → Coord n → ℝ) (H : Fin n → Fin n → Coord n → ℝ)
      (J : Fin n → Fin n → Fin n → Coord n → ℝ),
      (∀ a, MemLp (U a) 2 (volume.restrict K)) →
      (∀ a b, MemLp (H a b) 2 (volume.restrict K)) →
      (∀ a b c, MemLp (J a b c) 2 (volume.restrict K)) →
      ∀ E : ℝ, 0 ≤ E → (∀ a, (∫ x in K, (U a x)^2) ≤ E) →
      (∀ a b, (∫ x in K, (H a b x)^2) ≤ E) →
      (∀ a b c, (∫ x in K, (J a b c x)^2) ≤ E) →
        MemLp (realSecondCommutatorDerivative C U H J k l j i) 2 (volume.restrict K) ∧
        (∫ x in K, (realSecondCommutatorDerivative C U H J k l j i x)^2) ≤ D*E := by
  let A : Coord n → (Fin n × Fin 6) → ℝ := fun x t ↦
    let a := t.1
    ![coordPartial (fun y ↦ C y a j) x l,coordPartial (fun y ↦ coordPartial (fun z ↦ C z a j) y l) x i,coordPartial (fun y ↦ C y a j) x k,coordPartial (fun y ↦ coordPartial (fun z ↦ C z a j) y k) x i,coordPartial (fun y ↦ coordPartial (fun z ↦ C z a j) y k) x l,coordPartial (fun y ↦ coordPartial (fun z ↦ coordPartial (fun t ↦ C t a j) z k) y l) x i] t.2
  have hA (t : Fin n × Fin 6) : Continuous (fun x ↦ A x t) := by
    rcases t with ⟨a,b⟩
    fin_cases b
    · exact (real_coordPartial_smooth _ (hC a j) l).continuous
    · exact (real_coordPartial_smooth _ (real_coordPartial_smooth _ (hC a j) l) i).continuous
    · exact (real_coordPartial_smooth _ (hC a j) k).continuous
    · exact (real_coordPartial_smooth _ (real_coordPartial_smooth _ (hC a j) k) i).continuous
    · exact (real_coordPartial_smooth _ (real_coordPartial_smooth _ (hC a j) k) l).continuous
    · exact (real_coordPartial_smooth _ (real_coordPartial_smooth _ (real_coordPartial_smooth _ (hC a j) k) l) i).continuous
  obtain ⟨D,hD,hb⟩ := real_compact_fintype_coefficient_common_bound hK A hA
  refine ⟨D,hD,fun U H J hU hH hJ E hE hUE hHE hJE ↦ ?_⟩
  let V : (Fin n × Fin 6) → Coord n → ℝ := fun t ↦
    let a := t.1
    ![J a k i,H a k,J a l i,H a l,H a i,U a] t.2
  have hV (t : Fin n × Fin 6) : MemLp (V t) 2 (volume.restrict K) := by
    rcases t with ⟨a,b⟩
    fin_cases b
    · exact hJ a k i
    · exact hH a k
    · exact hJ a l i
    · exact hH a l
    · exact hH a i
    · exact hU a
  have hVE (t : Fin n × Fin 6) : (∫ x in K, (V t x)^2) ≤ E := by
    rcases t with ⟨a,b⟩
    fin_cases b
    · exact hJE a k i
    · exact hHE a k
    · exact hJE a l i
    · exact hHE a l
    · exact hHE a i
    · exact hUE a
  have h := hb V hV E hE hVE
  have heq : (fun x ↦ ∑ t, A x t*V t x)=realSecondCommutatorDerivative C U H J k l j i := by
    funext x
    simp [A,V,realSecondCommutatorDerivative,Fintype.sum_prod_type,Fin.sum_univ_succ,add_assoc]
  rw [heq] at h
  simp_rw [show ∀ x, _ = _ from fun x ↦ congrFun heq x] at h
  exact h

end
end Yau

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_RealSecondScalarBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau
open MeasureTheory Set
open scoped ContDiff
noncomputable section

theorem real_second_scalar_forcing_bound {n : ℕ} {K : Set (Coord n)} (hK : IsCompact K)
    (B : Coord n → ℝ) (hB : ContDiff ℝ ∞ B) (k l : Fin n) :
    ∃ C > 0, ∀ (w : Coord n → ℝ) (U : Fin n → Coord n → ℝ)
      (H : Fin n → Fin n → Coord n → ℝ),
      MemLp w 2 (volume.restrict K) → (∀ a, MemLp (U a) 2 (volume.restrict K)) →
      (∀ a b, MemLp (H a b) 2 (volume.restrict K)) →
      ∀ E : ℝ, 0 ≤ E → (∫ x in K, (w x)^2) ≤ E →
      (∀ a, (∫ x in K, (U a x)^2) ≤ E) →
      (∀ a b, (∫ x in K, (H a b x)^2) ≤ E) →
        MemLp (realSecondScalarForcing B w U H k l) 2 (volume.restrict K) ∧
        (∫ x in K, (realSecondScalarForcing B w U H k l x)^2) ≤ C*E := by
  let A : Coord n → Fin 4 → ℝ := fun x ↦
    ![B x,coordPartial B x l,coordPartial B x k,coordPartial (fun y ↦ coordPartial B y k) x l]
  have hA (a : Fin 4) : Continuous (fun x ↦ A x a) := by
    fin_cases a
    · exact hB.continuous
    · exact (real_coordPartial_smooth B hB l).continuous
    · exact (real_coordPartial_smooth B hB k).continuous
    · exact (real_coordPartial_smooth _ (real_coordPartial_smooth B hB k) l).continuous
  obtain ⟨C,hC,hb⟩ := real_compact_fintype_coefficient_common_bound hK A hA
  refine ⟨C,hC,fun w U H hw hU hH E hE hwE hUE hHE ↦ ?_⟩
  let V : Fin 4 → Coord n → ℝ := ![H k l,U k,U l,w]
  have hV (a : Fin 4) : MemLp (V a) 2 (volume.restrict K) := by
    fin_cases a
    · exact hH k l
    · exact hU k
    · exact hU l
    · exact hw
  have hVE (a : Fin 4) : (∫ x in K, (V a x)^2) ≤ E := by
    fin_cases a
    · exact hHE k l
    · exact hUE k
    · exact hUE l
    · exact hwE
  have h := hb V hV E hE hVE
  have heq : (fun x ↦ ∑ a, A x a*V a x)=realSecondScalarForcing B w U H k l := by
    funext x
    simp [A,V,realSecondScalarForcing,Fin.sum_univ_succ,add_assoc]
  rw [heq] at h
  simp_rw [show ∀ x, _ = _ from fun x ↦ congrFun heq x] at h
  exact h

end
end Yau

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Spectral_SphereEigenSecondForcingBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open MeasureTheory Yau.Geometry Set
open scoped ContDiff
noncomputable section

theorem sphere_same_second_forcing_bound (d : SphereEnergyData) (p : Base)
    (hrho : ContDiff ℝ ∞ (fun x ↦ d.density (sphereChartCoordMap p x)))
    (mu C2 C3 : ℝ) (hC2 : 0 ≤ C2) (hC3 : 0 ≤ C3) :
    ∃ M > 0, ∀ (f : SphereWeightedL2 d)
      (H : Fin 4 → Fin 4 → Lp ℝ 2 (volume.restrict (Yau.realCenteredCube 4 (1/2))))
      (J : Fin 4 → Fin 4 → Fin 4 → Lp ℝ 2 (volume.restrict (Yau.realCenteredCube 4 (1/4)))),
      (∑ a, ∑ k, ‖H a k‖^2) ≤ C2*(‖f‖^2+‖sphereWeakSolution d f‖^2) →
      (∑ a, ∑ k, ∑ i, ‖J a k i‖^2) ≤ C3*(‖f‖^2+‖sphereWeakSolution d f‖^2) →
      let Q := Yau.realCenteredCube 4 (1/4)
      let E := ‖f‖^2+‖sphereWeakSolution d f‖^2
      let C := sphereChartPrincipalDensity d p
      let B := sphereEigenForcingCoefficient d p mu
      let w := fun x ↦ (sphereL2Resolvent d f) (sphereChartCoordMap p x)
      let U := fun a ↦ (sphereChartDerivativeMap d p a (sphereWeakSolution d f) : Yau.Jets.Coord → ℝ)
      ∀ k l j i,
        (MemLp (Yau.realSecondScalarForcing B w U (fun a b ↦ H a b) k l) 2 (volume.restrict Q) ∧
          (∫ x in Q, (Yau.realSecondScalarForcing B w U (fun a b ↦ H a b) k l x)^2) ≤ M*E) ∧
        (MemLp (Yau.realSecondCommutator C U (fun a b ↦ H a b) k l j) 2 (volume.restrict Q) ∧
          (∫ x in Q, (Yau.realSecondCommutator C U (fun a b ↦ H a b) k l j x)^2) ≤ M*E) ∧
        (MemLp (Yau.realSecondCommutatorDerivative C U (fun a b ↦ H a b)
            (fun a b c ↦ J a b c) k l j i) 2 (volume.restrict Q) ∧
          (∫ x in Q, (Yau.realSecondCommutatorDerivative C U (fun a b ↦ H a b)
            (fun a b c ↦ J a b c) k l j i x)^2) ≤ M*E) := by
  let Q := Yau.realCenteredCube 4 (1/4)
  have hQ : IsCompact Q := Yau.realCenteredCube_isCompact 4 (1/4)
  let B := sphereEigenForcingCoefficient d p mu
  have hB : ContDiff ℝ ∞ B := contDiff_const.mul (roundCoordDensity_smooth.mul hrho)
  obtain ⟨A,hA,hjet⟩ := sphere_same_interior_jet_bound d p C2 C3 hC2 hC3
  choose CF hCF hFb using fun k l ↦ Yau.real_second_scalar_forcing_bound hQ B hB k l
  obtain ⟨F0,hF0,hFmax⟩ := Yau.real_finite_positive_majorant (fun t : Fin 4 × Fin 4 ↦ CF t.1 t.2)
  choose CG hCG hGb using fun k l j ↦ Yau.real_second_commutator_bound hQ
    (sphereChartPrincipalDensity d p) (sphereChartPrincipalDensity_smooth d p) k l j
  obtain ⟨G0,hG0,hGmax⟩ := Yau.real_finite_positive_majorant
    (fun t : Fin 4 × Fin 4 × Fin 4 ↦ CG t.1 t.2.1 t.2.2)
  choose CD hCD hDb using fun k l j i ↦ Yau.real_second_commutator_derivative_bound hQ
    (sphereChartPrincipalDensity d p) (sphereChartPrincipalDensity_smooth d p) k l j i
  obtain ⟨D0,hD0,hDmax⟩ := Yau.real_finite_positive_majorant
    (fun t : Fin 4 × Fin 4 × Fin 4 × Fin 4 ↦ CD t.1 t.2.1 t.2.2.1 t.2.2.2)
  let M := (F0+G0+D0)*A
  refine ⟨M,by dsimp [M] <;> positivity,fun f H J hH hJ ↦ ?_⟩
  dsimp only
  intro k l j i
  let E := ‖f‖^2+‖sphereWeakSolution d f‖^2
  have hE : 0 ≤ E := by dsimp [E] <;> positivity
  have hAE : 0 ≤ A*E := mul_nonneg hA.le hE
  obtain ⟨hw,hU,hH0,hJ0⟩ := hjet f H J hH hJ
  have hF := hFb k l _ _ _ hw.1 (fun a ↦ (hU a).1) (fun a b ↦ (hH0 a b).1)
    (A*E) hAE hw.2 (fun a ↦ (hU a).2) (fun a b ↦ (hH0 a b).2)
  have hG := hGb k l j _ _ (fun a ↦ (hU a).1) (fun a b ↦ (hH0 a b).1)
    (A*E) hAE (fun a ↦ (hU a).2) (fun a b ↦ (hH0 a b).2)
  have hD := hDb k l j i _ _ _ (fun a ↦ (hU a).1) (fun a b ↦ (hH0 a b).1)
    (fun a b c ↦ (hJ0 a b c).1) (A*E) hAE (fun a ↦ (hU a).2)
    (fun a b ↦ (hH0 a b).2) (fun a b c ↦ (hJ0 a b c).2)
  refine ⟨⟨hF.1,hF.2.trans ?_⟩,⟨hG.1,hG.2.trans ?_⟩,⟨hD.1,hD.2.trans ?_⟩⟩
  · have hm : CF k l ≤ F0+G0+D0 := by linarith [hFmax (k,l)]
    simpa only [M,mul_assoc] using mul_le_mul_of_nonneg_right hm hAE
  · have hm : CG k l j ≤ F0+G0+D0 := by linarith [hGmax (k,l,j)]
    simpa only [M,mul_assoc] using mul_le_mul_of_nonneg_right hm hAE
  · have hm : CD k l j i ≤ F0+G0+D0 := by linarith [hDmax (k,l,j,i)]
    simpa only [M,mul_assoc] using mul_le_mul_of_nonneg_right hm hAE

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Spectral_SphereEigenThirdDifferenceBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open MeasureTheory Yau.Geometry Set
open scoped ContDiff
noncomputable section

theorem sphere_same_third_difference_bound_oai (d : SphereEnergyData) (p : Base)
    (hrho : ContDiff ℝ ∞ (fun x ↦ d.density (sphereChartCoordMap p x)))
    (mu : ℝ) (hmu : mu ≠ 0) (C2 C3 : ℝ) (hC2 : 0 ≤ C2) (hC3 : 0 ≤ C3) :
    ∃ C > 0, ∀
    (f : SphereWeightedL2 d)
    (_ : sphereL2Resolvent d f=mu • f)
    (H : Fin 4 → Fin 4 → Lp ℝ 2 (volume.restrict (Yau.realCenteredCube 4 (1/2))))
    (J : Fin 4 → Fin 4 → Fin 4 → Lp ℝ 2 (volume.restrict (Yau.realCenteredCube 4 (1/4))))
    (_ : ∀ a k psi, ContDiff ℝ ∞ psi → HasCompactSupport psi →
      tsupport psi ⊆ Yau.realCenteredCube 4 (1/2) →
      (∫ x in Yau.realCenteredCube 4 (1/2),
        (sphereChartDerivativeMap d p a (sphereWeakSolution d f)) x*Yau.coordPartial psi x k) =
        -(∫ x in Yau.realCenteredCube 4 (1/2), H a k x*psi x))
    (_ : ∀ a k l psi, ContDiff ℝ ∞ psi → HasCompactSupport psi →
      tsupport psi ⊆ Yau.realCenteredCube 4 (1/4) →
      (∫ x in Yau.realCenteredCube 4 (1/4), H a k x*Yau.coordPartial psi x l) =
        -(∫ x in Yau.realCenteredCube 4 (1/4), J a k l x*psi x)),
      (∑ a, ∑ k, ‖H a k‖^2) ≤ C2*(‖f‖^2+‖sphereWeakSolution d f‖^2) →
      (∑ a, ∑ k, ∑ i, ‖J a k i‖^2) ≤ C3*(‖f‖^2+‖sphereWeakSolution d f‖^2) →
      ∀ (k l i : Fin 4) (h : ℝ), |h| ≤ 1/64 →
        (∀ a, MemLp (Yau.realDifferenceQuotient i h (J k l a)) 2
          (volume.restrict (Yau.realCenteredCube 4 (1/8)))) ∧
        (∑ a, ∫ x in Yau.realCenteredCube 4 (1/8),
          (Yau.realDifferenceQuotient i h (J k l a) x)^2) ≤ C*(‖f‖^2+‖sphereWeakSolution d f‖^2) := by
  obtain ⟨B,hB,hgain⟩ := sphere_interior_difference_bound d p (1/4) (1/8) (by norm_num) (by norm_num)
  obtain ⟨A,hA,hjet⟩ := sphere_same_interior_jet_bound d p C2 C3 hC2 hC3
  obtain ⟨M,hM,hforce⟩ := sphere_same_second_forcing_bound d p hrho mu C2 C3 hC2 hC3
  refine ⟨B*(A+M),by positivity,?_⟩
  intro f heigen H J hsecond hthird hH hJ k l i h hh
  let E := ‖f‖^2+‖sphereWeakSolution d f‖^2
  have hE : 0 ≤ E := by dsimp [E] <;> positivity
  have hAM : 0 ≤ (A+M)*E := by positivity
  have hAE : A*E ≤ (A+M)*E := mul_le_mul_of_nonneg_right (by linarith) hE
  have hME : M*E ≤ (A+M)*E := mul_le_mul_of_nonneg_right (by linarith) hE
  have hdata := sphere_same_second_differentiated_equation d p hrho mu hmu f heigen H J hsecond hthird k l
  have hsym := sphere_same_third_flux_symmetric d p (sphereWeakSolution d f) H J hsecond hthird
  have hjets := hjet f H J hH hJ
  have hforcing := hforce f H J hH hJ
  have hg := hgain (H k l) (fun a ↦ J k l a) (fun a ↦ J a k l) _ _ _
    (hjets.2.2.1 k l).1 (fun a ↦ Lp.memLp _) (fun a ↦ Lp.memLp _)
    (fun j ↦ (hdata.2.2 j 0).1) (fun j i ↦ (hdata.2.2 j i).2.1) hdata.1
    (fun a ↦ hsym a k l) (hthird k l)
    (fun j i psi hp hc hs ↦ ((hdata.2.2 j i).2.2 psi hp hc hs).2.2)
    (fun psi hp hc hs ↦ (hdata.2.1 psi hp hc hs).2.2.2)
    ((A+M)*E) hAM ((hjets.2.2.1 k l).2.trans hAE)
    (fun a ↦ (hjets.2.2.2 k l a).2.trans hAE)
    ((hforcing k l 0 0).1.2.trans hME)
    (fun j ↦ (hforcing k l j 0).2.1.2.trans hME)
    (fun j i ↦ (hforcing k l j i).2.2.2.trans hME) i h (by norm_num; exact hh)
  exact ⟨hg.1,by simpa only [E,mul_assoc] using hg.2⟩

end
end Yau.Target

end OAI
end

theorem solution : type_of% @OAI.Yau.Target.sphere_same_third_difference_bound_oai := @OAI.Yau.Target.sphere_same_third_difference_bound_oai
