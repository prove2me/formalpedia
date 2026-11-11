-- Prove2me | solution 1 for OAI.Yau.Target.sphere_resolvent_H1_difference_test_literal
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T00:34:57.091507+00:00
-- url     : https://prove2.me/submissions/717c51ec-2bf6-40a3-87b7-d1c8aad7db47

import Mathlib
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.ContDiff.RestrictScalars
import Mathlib.Analysis.Calculus.Deriv.Abs
import Mathlib.Analysis.Calculus.Deriv.Pi
import Mathlib.Analysis.Calculus.Deriv.Pow
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
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.Completion
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.Normed.Module.FiniteDimension
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
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
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

end
end Yau.Target

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

local instance sphereEnergyL2MapMeasurable_rccdb5c_1 : MeasurableSpace Base := borel Base
local instance sphereEnergyL2MapBorel_rccdb5c_1 : BorelSpace Base := ⟨rfl⟩
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

local instance sphereCompactChartTestingMeasurable_rccdb5c_1 : MeasurableSpace Base := borel Base
local instance sphereCompactChartTestingBorel_rccdb5c_1 : BorelSpace Base := ⟨rfl⟩
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
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_CompactFluxGreen
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

theorem weightedDiv_hasCompactSupport (gamma : Coord n → ℝ) (V : Coord n → Coord n)
    (hc : ∀ i, HasCompactSupport (fun x ↦ V x i)) :
    HasCompactSupport (weightedDiv gamma V) := by
  have h := HasCompactSupport.finset_sum (s := Finset.univ)
    (fun i _ ↦ ((hc i).mul_left (f := gamma)).fderiv_apply ℝ (Pi.single i 1))
  convert h.mul_left (f := fun x ↦ (gamma x)⁻¹) using 1
  all_goals try with_reducible_and_instances rfl
  first | rfl | (ext x; simp only [weightedDiv,coordDiv,coordPartial,Pi.mul_apply,Finset.sum_apply]; rfl)

theorem compact_flux_weighted_integration_by_parts (gamma phi : Coord n → ℝ)
    (hg : ContDiff ℝ ∞ gamma) (hgn : ∀ x, gamma x ≠ 0)
    (hphi : ContDiff ℝ ∞ phi)
    (V : Coord n → Coord n) (hV : ∀ i, ContDiff ℝ ∞ (fun x ↦ V x i))
    (hc : ∀ i, HasCompactSupport (fun x ↦ V x i)) :
    Integrable (fun x ↦ gamma x*pairing phi V x) ∧
    Integrable (fun x ↦ gamma x*phi x*weightedDiv gamma V x) ∧
    (∫ x, gamma x*pairing phi V x) = -(∫ x, gamma x*phi x*weightedDiv gamma V x) := by
  have hp : HasCompactSupport (pairing phi V) := by
    unfold pairing
    have h := HasCompactSupport.finset_sum (s := Finset.univ)
      (fun i _ ↦ (hc i).mul_left (f := fun x ↦ coordPartial phi x i))
    convert h using 1
    all_goals try with_reducible_and_instances rfl
    first | rfl | (ext x; simp only [Finset.sum_apply,Pi.mul_apply])
  have hiP : Integrable (fun x ↦ gamma x*pairing phi V x) :=
    (hg.mul (pairing_smooth hphi hV)).continuous.integrable_of_hasCompactSupport hp.mul_left
  have hiD : Integrable (fun x ↦ gamma x*phi x*weightedDiv gamma V x) :=
    ((hg.mul hphi).mul (weightedDiv_smooth hg hgn hV)).continuous.integrable_of_hasCompactSupport
      (weightedDiv_hasCompactSupport gamma V hc).mul_left
  obtain ⟨_,hz⟩ := integral_weightedDiv_compact_zero gamma hg hgn
    (fun x i ↦ phi x*V x i) (fun i ↦ hphi.mul (hV i)) (fun i ↦ (hc i).mul_left)
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

local instance sphereChartWeakDerivativeMeasurable_rccdb5c_1 : MeasurableSpace Base := borel Base
local instance sphereChartWeakDerivativeBorel_rccdb5c_1 : BorelSpace Base := ⟨rfl⟩
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

theorem realL2DifferenceQuotient_ae {n : ℕ} (i : Fin n) (h : ℝ) (f : RealEuclideanL2 n) :
    (realL2DifferenceQuotient i h f : (Fin n → ℝ) → ℝ) =ᵐ[volume] realDifferenceQuotient i h f := by
  filter_upwards [Lp.coeFn_smul h⁻¹ (realL2Translate ((Pi.single i h : Fin n → ℝ)) f-f),
    Lp.coeFn_sub (realL2Translate ((Pi.single i h : Fin n → ℝ)) f) f,
    realL2Translate_ae ((Pi.single i h : Fin n → ℝ)) f] with x h1 h2 h3
  change (h⁻¹ • (realL2Translate ((Pi.single i h : Fin n → ℝ)) f-f)) x = _
  rw [h1]
  change h⁻¹*((realL2Translate ((Pi.single i h : Fin n → ℝ)) f-f) x) = _
  rw [h2]
  change h⁻¹*((realL2Translate ((Pi.single i h : Fin n → ℝ)) f) x-f x) = _
  rw [h3]
  rfl

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

theorem realDifferenceQuotient_compact {n : ℕ} (i : Fin n) (h : ℝ)
    (u : Coord n → ℝ) (hc : HasCompactSupport u) :
    HasCompactSupport (realDifferenceQuotient i h u) :=
  ((hc.comp_homeomorph (Homeomorph.addRight (Pi.single i h))).sub hc).mul_left

theorem realDifferenceQuotient_partial {n : ℕ} (i j : Fin n) (h : ℝ)
    (u : Coord n → ℝ) (hu : ContDiff ℝ ∞ u) (x : Coord n) :
    coordPartial (realDifferenceQuotient i h u) x j =
      realDifferenceQuotient i h (fun y ↦ coordPartial u y j) x := by
  have ht : ContDiff ℝ ∞ (fun y ↦ u (y+Pi.single i h)) :=
    hu.comp (contDiff_id.add contDiff_const)
  unfold realDifferenceQuotient
  rw [real_coordPartial_const_mul _ (ht.sub hu)]
  unfold coordPartial
  rw [fderiv_fun_sub (ht.differentiable (by simp) x) (hu.differentiable (by simp) x),
    fderiv_comp_add_right]
  rfl

theorem realDifferenceQuotient_tsupport {n : ℕ} (i : Fin n) (h : ℝ)
    (u : Coord n → ℝ) {K : Set (Coord n)} (hK : IsClosed K)
    (hs : tsupport u ⊆ K) (ht : ∀ x, x+Pi.single i h ∈ tsupport u → x ∈ K) :
    tsupport (realDifferenceQuotient i h u) ⊆ K := by
  apply closure_minimal _ hK
  intro x hx
  by_contra hn
  have h1 : u x=0 := image_eq_zero_of_notMem_tsupport (fun h ↦ hn (hs h))
  have h2 : u (x+Pi.single i h)=0 := image_eq_zero_of_notMem_tsupport (fun h ↦ hn (ht x h))
  exact hx (by simp [realDifferenceQuotient,h1,h2])

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
-- module Solutions.OAIQ237_NY.NodalSets_Charts_SphereChartValueMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open MeasureTheory Yau.Geometry
noncomputable section

local instance sphereChartValueMapMeasurable_rccdb5c_1 : MeasurableSpace Base := borel Base
local instance sphereChartValueMapBorel_rccdb5c_1 : BorelSpace Base := ⟨rfl⟩
theorem sphereChartValueMap_ae (d : SphereEnergyData) (p : Base) (f : SphereWeightedL2 d) :
    (sphereChartValueMap d p f : Yau.Jets.Coord → ℝ) =ᵐ[volume.restrict (realFinCube 4)]
      (fun x ↦ f (sphereChartCoordMap p x)) := (sphereChartValue_memLp d p f).coeFn_toLp

theorem sphereChartValueMap_coe_ae (d : SphereEnergyData) (p : Base) (u : SphereEnergySmooth d) :
    (sphereChartValueMap d p (sphereEnergyL2Map d (sphereEnergyToCompletion d u)) : Yau.Jets.Coord → ℝ)
      =ᵐ[volume.restrict (realFinCube 4)]
      (fun x ↦ (SphereEnergySmooth.toSmooth d u : Base → ℝ) (sphereChartCoordMap p x)) := by
  rw [sphereEnergyL2Map_coe]
  apply (sphereChartValueMap_ae d p (sphereEnergyL2Linear d u)).trans
  apply ae_restrict_of_ae
  apply (sphereWeightedMeasure_ae_chart_iff d p (fun x ↦ (sphereEnergyL2Linear d u) x =
    (SphereEnergySmooth.toSmooth d u : Base → ℝ) x)).mp
  exact (sphereWeighted_memLp d.density d.continuous (fun x ↦ (d.positive x).le)
    (SphereEnergySmooth.toSmooth d u) (SphereEnergySmooth.toSmooth d u).property.continuous).coeFn_toLp

end
end Yau.Target

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

theorem realCompactL2Map_ae {n : ℕ} {K : Set (Fin n → ℝ)} (hK : IsCompact K)
    (eta : (Fin n → ℝ) → ℝ) (he : Continuous eta) (hs : tsupport eta ⊆ K)
    (u : Lp ℝ 2 (volume.restrict K)) :
    (realCompactL2Map hK eta he hs u : (Fin n → ℝ) → ℝ) =ᵐ[volume] (fun x ↦ eta x*u x) :=
  (real_compact_localL2_product hK eta u he hs (Lp.memLp u)).coeFn_toLp

end Yau

end

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Charts_SphereChartCutoffApproximation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open MeasureTheory Yau.Geometry Set Filter
open scoped ContDiff Topology
noncomputable section

local instance sphereChartCutoffApproxMeasurable_rccdb5c_1 : MeasurableSpace Base := borel Base
local instance sphereChartCutoffApproxBorel_rccdb5c_1 : BorelSpace Base := ⟨rfl⟩
theorem sphereCutoffValueMap_ae (d : SphereEnergyData) (p : Base)
    (eta : Yau.Jets.Coord → ℝ) (he : ContDiff ℝ ∞ eta)
    (hs : tsupport eta ⊆ realFinCube 4) (z : SphereEnergyHilbert d) :
    (sphereCutoffValueMap d p eta he hs z : Yau.Jets.Coord → ℝ) =ᵐ[volume]
      (fun x ↦ eta x*(sphereEnergyL2Map d z) (sphereChartCoordMap p x)) :=
  (Yau.realCompactL2Map_ae (realFinCube_isCompact 4) eta he.continuous hs _).trans
    (Yau.real_compact_mul_ae (realFinCube_isCompact 4).measurableSet eta _ _ hs
      (sphereChartValueMap_ae d p (sphereEnergyL2Map d z)))

theorem sphereCutoffDerivativeMap_ae (d : SphereEnergyData) (p : Base)
    (eta : Yau.Jets.Coord → ℝ) (he : ContDiff ℝ ∞ eta)
    (hs : tsupport eta ⊆ realFinCube 4) (i : Fin 4) (z : SphereEnergyHilbert d) :
    (sphereCutoffDerivativeMap d p eta he hs i z : Yau.Jets.Coord → ℝ) =ᵐ[volume]
      (fun x ↦ eta x*(sphereChartDerivativeMap d p i z) x+
        Yau.coordPartial eta x i*(sphereEnergyL2Map d z) (sphereChartCoordMap p x)) := by
  have hd := (tsupport_fderiv_apply_subset ℝ (Pi.single i 1) (f := eta)).trans hs
  have h1 := Yau.realCompactL2Map_ae (realFinCube_isCompact 4) eta he.continuous hs
    (sphereChartDerivativeMap d p i z)
  have h2 := (Yau.realCompactL2Map_ae (realFinCube_isCompact 4) _
    (Yau.real_coordPartial_smooth eta he i).continuous hd
    (sphereChartValueMap d p (sphereEnergyL2Map d z))).trans
      (Yau.real_compact_mul_ae (realFinCube_isCompact 4).measurableSet _ _ _ hd
        (sphereChartValueMap_ae d p (sphereEnergyL2Map d z)))
  exact (Lp.coeFn_add _ _).trans (h1.add h2)

theorem sphereCutoffValueMap_smooth_ae (d : SphereEnergyData) (p : Base)
    (eta : Yau.Jets.Coord → ℝ) (he : ContDiff ℝ ∞ eta)
    (hs : tsupport eta ⊆ realFinCube 4) (u : SphereEnergySmooth d) :
    (sphereCutoffValueMap d p eta he hs (sphereEnergyToCompletion d u) : Yau.Jets.Coord → ℝ)
      =ᵐ[volume] (fun x ↦ eta x*(SphereEnergySmooth.toSmooth d u : Base → ℝ) (sphereChartCoordMap p x)) :=
  (Yau.realCompactL2Map_ae (realFinCube_isCompact 4) eta he.continuous hs _).trans
    (Yau.real_compact_mul_ae (realFinCube_isCompact 4).measurableSet eta _ _ hs
      (sphereChartValueMap_coe_ae d p u))

theorem sphereCutoffDerivativeMap_smooth_ae (d : SphereEnergyData) (p : Base)
    (eta : Yau.Jets.Coord → ℝ) (he : ContDiff ℝ ∞ eta)
    (hs : tsupport eta ⊆ realFinCube 4) (i : Fin 4) (u : SphereEnergySmooth d) :
    (sphereCutoffDerivativeMap d p eta he hs i (sphereEnergyToCompletion d u) : Yau.Jets.Coord → ℝ)
      =ᵐ[volume] (fun x ↦ Yau.coordPartial
        (fun y ↦ eta y*(SphereEnergySmooth.toSmooth d u : Base → ℝ) (sphereChartCoordMap p y)) x i) := by
  have hd := (tsupport_fderiv_apply_subset ℝ (Pi.single i 1) (f := eta)).trans hs
  have hpart : (sphereChartDerivativeMap d p i (sphereEnergyToCompletion d u) : Yau.Jets.Coord → ℝ)
      =ᵐ[volume.restrict (realFinCube 4)] sphereSmoothChartPartial d p i u := by
    rw [sphereChartDerivativeMap_coe]
    exact (sphereSmoothChartPartial_memLp d p i u).coeFn_toLp
  have h1 := (Yau.realCompactL2Map_ae (realFinCube_isCompact 4) eta he.continuous hs
    (sphereChartDerivativeMap d p i (sphereEnergyToCompletion d u))).trans
      (Yau.real_compact_mul_ae (realFinCube_isCompact 4).measurableSet eta _ _ hs hpart)
  have h2 := (Yau.realCompactL2Map_ae (realFinCube_isCompact 4) _
    (Yau.real_coordPartial_smooth eta he i).continuous hd
    (sphereChartValueMap d p (sphereEnergyL2Map d (sphereEnergyToCompletion d u)))).trans
      (Yau.real_compact_mul_ae (realFinCube_isCompact 4).measurableSet _ _ _ hd
        (sphereChartValueMap_coe_ae d p u))
  apply ((Lp.coeFn_add _ _).trans (h1.add h2)).trans
  apply Filter.Eventually.of_forall
  intro x
  have hp := Yau.real_coordPartial_mul eta _ he
    (spherePullback_smooth _ (SphereEnergySmooth.toSmooth d u).property p) x i
  simp only [Function.comp_def] at hp
  simp only [Pi.add_apply,sphereSmoothChartPartial,Function.comp_def]
  rw [hp]
  ring

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Charts_SphereChartTestFlux
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Set
open scoped ContDiff
noncomputable section

theorem sphereChartTestFlux_smooth (d : SphereEnergyData) (p : Base)
    (phi : Yau.Jets.Coord → ℝ) (hp : ContDiff ℝ ∞ phi) (i : Fin 4) :
    ContDiff ℝ ∞ (fun x ↦ sphereChartTestFlux d p phi x i) :=
  roundCoordDensity_smooth.mul (ContDiff.sum (fun j _ ↦
    (intrinsicRealPrincipal_smooth d.tensor d.smooth d.symm d.pos p i j).mul
      (Yau.real_coordPartial_smooth phi hp j)))

theorem sphereChartTestFlux_tsupport (d : SphereEnergyData) (p : Base)
    (phi : Yau.Jets.Coord → ℝ) (i : Fin 4) :
    tsupport (fun x ↦ sphereChartTestFlux d p phi x i) ⊆ tsupport phi := by
  apply closure_minimal _ (isClosed_tsupport phi)
  intro x hx
  by_contra hn
  have hd : fderiv ℝ phi x = 0 := fderiv_of_notMem_tsupport ℝ hn
  have hz : sphereChartTestFlux d p phi x i = 0 := by
    simp [sphereChartTestFlux,Yau.coordPartial,hd]
  exact hx hz

theorem sphereChartTestFlux_compact (d : SphereEnergyData) (p : Base)
    (phi : Yau.Jets.Coord → ℝ) (hc : HasCompactSupport phi) (i : Fin 4) :
    HasCompactSupport (fun x ↦ sphereChartTestFlux d p phi x i) :=
  hc.of_isClosed_subset (isClosed_tsupport _) (sphereChartTestFlux_tsupport d p phi i)

theorem sphereChartTestFlux_div_tsupport (d : SphereEnergyData) (p : Base)
    (phi : Yau.Jets.Coord → ℝ) :
    tsupport (Yau.coordDiv (sphereChartTestFlux d p phi)) ⊆ tsupport phi := by
  apply closure_minimal _ (isClosed_tsupport phi)
  intro x hx
  by_contra hn
  have hd (i : Fin 4) : fderiv ℝ (fun y ↦ sphereChartTestFlux d p phi y i) x = 0 :=
    fderiv_of_notMem_tsupport ℝ (fun h ↦ hn (sphereChartTestFlux_tsupport d p phi i h))
  have hz : Yau.coordDiv (sphereChartTestFlux d p phi) x = 0 := by
    simp [Yau.coordDiv,Yau.coordPartial,hd]
  exact hx hz

theorem sphereChartTestFlux_div (d : SphereEnergyData) (p : Base)
    (phi : Yau.Jets.Coord → ℝ) (x : Yau.Jets.Coord) :
    Yau.coordDiv (sphereChartTestFlux d p phi) x = roundCoordDensity x *
      Yau.weightedDiv roundCoordDensity
        (fun y i ↦ ∑ j, intrinsicRealPrincipal d.tensor p y i j*Yau.coordPartial phi y j) x := by
  simp only [Yau.weightedDiv,← mul_assoc,mul_inv_cancel₀ (roundCoordDensity_pos x).ne',one_mul]
  rfl

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Charts_SphereChartWeakDivergence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open MeasureTheory Yau.Geometry Set
open scoped ContDiff
noncomputable section

local instance sphereChartWeakDivergenceMeasurable_rccdb5c_1 : MeasurableSpace Base := borel Base
local instance sphereChartWeakDivergenceBorel_rccdb5c_1 : BorelSpace Base := ⟨rfl⟩
theorem sphere_chart_weak_divergence (d : SphereEnergyData) (p : Base) (z : SphereEnergyHilbert d)
    (V : Yau.Jets.Coord → Yau.Jets.Coord)
    (hV : ∀ i, ContDiff ℝ ∞ (fun x ↦ V x i))
    (hc : ∀ i, HasCompactSupport (fun x ↦ V x i))
    (hs : ∀ i, tsupport (fun x ↦ V x i) ⊆ realFinCube 4) :
    IntegrableOn (fun x ↦ ∑ i, (sphereChartDerivativeMap d p i z) x*V x i) (realFinCube 4) ∧
    IntegrableOn (fun x ↦ (sphereEnergyL2Map d z) (sphereChartCoordMap p x)*Yau.coordDiv V x)
      (realFinCube 4) ∧
    (∫ x in realFinCube 4, ∑ i, (sphereChartDerivativeMap d p i z) x*V x i) =
      -(∫ x in realFinCube 4, (sphereEnergyL2Map d z) (sphereChartCoordMap p x)*Yau.coordDiv V x) := by
  have h (i : Fin 4) := sphere_chart_weak_derivative d p i z (fun x ↦ V x i) (hV i) (hc i) (hs i)
  have hleft := integrable_finsetSum Finset.univ (fun i _ ↦ (h i).1)
  have hright := integrable_finsetSum Finset.univ (fun i _ ↦ (h i).2.1)
  have he : (fun x ↦ (sphereEnergyL2Map d z) (sphereChartCoordMap p x)*Yau.coordDiv V x) =
      (fun x ↦ ∑ i, (sphereEnergyL2Map d z) (sphereChartCoordMap p x)*Yau.coordPartial (fun y ↦ V y i) x i) := by
    funext x
    simp only [Yau.coordDiv,Finset.mul_sum]
  rw [he]
  refine ⟨hleft,hright,?_⟩
  rw [integral_finsetSum _ (fun i _ ↦ (h i).1),integral_finsetSum _ (fun i _ ↦ (h i).2.1)]
  simp only [(h _).2.2,Finset.sum_neg_distrib]

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Charts_SphereCompactFluxGreen
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Manifold Yau.Geometry MeasureTheory
open scoped ContDiff
noncomputable section

theorem sphereChartFlux_hasCompactSupport (A : IntrinsicTensor) (v : Base → ℝ) (p : Base)
    (hc : HasCompactSupport (v ∘ sphereChartCoordMap p)) (i : Fin 4) :
    HasCompactSupport (fun x ↦ sphereChartFlux A v p x i) := by
  have h := HasCompactSupport.finset_sum (s := Finset.univ) (fun j _ ↦
    (hc.fderiv_apply ℝ (Pi.single j 1)).mul_left
      (f := fun x ↦ intrinsicRealPrincipal A p x i j))
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  rfl

theorem sphere_smooth_green_compact_flux (A : IntrinsicTensor) (hA : IntrinsicTensorSmooth A)
    (hs : ∀ x alpha beta, A x alpha beta = A x beta alpha)
    (hp : ∀ x alpha, alpha ≠ 0 → 0 < A x alpha alpha)
    (u v : Base → ℝ) (hu : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ u)
    (hv : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ v) (p : Base)
    (hc : HasCompactSupport (v ∘ sphereChartCoordMap p)) :
    Integrable (fun x ↦ roundCoordDensity x*u (sphereChartCoordMap p x)*
      Yau.weightedDiv roundCoordDensity (sphereChartFlux A v p) x) ∧
    sphereDirichletForm A u v = -(∫ x, roundCoordDensity x*u (sphereChartCoordMap p x)*
      Yau.weightedDiv roundCoordDensity (sphereChartFlux A v p) x) := by
  have h := Yau.compact_flux_weighted_integration_by_parts roundCoordDensity
    (u ∘ sphereChartCoordMap p) roundCoordDensity_smooth (fun x ↦ (roundCoordDensity_pos x).ne')
    (spherePullback_smooth u hu p) (sphereChartFlux A v p)
    (intrinsicRealVector_smooth A hA hs hp v hv p) (sphereChartFlux_hasCompactSupport A v p hc)
  refine ⟨h.2.1,?_⟩
  rw [sphereDirichletForm,sphereReferenceMeasure_integral_chart p]
  simp only [roundChartDensity_coord_eq,intrinsic_differential_pair_chart A u v hu hv]
  simpa only [Yau.pairing,sphereChartFlux,Function.comp_apply,Finset.mul_sum,mul_assoc] using h.2.2

theorem sphere_compact_test_divergence_extension (A : IntrinsicTensor) (hA : IntrinsicTensorSmooth A)
    (hs : ∀ x alpha beta, A x alpha beta = A x beta alpha)
    (hp : ∀ x alpha, alpha ≠ 0 → 0 < A x alpha alpha)
    (p : Base) (phi : Yau.Jets.Coord → ℝ) (hphi : ContDiff ℝ ∞ phi)
    (hc : HasCompactSupport phi) :
    ∃ v g : Base → ℝ, ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ v ∧
      ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ g ∧
      (∀ x, v (sphereChartCoordMap p x) = phi x) ∧
      (∀ x, g (sphereChartCoordMap p x) = Yau.weightedDiv roundCoordDensity
        (fun y i ↦ ∑ j, intrinsicRealPrincipal A p y i j*Yau.coordPartial phi y j) x) ∧
      ∀ u : Base → ℝ, ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ u →
        sphereDirichletForm A u v = -(∫ x, u x*g x ∂sphereReferenceMeasure) := by
  obtain ⟨v,hv,_,hval⟩ := sphere_chart_scalar_extension p phi hphi hc
  have hcomp : v ∘ sphereChartCoordMap p = phi := funext hval
  have hvc : HasCompactSupport (v ∘ sphereChartCoordMap p) := hcomp ▸ hc
  let D := Yau.weightedDiv roundCoordDensity (sphereChartFlux A v p)
  have hD : ContDiff ℝ ∞ D := Yau.weightedDiv_smooth roundCoordDensity_smooth
    (fun x ↦ (roundCoordDensity_pos x).ne') (intrinsicRealVector_smooth A hA hs hp v hv p)
  have hDc : HasCompactSupport D := Yau.weightedDiv_hasCompactSupport _ _
    (sphereChartFlux_hasCompactSupport A v p hvc)
  obtain ⟨g,hg,_,hgval⟩ := sphere_chart_scalar_extension p D hD hDc
  refine ⟨v,g,hv,hg,hval,?_,?_⟩
  · intro x
    rw [hgval]
    change Yau.weightedDiv roundCoordDensity (sphereChartFlux A v p) x = _
    have hflux : sphereChartFlux A v p =
        (fun y i ↦ ∑ j, intrinsicRealPrincipal A p y i j*Yau.coordPartial phi y j) := by
      unfold sphereChartFlux
      rw [hcomp]
    rw [hflux]
  · intro u hu
    rw [(sphere_smooth_green_compact_flux A hA hs hp u v hu hv p hvc).2,
      sphereReferenceMeasure_integral_chart p]
    simp only [roundChartDensity_coord_eq,hgval,D,mul_assoc]

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

local instance sphereWeakResolventMeasurable_rccdb5c_1 : MeasurableSpace Base := borel Base
local instance sphereWeakResolventBorel_rccdb5c_1 : BorelSpace Base := ⟨rfl⟩
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

theorem sphereWeakSolution_spec (d : SphereEnergyData) (f : SphereWeightedL2 d) (v : SphereEnergyHilbert d) :
    inner ℝ (sphereWeakSolution d f) v = inner ℝ f (sphereEnergyL2Map d v) :=
  (sphereEnergyL2Map d).adjoint_inner_left v f

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Charts_SphereCompletedGreenTest
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open MeasureTheory
noncomputable section

local instance sphereCompletedGreenTestMeasurable_rccdb5c_1 : MeasurableSpace Base := borel Base
local instance sphereCompletedGreenTestBorel_rccdb5c_1 : BorelSpace Base := ⟨rfl⟩
theorem sphere_completed_green_test (d : SphereEnergyData) (v : SphereEnergySmooth d)
    (g : Base → ℝ) (hg : Continuous g)
    (hgreen : ∀ u : SphereEnergySmooth d,
      sphereDirichletForm d.tensor (SphereEnergySmooth.toSmooth d u) (SphereEnergySmooth.toSmooth d v) =
        -(∫ x, (SphereEnergySmooth.toSmooth d u : Base → ℝ) x*g x ∂sphereReferenceMeasure))
    (z : SphereEnergyHilbert d) :
    sphereCompletedDirichlet d z (sphereEnergyToCompletion d v) =
      -inner ℝ (sphereEnergyL2Map d z)
        (sphereWeightedToLp d.density d.continuous (fun x ↦ (d.positive x).le)
          (fun x ↦ g x/d.density x) (hg.div d.continuous (fun x ↦ (d.positive x).ne'))) := by
  let G := sphereWeightedToLp d.density d.continuous (fun x ↦ (d.positive x).le)
    (fun x ↦ g x/d.density x) (hg.div d.continuous (fun x ↦ (d.positive x).ne'))
  change sphereCompletedDirichlet d z (sphereEnergyToCompletion d v) = -inner ℝ (sphereEnergyL2Map d z) G
  apply (sphereEnergyToCompletion_dense d).induction_on
    (p := fun z ↦ sphereCompletedDirichlet d z (sphereEnergyToCompletion d v) =
      -inner ℝ (sphereEnergyL2Map d z) G) z
  · apply isClosed_eq
    · exact (continuous_id.inner continuous_const).sub
        ((sphereEnergyL2Map d).continuous.inner continuous_const)
    · exact ((sphereEnergyL2Map d).continuous.inner continuous_const).neg
  · intro u
    rw [sphereCompletedDirichlet_coe,hgreen,sphereEnergyL2Map_coe]
    change -(∫ x, (SphereEnergySmooth.toSmooth d u : Base → ℝ) x*g x ∂sphereReferenceMeasure) =
      -inner ℝ (sphereWeightedToLp d.density d.continuous (fun x ↦ (d.positive x).le)
        (SphereEnergySmooth.toSmooth d u) (SphereEnergySmooth.toSmooth d u).property.continuous) G
    rw [sphereWeightedToLp_inner]
    congr 1
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun x ↦ by
      change _ = d.density x*(SphereEnergySmooth.toSmooth d u : Base → ℝ) x*(g x/d.density x)
      field_simp [(d.positive x).ne'])

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Spectral_SphereResolventDistribution
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Manifold MeasureTheory
open scoped ContDiff
noncomputable section

local instance sphereResolventDistributionMeasurable_rccdb5c_1 : MeasurableSpace Base := borel Base
local instance sphereResolventDistributionBorel_rccdb5c_1 : BorelSpace Base := ⟨rfl⟩
theorem sphere_resolvent_chart_distribution (d : SphereEnergyData) (f : SphereWeightedL2 d)
    (p : Base) (phi : Yau.Jets.Coord → ℝ) (hphi : ContDiff ℝ ∞ phi)
    (hc : HasCompactSupport phi) :
    let w := sphereL2Resolvent d f
    let D := Yau.weightedDiv roundCoordDensity
      (fun y i ↦ ∑ j, intrinsicRealPrincipal d.tensor p y i j*Yau.coordPartial phi y j)
    Integrable (fun y ↦ roundCoordDensity y*w (sphereChartCoordMap p y)*
      (d.density (sphereChartCoordMap p y)*phi y-D y)) ∧
    Integrable (fun y ↦ roundCoordDensity y*d.density (sphereChartCoordMap p y)*
      f (sphereChartCoordMap p y)*phi y) ∧
    (∫ y, roundCoordDensity y*w (sphereChartCoordMap p y)*
      (d.density (sphereChartCoordMap p y)*phi y-D y)) =
      ∫ y, roundCoordDensity y*d.density (sphereChartCoordMap p y)*
        f (sphereChartCoordMap p y)*phi y := by
  dsimp only
  let w := sphereL2Resolvent d f
  let D := Yau.weightedDiv roundCoordDensity
    (fun y i ↦ ∑ j, intrinsicRealPrincipal d.tensor p y i j*Yau.coordPartial phi y j)
  obtain ⟨v,g,hv,hg,hval,hgval,hgreen⟩ := sphere_compact_test_divergence_extension
    d.tensor d.smooth d.symm d.pos p phi hphi hc
  let V : SphereEnergySmooth d := ⟨v,hv⟩
  have hgq : Continuous (fun x ↦ g x/d.density x) :=
    hg.continuous.div d.continuous (fun x ↦ (d.positive x).ne')
  let G := sphereWeightedToLp d.density d.continuous (fun x ↦ (d.positive x).le) _ hgq
  obtain ⟨hvi,hve⟩ := sphereWeightedL2_test_chart d w v hv.continuous p
  obtain ⟨hfi,hfe⟩ := sphereWeightedL2_test_chart d f v hv.continuous p
  obtain ⟨hgi,hge⟩ := sphereWeightedL2_test_chart d w _ hgq p
  simp only [hval] at hvi hve hfi hfe
  have heG : (fun y ↦ roundCoordDensity y*d.density (sphereChartCoordMap p y)*
      w (sphereChartCoordMap p y)*(g (sphereChartCoordMap p y)/d.density (sphereChartCoordMap p y))) =
      (fun y ↦ roundCoordDensity y*w (sphereChartCoordMap p y)*D y) := by
    funext y
    rw [hgval]
    dsimp only [D]
    field_simp [(d.positive (sphereChartCoordMap p y)).ne']
  rw [heG] at hgi hge
  have heS : (fun y ↦ roundCoordDensity y*w (sphereChartCoordMap p y)*
      (d.density (sphereChartCoordMap p y)*phi y-D y)) =
      (fun y ↦ roundCoordDensity y*d.density (sphereChartCoordMap p y)*w (sphereChartCoordMap p y)*phi y -
        roundCoordDensity y*w (sphereChartCoordMap p y)*D y) := by
    funext y
    ring
  have hweak := sphereWeakSolution_spec d f (sphereEnergyToCompletion d V)
  have hcompleted := sphere_completed_green_test d V g hg.continuous
    (fun u ↦ hgreen (SphereEnergySmooth.toSmooth d u) (SphereEnergySmooth.toSmooth d u).property)
    (sphereWeakSolution d f)
  rw [sphereCompletedDirichlet,sphereEnergyL2Map_coe] at hcompleted
  rw [sphereEnergyL2Map_coe] at hweak
  change inner ℝ (sphereWeakSolution d f) (sphereEnergyToCompletion d V) -
    inner ℝ w (sphereEnergyL2Linear d V) = -inner ℝ w G at hcompleted
  change inner ℝ w (sphereEnergyL2Linear d V) = _ at hve
  change inner ℝ f (sphereEnergyL2Linear d V) = _ at hfe
  change inner ℝ w G = _ at hge
  change Integrable (fun y ↦ roundCoordDensity y*w (sphereChartCoordMap p y)*
      (d.density (sphereChartCoordMap p y)*phi y-D y)) ∧ _
  rw [heS]
  refine ⟨hvi.sub hgi,hfi,?_⟩
  rw [integral_sub hvi hgi,← hve,← hge,← hfe]
  linarith

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Spectral_SphereResolventVariational
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open MeasureTheory Yau.Geometry Set
open scoped ContDiff
noncomputable section

local instance sphereResolventVariationalMeasurable_rccdb5c_1 : MeasurableSpace Base := borel Base
local instance sphereResolventVariationalBorel_rccdb5c_1 : BorelSpace Base := ⟨rfl⟩
theorem sphereWeightedL2_compact_test_integrable (d : SphereEnergyData) (f : SphereWeightedL2 d)
    (p : Base) (phi : Yau.Jets.Coord → ℝ) (hp : ContDiff ℝ ∞ phi)
    (hc : HasCompactSupport phi) :
    Integrable (fun x ↦ roundCoordDensity x*d.density (sphereChartCoordMap p x)*
      f (sphereChartCoordMap p x)*phi x) := by
  obtain ⟨v,hv,_,hval⟩ := sphere_chart_scalar_extension p phi hp hc
  have h := (sphereWeightedL2_test_chart d f v hv.continuous p).1
  simpa only [hval] using h

theorem sphere_resolvent_chart_variational (d : SphereEnergyData) (f : SphereWeightedL2 d)
    (p : Base) (phi : Yau.Jets.Coord → ℝ) (hp : ContDiff ℝ ∞ phi)
    (hc : HasCompactSupport phi) (hs : tsupport phi ⊆ realFinCube 4) :
    let z := sphereWeakSolution d f
    let w := sphereEnergyL2Map d z
    let F := fun x ↦ roundCoordDensity x * ∑ i, (sphereChartDerivativeMap d p i z) x *
      (∑ j, intrinsicRealPrincipal d.tensor p x i j*Yau.coordPartial phi x j)
    let M := fun x ↦ roundCoordDensity x*d.density (sphereChartCoordMap p x)*
      w (sphereChartCoordMap p x)*phi x
    let R := fun x ↦ roundCoordDensity x*d.density (sphereChartCoordMap p x)*
      f (sphereChartCoordMap p x)*phi x
    IntegrableOn F (realFinCube 4) ∧ IntegrableOn M (realFinCube 4) ∧
      IntegrableOn R (realFinCube 4) ∧
      (∫ x in realFinCube 4, F x)+(∫ x in realFinCube 4, M x) = ∫ x in realFinCube 4, R x := by
  dsimp only
  let z := sphereWeakSolution d f
  let w := sphereEnergyL2Map d z
  let V := sphereChartTestFlux d p phi
  let M := fun x ↦ roundCoordDensity x*d.density (sphereChartCoordMap p x)*w (sphereChartCoordMap p x)*phi x
  let R := fun x ↦ roundCoordDensity x*d.density (sphereChartCoordMap p x)*f (sphereChartCoordMap p x)*phi x
  let D := fun x ↦ w (sphereChartCoordMap p x)*Yau.coordDiv V x
  obtain ⟨hF,hD,hweak⟩ := sphere_chart_weak_divergence d p z V
    (sphereChartTestFlux_smooth d p phi hp) (sphereChartTestFlux_compact d p phi hc)
    (fun i ↦ (sphereChartTestFlux_tsupport d p phi i).trans hs)
  have hM := sphereWeightedL2_compact_test_integrable d w p phi hp hc
  have hR := sphereWeightedL2_compact_test_integrable d f p phi hp hc
  have heF : (fun x ↦ ∑ i, (sphereChartDerivativeMap d p i z) x*V x i) =
      (fun x ↦ roundCoordDensity x * ∑ i, (sphereChartDerivativeMap d p i z) x *
        (∑ j, intrinsicRealPrincipal d.tensor p x i j*Yau.coordPartial phi x j)) := by
    funext x
    simp only [V,sphereChartTestFlux,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring_nf
  rw [heF] at hF hweak
  have hdist := (sphere_resolvent_chart_distribution d f p phi hp hc).2.2
  have heDist : (fun x ↦ roundCoordDensity x*(sphereL2Resolvent d f) (sphereChartCoordMap p x)*
      (d.density (sphereChartCoordMap p x)*phi x - Yau.weightedDiv roundCoordDensity
        (fun y i ↦ ∑ j, intrinsicRealPrincipal d.tensor p y i j*Yau.coordPartial phi y j) x)) =
      fun x ↦ M x-D x := by
    funext x
    dsimp only [M,D,V]
    rw [sphereChartTestFlux_div]
    change roundCoordDensity x*w (sphereChartCoordMap p x)*_ = _
    ring
  rw [heDist] at hdist
  have hzM (x : Yau.Jets.Coord) (hx : x ∉ realFinCube 4) : M x=0 := by
    dsimp only [M]
    rw [image_eq_zero_of_notMem_tsupport (fun h ↦ hx (hs h)),mul_zero]
  have hzR (x : Yau.Jets.Coord) (hx : x ∉ realFinCube 4) : R x=0 := by
    dsimp only [R]
    rw [image_eq_zero_of_notMem_tsupport (fun h ↦ hx (hs h)),mul_zero]
  have hzD (x : Yau.Jets.Coord) (hx : x ∉ realFinCube 4) : D x=0 := by
    dsimp only [D,V]
    rw [image_eq_zero_of_notMem_tsupport (fun h ↦ hx (hs (sphereChartTestFlux_div_tsupport d p phi h))),mul_zero]
  have hMD : (∫ x in realFinCube 4, M x-D x) = ∫ x, M x-D x :=
    setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx ↦ by rw [hzM x hx,hzD x hx,sub_self])
  have hReq : (∫ x in realFinCube 4, R x) = ∫ x, R x :=
    setIntegral_eq_integral_of_forall_compl_eq_zero hzR
  change (∫ x, M x-D x) = ∫ x, R x at hdist
  rw [← hMD,← hReq,integral_sub hM.integrableOn hD] at hdist
  refine ⟨hF,hM.integrableOn,hR.integrableOn,?_⟩
  change _+(∫ x in realFinCube 4, M x) = ∫ x in realFinCube 4, R x
  linarith only [hweak,hdist]

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

local instance sphereChartDivergenceDataMeasurable_rccdb5c_1 : MeasurableSpace Base := borel Base
local instance sphereChartDivergenceDataBorel_rccdb5c_1 : BorelSpace Base := ⟨rfl⟩
theorem sphereChartPrincipalDensity_smooth (d : SphereEnergyData) (p : Base) (i j : Fin 4) :
    ContDiff ℝ ∞ (fun x ↦ sphereChartPrincipalDensity d p x i j) :=
  roundCoordDensity_smooth.mul (intrinsicRealPrincipal_smooth d.tensor d.smooth d.symm d.pos p i j)

theorem sphereChartResolventForcing_bound (d : SphereEnergyData) (p : Base)
    {K : Set Yau.Jets.Coord} (hK : IsCompact K) :
    ∃ C > 0, ∀ f : SphereWeightedL2 d,
      MemLp (sphereChartResolventForcing d p f) 2 (volume.restrict K) ∧
      (∫ x in K, (sphereChartResolventForcing d p f x)^2) ≤
        C*(‖f‖^2+‖sphereWeakSolution d f‖^2) := by
  let a := fun x ↦ roundCoordDensity x*d.density (sphereChartCoordMap p x)
  have ha : Continuous a := roundCoordDensity_smooth.continuous.mul
    (d.continuous.comp (sphereChartCoordMap_smooth p).continuous)
  obtain ⟨B,hB,hb⟩ := Yau.real_compact_multiplier_bound hK a ha
  obtain ⟨D,hD,hd⟩ := sphereWeightedL2_compact_chart_bound d p hK
  refine ⟨2*(B*D),by positivity,?_⟩
  intro f
  let g := f-sphereL2Resolvent d f
  obtain ⟨hg,hgb⟩ := hd g
  obtain ⟨hm,hmb⟩ := hb _ hg
  have he : (fun x ↦ a x*g (sphereChartCoordMap p x)) =ᵐ[volume.restrict K]
      sphereChartResolventForcing d p f := by
    have h := (sphereWeightedMeasure_ae_chart_iff d p (fun x ↦ g x=f x-(sphereL2Resolvent d f) x)).mp
      (Lp.coeFn_sub f (sphereL2Resolvent d f))
    filter_upwards [ae_restrict_of_ae h] with x hx
    simp only [sphereChartResolventForcing,← hx,a]
  refine ⟨hm.ae_eq he,?_⟩
  have hi : (∫ x in K, (sphereChartResolventForcing d p f x)^2) = ∫ x in K, (a x*g (sphereChartCoordMap p x))^2 :=
    integral_congr_ae (he.fun_comp (fun t : ℝ ↦ t^2)).symm
  rw [hi]
  have hn : ‖g‖ ≤ ‖f‖+‖sphereWeakSolution d f‖ :=
    (norm_sub_le f (sphereL2Resolvent d f)).trans (add_le_add_right
      (sphereEnergyL2Map_apply_norm_le d (sphereWeakSolution d f)) _)
  have hns : ‖g‖^2 ≤ 2*(‖f‖^2+‖sphereWeakSolution d f‖^2) := by
    nlinarith [norm_nonneg g,norm_nonneg f,norm_nonneg (sphereWeakSolution d f),
      sq_nonneg (‖f‖-‖sphereWeakSolution d f‖)]
  calc
    _ ≤ B*(D*‖g‖^2) := hmb.trans (mul_le_mul_of_nonneg_left hgb hB.le)
    _ ≤ B*(D*(2*(‖f‖^2+‖sphereWeakSolution d f‖^2))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hns hD.le) hB.le
    _ = _ := by ring

theorem sphere_resolvent_divergence_weak (d : SphereEnergyData) (f : SphereWeightedL2 d)
    (p : Base) (phi : Yau.Jets.Coord → ℝ) (hp : ContDiff ℝ ∞ phi)
    (hc : HasCompactSupport phi) (hs : tsupport phi ⊆ realFinCube 4) :
    IntegrableOn (fun x ↦ ∑ i, ∑ j, sphereChartPrincipalDensity d p x i j*
      (sphereChartDerivativeMap d p i (sphereWeakSolution d f)) x*Yau.coordPartial phi x j) (realFinCube 4) ∧
    IntegrableOn (fun x ↦ sphereChartResolventForcing d p f x*phi x) (realFinCube 4) ∧
    (∫ x in realFinCube 4, ∑ i, ∑ j, sphereChartPrincipalDensity d p x i j*
      (sphereChartDerivativeMap d p i (sphereWeakSolution d f)) x*Yau.coordPartial phi x j) =
      ∫ x in realFinCube 4, sphereChartResolventForcing d p f x*phi x := by
  obtain ⟨hF,hM,hR,he⟩ := sphere_resolvent_chart_variational d f p phi hp hc hs
  have heF : (fun x ↦ roundCoordDensity x*∑ i, (sphereChartDerivativeMap d p i (sphereWeakSolution d f)) x*
      (∑ j, intrinsicRealPrincipal d.tensor p x i j*Yau.coordPartial phi x j)) =
      fun x ↦ ∑ i, ∑ j, sphereChartPrincipalDensity d p x i j*
        (sphereChartDerivativeMap d p i (sphereWeakSolution d f)) x*Yau.coordPartial phi x j := by
    funext x
    simp only [sphereChartPrincipalDensity,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [heF] at hF he
  have heR : (fun x ↦ roundCoordDensity x*d.density (sphereChartCoordMap p x)*
      f (sphereChartCoordMap p x)*phi x - roundCoordDensity x*d.density (sphereChartCoordMap p x)*
      (sphereEnergyL2Map d (sphereWeakSolution d f)) (sphereChartCoordMap p x)*phi x) =
      fun x ↦ sphereChartResolventForcing d p f x*phi x := by
    funext x
    unfold sphereChartResolventForcing
    change _ = _*(_-(sphereEnergyL2Map d (sphereWeakSolution d f)) (sphereChartCoordMap p x))*phi x
    ring
  refine ⟨hF,by rw [← heR]; exact hR.sub hM,?_⟩
  rw [← heR,integral_sub hR hM]
  linarith only [he]

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Charts_SphereChartFluxL2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open MeasureTheory Yau.Geometry Set
open scoped ContDiff
noncomputable section

local instance sphereChartFluxL2Measurable_rccdb5c_1 : MeasurableSpace Base := borel Base
local instance sphereChartFluxL2Borel_rccdb5c_1 : BorelSpace Base := ⟨rfl⟩
theorem sphereChartCompletedFlux_memLp (d : SphereEnergyData) (p : Base)
    (z : SphereEnergyHilbert d) (j : Fin 4) :
    MemLp (sphereChartCompletedFlux d p z j) 2 (volume.restrict (realFinCube 4)) := by
  apply memLp_finsetSum
  intro i _
  obtain ⟨_,_,hb⟩ := Yau.real_compact_multiplier_bound (realFinCube_isCompact 4)
    (fun x ↦ sphereChartPrincipalDensity d p x i j) (sphereChartPrincipalDensity_smooth d p i j).continuous
  exact (hb _ (Lp.memLp (sphereChartDerivativeMap d p i z))).1

theorem sphereChartFluxZero_memLp (d : SphereEnergyData) (p : Base)
    (z : SphereEnergyHilbert d) (j : Fin 4) : MemLp (sphereChartFluxZero d p z j) 2 volume :=
  (memLp_indicator_iff_restrict (realFinCube_isCompact 4).measurableSet).mpr
    (sphereChartCompletedFlux_memLp d p z j)

theorem sphereChartForcingZero_memLp (d : SphereEnergyData) (p : Base)
    (f : SphereWeightedL2 d) : MemLp (sphereChartForcingZero d p f) 2 volume := by
  obtain ⟨_,_,hb⟩ := sphereChartResolventForcing_bound d p (realFinCube_isCompact 4)
  exact (memLp_indicator_iff_restrict (realFinCube_isCompact 4).measurableSet).mpr (hb f).1

theorem sphere_resolvent_zeroFlux_test (d : SphereEnergyData) (f : SphereWeightedL2 d)
    (p : Base) (phi : Yau.Jets.Coord → ℝ) (hp : ContDiff ℝ ∞ phi)
    (hc : HasCompactSupport phi) (hs : tsupport phi ⊆ realFinCube 4) :
    (∑ j, ∫ x, sphereChartFluxZero d p (sphereWeakSolution d f) j x*Yau.coordPartial phi x j) =
      ∫ x, sphereChartForcingZero d p f x*phi x := by
  have hi (j : Fin 4) : IntegrableOn (fun x ↦ sphereChartCompletedFlux d p (sphereWeakSolution d f) j x*
      Yau.coordPartial phi x j) (realFinCube 4) :=
    (sphereChartCompletedFlux_memLp d p (sphereWeakSolution d f) j).integrable_mul
      (Yau.real_continuous_memLp_compact (realFinCube_isCompact 4) _
        (Yau.real_coordPartial_smooth phi hp j).continuous)
  have h := (sphere_resolvent_divergence_weak d f p phi hp hc hs).2.2
  have hj (j : Fin 4) :
      (∫ x, sphereChartFluxZero d p (sphereWeakSolution d f) j x*Yau.coordPartial phi x j) =
      ∫ x in realFinCube 4, sphereChartCompletedFlux d p (sphereWeakSolution d f) j x*Yau.coordPartial phi x j := by
    rw [← integral_indicator (realFinCube_isCompact 4).measurableSet]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun x ↦ (Set.indicator_mul_left (realFinCube 4)
      (sphereChartCompletedFlux d p (sphereWeakSolution d f) j) (fun x ↦ Yau.coordPartial phi x j)).symm)
  simp only [hj,sphereChartForcingZero,← Set.indicator_mul_left,
    integral_indicator (realFinCube_isCompact 4).measurableSet]
  rw [← integral_finsetSum Finset.univ (fun j _ ↦ hi j)]
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun x ↦ by
    simp only [sphereChartCompletedFlux,Finset.sum_mul]
    exact Finset.sum_comm)

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_RealL2DifferenceLimit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau
open MeasureTheory Filter
open scoped Topology
noncomputable section

theorem realDifferenceQuotient_congr_ae {n : ℕ} (i : Fin n) (h : ℝ)
    {u v : (Fin n → ℝ) → ℝ} (huv : u =ᵐ[volume] v) :
    realDifferenceQuotient i h u =ᵐ[volume] realDifferenceQuotient i h v := by
  have hs := (measurePreserving_add_right (G := Fin n → ℝ) volume
    (Pi.single i h)).quasiMeasurePreserving.ae_eq_comp huv
  filter_upwards [huv,hs] with x hx ht
  exact congrArg₂ (fun a b : ℝ ↦ h⁻¹*(a-b)) ht hx

theorem realL2DifferenceMap_ae {n : ℕ} (i : Fin n) (h : ℝ) (u : RealEuclideanL2 n)
    (v : (Fin n → ℝ) → ℝ) (he : (u : (Fin n → ℝ) → ℝ) =ᵐ[volume] v) :
    (realL2DifferenceMap i h u : (Fin n → ℝ) → ℝ) =ᵐ[volume] realDifferenceQuotient i h v :=
  (realL2DifferenceQuotient_ae i h u).trans (realDifferenceQuotient_congr_ae i h he)

end
end Yau

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_RealGlobalL2Multiplier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau
open MeasureTheory Set
noncomputable section

theorem realL2RestrictMap_ae {n : ℕ} (K : Set (Fin n → ℝ)) (u : RealEuclideanL2 n) :
    (realL2RestrictMap K u : (Fin n → ℝ) → ℝ) =ᵐ[volume.restrict K] u :=
  ((Lp.memLp u).mono_measure Measure.restrict_le_self).coeFn_toLp

theorem realGlobalCompactMap_ae {n : ℕ} {K : Set (Fin n → ℝ)} (hK : IsCompact K)
    (eta : (Fin n → ℝ) → ℝ) (he : Continuous eta) (hs : tsupport eta ⊆ K)
    (u : RealEuclideanL2 n) (v : (Fin n → ℝ) → ℝ)
    (hv : (u : (Fin n → ℝ) → ℝ) =ᵐ[volume] v) :
    (realGlobalCompactMap hK eta he hs u : (Fin n → ℝ) → ℝ) =ᵐ[volume] (fun x ↦ eta x*v x) :=
  (realCompactL2Map_ae hK eta he hs _).trans
    (real_compact_mul_ae hK.measurableSet eta _ _ hs
      ((realL2RestrictMap_ae K u).trans (ae_restrict_of_ae hv)))

end
end Yau

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Charts_SphereDifferenceTestMaps
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open MeasureTheory Yau.Geometry Set
open scoped ContDiff
noncomputable section

local instance sphereDifferenceTestMeasurable_rccdb5c_1 : MeasurableSpace Base := borel Base
local instance sphereDifferenceTestBorel_rccdb5c_1 : BorelSpace Base := ⟨rfl⟩
theorem sphereDifferenceTestMap_ae (d : SphereEnergyData) (p : Base)
    (eta theta : Yau.Jets.Coord → ℝ) (he : ContDiff ℝ ∞ eta) (ht : ContDiff ℝ ∞ theta)
    (hes : tsupport eta ⊆ realFinCube 4) (hts : tsupport theta ⊆ realFinCube 4)
    (i : Fin 4) (h : ℝ) (z : SphereEnergyHilbert d) :
    (sphereDifferenceTestMap d p eta theta he ht hes hts i h z : Yau.Jets.Coord → ℝ)
      =ᵐ[volume] (fun x ↦ theta x*Yau.realDifferenceQuotient i h
        (fun y ↦ eta y*(sphereEnergyL2Map d z) (sphereChartCoordMap p y)) x) :=
  Yau.realGlobalCompactMap_ae (realFinCube_isCompact 4) theta ht.continuous hts _ _
    (Yau.realL2DifferenceMap_ae i h _ _ (sphereCutoffValueMap_ae d p eta he hes z))

theorem sphereDifferenceTestDerivativeMap_ae (d : SphereEnergyData) (p : Base)
    (eta theta : Yau.Jets.Coord → ℝ) (he : ContDiff ℝ ∞ eta) (ht : ContDiff ℝ ∞ theta)
    (hes : tsupport eta ⊆ realFinCube 4) (hts : tsupport theta ⊆ realFinCube 4)
    (i : Fin 4) (h : ℝ) (j : Fin 4) (z : SphereEnergyHilbert d) :
    (sphereDifferenceTestDerivativeMap d p eta theta he ht hes hts i h j z : Yau.Jets.Coord → ℝ)
      =ᵐ[volume] (fun x ↦ theta x*Yau.realDifferenceQuotient i h
        (fun y ↦ eta y*(sphereChartDerivativeMap d p j z) y+
          Yau.coordPartial eta y j*(sphereEnergyL2Map d z) (sphereChartCoordMap p y)) x +
        Yau.coordPartial theta x j*Yau.realDifferenceQuotient i h
          (fun y ↦ eta y*(sphereEnergyL2Map d z) (sphereChartCoordMap p y)) x) := by
  exact (Lp.coeFn_add _ _).trans
    ((Yau.realGlobalCompactMap_ae (realFinCube_isCompact 4) theta ht.continuous hts _ _
      (Yau.realL2DifferenceMap_ae i h _ _ (sphereCutoffDerivativeMap_ae d p eta he hes j z))).add
    (Yau.realGlobalCompactMap_ae (realFinCube_isCompact 4) _
      (Yau.real_coordPartial_smooth theta ht j).continuous
      ((tsupport_fderiv_apply_subset ℝ (Pi.single j 1)).trans hts) _ _
      (Yau.realL2DifferenceMap_ae i h _ _ (sphereCutoffValueMap_ae d p eta he hes z))))

theorem sphereDifferenceTestMap_smooth_ae (d : SphereEnergyData) (p : Base)
    (eta theta : Yau.Jets.Coord → ℝ) (he : ContDiff ℝ ∞ eta) (ht : ContDiff ℝ ∞ theta)
    (hes : tsupport eta ⊆ realFinCube 4) (hts : tsupport theta ⊆ realFinCube 4)
    (i : Fin 4) (h : ℝ) (u : SphereEnergySmooth d) :
    (sphereDifferenceTestMap d p eta theta he ht hes hts i h (sphereEnergyToCompletion d u) : Yau.Jets.Coord → ℝ)
      =ᵐ[volume] (fun x ↦ theta x*Yau.realDifferenceQuotient i h
        (fun y ↦ eta y*(SphereEnergySmooth.toSmooth d u : Base → ℝ) (sphereChartCoordMap p y)) x) :=
  Yau.realGlobalCompactMap_ae (realFinCube_isCompact 4) theta ht.continuous hts _ _
    (Yau.realL2DifferenceMap_ae i h _ _ (sphereCutoffValueMap_smooth_ae d p eta he hes u))

theorem sphereDifferenceTestDerivativeMap_smooth_ae (d : SphereEnergyData) (p : Base)
    (eta theta : Yau.Jets.Coord → ℝ) (he : ContDiff ℝ ∞ eta) (ht : ContDiff ℝ ∞ theta)
    (hes : tsupport eta ⊆ realFinCube 4) (hts : tsupport theta ⊆ realFinCube 4)
    (i : Fin 4) (h : ℝ) (j : Fin 4) (u : SphereEnergySmooth d) :
    (sphereDifferenceTestDerivativeMap d p eta theta he ht hes hts i h j (sphereEnergyToCompletion d u) : Yau.Jets.Coord → ℝ)
      =ᵐ[volume] (fun x ↦ Yau.coordPartial (fun y ↦ theta y*Yau.realDifferenceQuotient i h
        (fun a ↦ eta a*(SphereEnergySmooth.toSmooth d u : Base → ℝ) (sphereChartCoordMap p a)) y) x j) := by
  let v : Yau.Jets.Coord → ℝ := fun y ↦ eta y*(SphereEnergySmooth.toSmooth d u : Base → ℝ) (sphereChartCoordMap p y)
  have hv : ContDiff ℝ ∞ v := he.mul (spherePullback_smooth _ (SphereEnergySmooth.toSmooth d u).property p)
  have h1 := Yau.realGlobalCompactMap_ae (realFinCube_isCompact 4) theta ht.continuous hts _ _
    (Yau.realL2DifferenceMap_ae i h _ _ (sphereCutoffDerivativeMap_smooth_ae d p eta he hes j u))
  have h2 := Yau.realGlobalCompactMap_ae (realFinCube_isCompact 4) _
    (Yau.real_coordPartial_smooth theta ht j).continuous
    ((tsupport_fderiv_apply_subset ℝ (Pi.single j 1)).trans hts) _ _
    (Yau.realL2DifferenceMap_ae i h _ _ (sphereCutoffValueMap_smooth_ae d p eta he hes u))
  apply ((Lp.coeFn_add _ _).trans (h1.add h2)).trans
  apply Filter.Eventually.of_forall
  intro x
  change theta x*Yau.realDifferenceQuotient i h (fun a ↦ Yau.coordPartial v a j) x +
    Yau.coordPartial theta x j*Yau.realDifferenceQuotient i h v x =
    Yau.coordPartial (fun a ↦ theta a*Yau.realDifferenceQuotient i h v a) x j
  rw [Yau.real_coordPartial_mul theta _ ht (Yau.realDifferenceQuotient_smooth i h v hv),
    Yau.realDifferenceQuotient_partial i j h v hv]
  ring

end
end Yau.Target

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
-- module Solutions.OAIQ237_NY.NodalSets_Spectral_SphereResolventDifferenceEquation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open MeasureTheory Yau.Geometry Set
open scoped ContDiff
noncomputable section

local instance sphereResolventDifferenceEquationMeasurable_rccdb5c_1 : MeasurableSpace Base := borel Base
local instance sphereResolventDifferenceEquationBorel_rccdb5c_1 : BorelSpace Base := ⟨rfl⟩
theorem sphere_resolvent_difference_equation_radius (d : SphereEnergyData) (f : SphereWeightedL2 d)
    (p : Base) (i : Fin 4) (r : ℝ) (hr : r ≤ 1) (h : ℝ) (hh : |h| ≤ 1-r)
    (phi : Yau.Jets.Coord → ℝ) (hp : ContDiff ℝ ∞ phi) (hc : HasCompactSupport phi)
    (hs : tsupport phi ⊆ Yau.realCenteredCube 4 r) :
    (∀ j : Fin 4, Integrable (fun x ↦
      Yau.realDifferenceQuotient i h (sphereChartFluxZero d p (sphereWeakSolution d f) j) x*
        Yau.coordPartial phi x j)) ∧
    Integrable (fun x ↦ sphereChartForcingZero d p f x*Yau.realDifferenceQuotient i (-h) phi x) ∧
    (∑ j, ∫ x, Yau.realDifferenceQuotient i h (sphereChartFluxZero d p (sphereWeakSolution d f) j) x*
      Yau.coordPartial phi x j) =
      -(∫ x, sphereChartForcingZero d p f x*Yau.realDifferenceQuotient i (-h) phi x) := by
  have htest := sphere_resolvent_zeroFlux_test d f p (Yau.realDifferenceQuotient i (-h) phi)
    (Yau.realDifferenceQuotient_smooth i (-h) phi hp)
    (Yau.realDifferenceQuotient_compact i (-h) phi hc)
    (Yau.realDifferenceQuotient_tsupport i (-h) phi (realFinCube_isCompact 4).isClosed
      (hs.trans (Yau.realCenteredCube_mono hr))
      (fun x hx ↦ Yau.realCenteredCube_shift i (by simpa only [abs_neg] using hh) (hs hx)))
  have hd (j : Fin 4) := Yau.real_differenceQuotient_pairing i h
    (sphereChartFluxZero d p (sphereWeakSolution d f) j) (fun x ↦ Yau.coordPartial phi x j)
    (sphereChartFluxZero_memLp d p (sphereWeakSolution d f) j)
    (Yau.real_compact_continuous_memLp _ (Yau.real_coordPartial_smooth phi hp j).continuous
      (hc.fderiv_apply ℝ (Pi.single j 1)))
  have hi := (sphereChartForcingZero_memLp d p f).integrable_mul
    (Yau.realDifferenceQuotient_memLp i (-h) phi (Yau.real_compact_continuous_memLp phi hp.continuous hc))
  refine ⟨fun j ↦ (hd j).1,hi,?_⟩
  simp only [Yau.realDifferenceQuotient_partial i _ (-h) phi hp] at htest
  simp only [(hd _).2.2,Finset.sum_neg_distrib]
  exact congrArg Neg.neg htest

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Charts_SphereDifferenceTestEquation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open MeasureTheory Yau.Geometry Set
open scoped ContDiff
noncomputable section

local instance sphereDifferenceEquationMeasurable_rccdb5c_1 : MeasurableSpace Base := borel Base
local instance sphereDifferenceEquationBorel_rccdb5c_1 : BorelSpace Base := ⟨rfl⟩
theorem sphere_resolvent_H1_difference_test (d : SphereEnergyData) (f : SphereWeightedL2 d)
    (p : Base) (z : SphereEnergyHilbert d) (eta theta : Yau.Jets.Coord → ℝ)
    (he : ContDiff ℝ ∞ eta) (ht : ContDiff ℝ ∞ theta)
    (hes : tsupport eta ⊆ realFinCube 4) (r : ℝ) (hr : r ≤ 1)
    (hts : tsupport theta ⊆ Yau.realCenteredCube 4 r) (i : Fin 4) (h : ℝ) (hh : |h| ≤ 1-r) :
    let hts' : tsupport theta ⊆ realFinCube 4 := hts.trans (Yau.realCenteredCube_mono hr)
    let T := sphereDifferenceTestMap d p eta theta he ht hes hts' i h
    let D := sphereDifferenceTestDerivativeMap d p eta theta he ht hes hts' i h
    (∀ j : Fin 4, Integrable (fun x ↦
      Yau.realDifferenceQuotient i h (sphereChartFluxZero d p (sphereWeakSolution d f) j) x*(D j z) x)) ∧
    Integrable (fun x ↦ sphereChartForcingZero d p f x*Yau.realDifferenceQuotient i (-h) (T z) x) ∧
    (∑ j, ∫ x, Yau.realDifferenceQuotient i h (sphereChartFluxZero d p (sphereWeakSolution d f) j) x*(D j z) x) =
      -(∫ x, sphereChartForcingZero d p f x*Yau.realDifferenceQuotient i (-h) (T z) x) := by
  dsimp only
  let hts' : tsupport theta ⊆ realFinCube 4 := hts.trans (Yau.realCenteredCube_mono hr)
  let T := sphereDifferenceTestMap d p eta theta he ht hes hts' i h
  let D := sphereDifferenceTestDerivativeMap d p eta theta he ht hes hts' i h
  let A : Fin 4 → Yau.RealEuclideanL2 4 := fun j ↦
    (Yau.realDifferenceQuotient_memLp i h _ (sphereChartFluxZero_memLp d p (sphereWeakSolution d f) j)).toLp
      (Yau.realDifferenceQuotient i h (sphereChartFluxZero d p (sphereWeakSolution d f) j))
  let F : Yau.RealEuclideanL2 4 := (sphereChartForcingZero_memLp d p f).toLp (sphereChartForcingZero d p f)
  have ha (j : Fin 4) : (A j : Yau.Jets.Coord → ℝ) =ᵐ[volume]
      Yau.realDifferenceQuotient i h (sphereChartFluxZero d p (sphereWeakSolution d f) j) :=
    (Yau.realDifferenceQuotient_memLp i h _ (sphereChartFluxZero_memLp d p (sphereWeakSolution d f) j)).coeFn_toLp
  have hf : (F : Yau.Jets.Coord → ℝ) =ᵐ[volume] sphereChartForcingZero d p f :=
    (sphereChartForcingZero_memLp d p f).coeFn_toLp
  have hid (w : SphereEnergyHilbert d) : (∑ j, inner ℝ (A j) (D j w)) =
      -inner ℝ F (Yau.realL2DifferenceMap i (-h) (T w)) := by
    apply (sphereEnergyToCompletion_dense d).induction_on
      (p := fun w ↦ (∑ j, inner ℝ (A j) (D j w)) = -inner ℝ F (Yau.realL2DifferenceMap i (-h) (T w))) w
    · apply isClosed_eq
      · exact continuous_finsetSum _ (fun j _ ↦ continuous_const.inner (D j).continuous)
      · exact (continuous_const.inner ((Yau.realL2DifferenceMap i (-h)).continuous.comp T.continuous)).neg
    · intro u
      let v : Yau.Jets.Coord → ℝ := fun y ↦ eta y*(SphereEnergySmooth.toSmooth d u : Base → ℝ) (sphereChartCoordMap p y)
      let phi : Yau.Jets.Coord → ℝ := fun x ↦ theta x*Yau.realDifferenceQuotient i h v x
      have hv : ContDiff ℝ ∞ v := he.mul (spherePullback_smooth _ (SphereEnergySmooth.toSmooth d u).property p)
      have hp : ContDiff ℝ ∞ phi := ht.mul (Yau.realDifferenceQuotient_smooth i h v hv)
      have hct : HasCompactSupport theta :=
        (Yau.realCenteredCube_isCompact 4 r).of_isClosed_subset (isClosed_tsupport theta) hts
      have hc : HasCompactSupport phi := hct.mul_right
      have hs : tsupport phi ⊆ Yau.realCenteredCube 4 r := tsupport_mul_subset_left.trans hts
      have eq := (sphere_resolvent_difference_equation_radius d f p i r hr h hh phi hp hc hs).2.2
      have ht0 := sphereDifferenceTestMap_smooth_ae d p eta theta he ht hes hts' i h u
      have hd0 (j : Fin 4) := sphereDifferenceTestDerivativeMap_smooth_ae d p eta theta he ht hes hts' i h j u
      have hleft (j : Fin 4) : inner ℝ (A j) (D j (sphereEnergyToCompletion d u)) =
          ∫ x, Yau.realDifferenceQuotient i h (sphereChartFluxZero d p (sphereWeakSolution d f) j) x*
            Yau.coordPartial phi x j :=
        (Yau.real_L2_inner_reps _ _ _ _ (ha j) (hd0 j)).2
      have hright : inner ℝ F (Yau.realL2DifferenceMap i (-h) (T (sphereEnergyToCompletion d u))) =
          ∫ x, sphereChartForcingZero d p f x*Yau.realDifferenceQuotient i (-h) phi x :=
        (Yau.real_L2_inner_reps _ _ _ _ hf (Yau.realL2DifferenceMap_ae i (-h) _ _ ht0)).2
      simp only [hleft,hright]
      exact eq
  have hl (j : Fin 4) := Yau.real_L2_inner_reps (A j) (D j z) _ _ (ha j) Filter.EventuallyEq.rfl
  have hr' := Yau.real_L2_inner_reps F (Yau.realL2DifferenceMap i (-h) (T z)) _ _ hf
    (Yau.realL2DifferenceMap_ae i (-h) (T z) (T z) Filter.EventuallyEq.rfl)
  refine ⟨fun j ↦ (hl j).1,hr'.1,?_⟩
  have h0 := hid z
  simpa only [(hl _).2,hr'.2] using h0

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Charts_SphereDifferenceTestLiteral
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open MeasureTheory Yau.Geometry Set
open scoped ContDiff
noncomputable section

local instance sphereDifferenceLiteralMeasurable_rccdb5c_1 : MeasurableSpace Base := borel Base
local instance sphereDifferenceLiteralBorel_rccdb5c_1 : BorelSpace Base := ⟨rfl⟩
theorem sphere_resolvent_H1_difference_test_literal_oai (d : SphereEnergyData) (f : SphereWeightedL2 d)
    (p : Base) (z : SphereEnergyHilbert d) (eta theta : Yau.Jets.Coord → ℝ)
    (he : ContDiff ℝ ∞ eta) (ht : ContDiff ℝ ∞ theta)
    (hes : tsupport eta ⊆ realFinCube 4) (r : ℝ) (hr : r ≤ 1)
    (hts : tsupport theta ⊆ Yau.realCenteredCube 4 r) (i : Fin 4) (h : ℝ) (hh : |h| ≤ 1-r) :
    let v := fun x ↦ eta x*(sphereEnergyL2Map d z) (sphereChartCoordMap p x)
    let G := fun j x ↦ eta x*(sphereChartDerivativeMap d p j z) x+
      Yau.coordPartial eta x j*(sphereEnergyL2Map d z) (sphereChartCoordMap p x)
    let phi := fun x ↦ theta x*Yau.realDifferenceQuotient i h v x
    let Psi := fun j x ↦ theta x*Yau.realDifferenceQuotient i h (G j) x+
      Yau.coordPartial theta x j*Yau.realDifferenceQuotient i h v x
    MemLp phi 2 volume ∧ (∀ j : Fin 4, MemLp (Psi j) 2 volume) ∧
    (∀ j : Fin 4, Integrable (fun x ↦
      Yau.realDifferenceQuotient i h (sphereChartFluxZero d p (sphereWeakSolution d f) j) x*Psi j x)) ∧
    Integrable (fun x ↦ sphereChartForcingZero d p f x*Yau.realDifferenceQuotient i (-h) phi x) ∧
    (∑ j, ∫ x, Yau.realDifferenceQuotient i h (sphereChartFluxZero d p (sphereWeakSolution d f) j) x*Psi j x) =
      -(∫ x, sphereChartForcingZero d p f x*Yau.realDifferenceQuotient i (-h) phi x) := by
  dsimp only
  let hts' : tsupport theta ⊆ realFinCube 4 := hts.trans (Yau.realCenteredCube_mono hr)
  have hv := sphereDifferenceTestMap_ae d p eta theta he ht hes hts' i h z
  have hg (j : Fin 4) := sphereDifferenceTestDerivativeMap_ae d p eta theta he ht hes hts' i h j z
  have hb := sphere_resolvent_H1_difference_test d f p z eta theta he ht hes r hr hts i h hh
  dsimp only at hb
  have hd := Yau.realDifferenceQuotient_congr_ae i (-h) hv
  have hleft (j : Fin 4) :
      (fun x ↦ Yau.realDifferenceQuotient i h (sphereChartFluxZero d p (sphereWeakSolution d f) j) x*
        (sphereDifferenceTestDerivativeMap d p eta theta he ht hes hts' i h j z) x) =ᵐ[volume]
      (fun x ↦ Yau.realDifferenceQuotient i h (sphereChartFluxZero d p (sphereWeakSolution d f) j) x*
        (theta x*Yau.realDifferenceQuotient i h
          (fun y ↦ eta y*(sphereChartDerivativeMap d p j z) y+
            Yau.coordPartial eta y j*(sphereEnergyL2Map d z) (sphereChartCoordMap p y)) x+
          Yau.coordPartial theta x j*Yau.realDifferenceQuotient i h
            (fun y ↦ eta y*(sphereEnergyL2Map d z) (sphereChartCoordMap p y)) x)) :=
    Filter.EventuallyEq.rfl.mul (hg j)
  have hright := Filter.EventuallyEq.rfl.mul hd
    (f := sphereChartForcingZero d p f)
  refine ⟨(memLp_congr_ae hv).mp (Lp.memLp _),
    fun j ↦ (memLp_congr_ae (hg j)).mp (Lp.memLp _),
    fun j ↦ (hb.1 j).congr (hleft j),hb.2.1.congr hright,?_⟩
  have h0 := hb.2.2
  simp only [integral_congr_ae (hleft _)] at h0
  exact h0.trans (congrArg Neg.neg (integral_congr_ae hright))

end
end Yau.Target

end OAI
end

theorem solution : type_of% @OAI.Yau.Target.sphere_resolvent_H1_difference_test_literal_oai := @OAI.Yau.Target.sphere_resolvent_H1_difference_test_literal_oai
