-- Prove2me | solution 1 for OAI.Yau.Target.sphereL2Resolvent_compact
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T00:33:11.728776+00:00
-- url     : https://prove2.me/submissions/cecff4b6-feff-4cd4-963c-e99403e9e804

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

open MeasureTheory Set Function

lemma realFinCube_mass (n : ℕ) :
    (volume.restrict (realFinCube n)).real univ = (2:ℝ)^n := by
  rw [realFinCube_volume,Measure.real,Measure.pi_univ]
  norm_num

lemma real_interval_cube_integral_continuous (n : ℕ)
    (F : ℝ × (Fin n → ℝ) → ℝ) (hF : Continuous F) :
    Continuous (fun t ↦ ∫ z in realFinCube n, F (t,z)) := by
  apply continuous_parametric_integral_of_continuous _ (realFinCube_isCompact n)
  exact hF

lemma real_cube_interval_integral_continuous (n : ℕ)
    (F : ℝ × (Fin n → ℝ) → ℝ) (hF : Continuous F) :
    Continuous (fun z ↦ ∫ t in Icc (-1:ℝ) 1, F (t,z)) := by
  apply continuous_parametric_integral_of_continuous _ isCompact_Icc
  exact hF.comp continuous_swap

lemma real_interval_cube_integral_swap (n : ℕ)
    (F : ℝ × (Fin n → ℝ) → ℝ) (hF : Continuous F) :
    (∫ t in Icc (-1:ℝ) 1, ∫ z in realFinCube n, F (t,z)) =
      ∫ z in realFinCube n, ∫ t in Icc (-1:ℝ) 1, F (t,z) := by
  apply integral_integral_swap
  rw [Measure.prod_restrict]
  exact hF.continuousOn.integrableOn_compact (isCompact_Icc.prod (realFinCube_isCompact n))

end Yau.Geometry

end

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
-- module Solutions.OAIQ237_NY.NodalSets_Charts_SphereFiniteChartL2Comparison
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Manifold Yau.Geometry MeasureTheory Set
open scoped ContDiff
noncomputable section

theorem sphere_finite_chart_l2_comparison (rho : Base → ℝ)
    (hr : Continuous rho) (hrp : ∀ x, 0 < rho x) :
    ∃ (P : Finset Base) (R : ℝ), 0 < R ∧ ∀ u : Base → ℝ, Continuous u →
      sphereWeightedPairing rho u u ≤
        R*∑ p : {p // p ∈ P}, ∫ x in realFinCube 4, (u (sphereChartCoordMap p.val x))^2 := by
  classical
  obtain ⟨P,theta,htheta,htn,htsum,_,htsupport,_⟩ := sphere_finite_smooth_partition
  obtain ⟨R,hR,hRb⟩ := (isCompact_univ.image hr).isBounded.exists_pos_norm_le
  have hrle (x : Base) : rho x ≤ R := (le_abs_self _).trans (hRb _ ⟨x,mem_univ x,rfl⟩)
  have htle (p : {p // p ∈ P}) (x : Base) : theta p x ≤ 1 := by
    rw [← htsum x]
    exact Finset.single_le_sum (fun q _ ↦ htn q x) (Finset.mem_univ p)
  refine ⟨P,R,hR,?_⟩
  intro u hu
  let f : {p // p ∈ P} → Base → ℝ := fun p x ↦ rho x*theta p x*u x^2
  have hf (p : {p // p ∈ P}) : Continuous (f p) := (hr.mul (htheta p).continuous).mul (hu.pow 2)
  have hsum (x : Base) : (∑ p, f p x)=rho x*u x*u x := by
    simp only [f,← Finset.sum_mul,← Finset.mul_sum,htsum,one_mul,pow_two,mul_assoc]
  have hlocal (p : {p // p ∈ P}) : (∫ x, f p x ∂sphereReferenceMeasure) ≤
      R*(∫ x in realFinCube 4, (u (sphereChartCoordMap p.val x))^2) := by
    let F : Yau.Jets.Coord → ℝ := fun x ↦ roundCoordDensity x*f p (sphereChartCoordMap p.val x)
    have hF : Continuous F := roundCoordDensity_smooth.continuous.mul
      ((hf p).comp (sphereChartCoordMap_smooth p.val).continuous)
    have hz (x : Yau.Jets.Coord) (hx : x ∉ realFinCube 4) : F x=0 := by
      have ht : theta p (sphereChartCoordMap p.val x)=0 := by
        apply Function.notMem_support.mp
        intro hs
        have hb := htsupport p (subset_closure hs)
        exact hx (by rwa [realFinCube_four_eq_closedBall])
      simp [F,f,ht]
    rw [sphereReferenceMeasure_integral_chart p.val]
    simp only [roundChartDensity_coord_eq]
    change (∫ x, F x) ≤ _
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hz]
    have hpt (x : Yau.Jets.Coord) : F x ≤ R*(u (sphereChartCoordMap p.val x))^2 := by
      have h1 := mul_le_mul_of_nonneg_right (roundCoordDensity_le_one x) (hrp (sphereChartCoordMap p.val x)).le
      have h2 := mul_le_mul_of_nonneg_left (htle p (sphereChartCoordMap p.val x))
        (mul_nonneg (roundCoordDensity_pos x).le (hrp (sphereChartCoordMap p.val x)).le)
      have hb : roundCoordDensity x*rho (sphereChartCoordMap p.val x)*theta p (sphereChartCoordMap p.val x) ≤ R := by
        nlinarith only [h1,h2,hrle (sphereChartCoordMap p.val x)]
      have h := mul_le_mul_of_nonneg_right hb (sq_nonneg (u (sphereChartCoordMap p.val x)))
      dsimp [F,f]
      nlinarith only [h]
    have hiR : IntegrableOn (fun x ↦ R*(u (sphereChartCoordMap p.val x))^2) (realFinCube 4) :=
      realFinCube_integrable 4 _ (((hu.comp (sphereChartCoordMap_smooth p.val).continuous).pow 2).const_mul R)
    have hm := setIntegral_mono_on (μ := volume) (s := realFinCube 4)
      (realFinCube_integrable 4 F hF) hiR
      (realFinCube_isCompact 4).measurableSet (fun x _ ↦ hpt x)
    rw [integral_const_mul] at hm
    exact hm

  calc
    sphereWeightedPairing rho u u = ∫ x, ∑ p, f p x ∂sphereReferenceMeasure := by
      unfold sphereWeightedPairing
      exact integral_congr_ae (Filter.Eventually.of_forall (fun x ↦ (hsum x).symm))
    _ = ∑ p, ∫ x, f p x ∂sphereReferenceMeasure := by
      exact integral_finsetSum (Finset.univ : Finset {p // p ∈ P})
        (fun p _ ↦ sphereReferenceMeasure_integrable_continuous _ (hf p))
    _ ≤ ∑ p : {p // p ∈ P}, R*(∫ x in realFinCube 4, (u (sphereChartCoordMap p.val x))^2) :=
      by
        exact Finset.sum_le_sum (fun p _ ↦ hlocal p)
    _ = _ := by
      rw [Finset.mul_sum]

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_RealCountableScalarCompactness
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Set Filter
open scoped Topology
noncomputable section

theorem real_countable_bounded_subsequence {I : Type*} [Countable I]
    (a : ℕ → I → ℝ) (B : I → ℝ) (hb : ∀ j i, |a j i| ≤ B i) :
    ∃ f : I → ℝ, ∃ nu : ℕ → ℕ, StrictMono nu ∧
      ∀ i, Tendsto (fun j ↦ a (nu j) i) atTop (𝓝 (f i)) := by
  have hc : IsCompact (univ.pi (fun i ↦ Icc (-B i) (B i))) :=
    isCompact_univ_pi (fun _ ↦ isCompact_Icc)
  have hmem (j : ℕ) : a j ∈ univ.pi (fun i ↦ Icc (-B i) (B i)) := by
    intro i _
    exact abs_le.mp (hb j i)
  obtain ⟨f,_,nu,hnu,ht⟩ := hc.tendsto_subseq hmem
  exact ⟨f,nu,hnu,fun i ↦ ((continuous_apply i).tendsto f).comp ht⟩

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

lemma corrugationCube_ball_inside (o : _root_.OAI.Yau.Jets.Coord) {L : ℝ} (hL : 0 < L)
    {n : ℕ} (hn : 0 < n) (k : Fin 4 → Fin n) :
    ball (corrugationCubeCenter o L n k) ((L/(n:ℝ))/2) ⊆
      interior (Set.Icc o (fun i ↦ o i+L)) := by
  have hnR : (0:ℝ) < n := by exact_mod_cast hn
  have hR : 0 < L/(n:ℝ) := div_pos hL hnR
  have hRn : (L/(n:ℝ))*(n:ℝ) = L := div_mul_cancel₀ L hnR.ne'
  intro x hx
  rw [← pi_univ_Icc,interior_pi_set Set.finite_univ]
  intro i _
  change x i ∈ interior (Icc (o i) (o i+L))
  rw [interior_Icc]
  constructor
  all_goals
    have hxi : |x i-corrugationCubeCenter o L n k i| < (L/(n:ℝ))/2 := by
      have hnorm := norm_le_pi_norm (x-corrugationCubeCenter o L n k) i
      exact lt_of_le_of_lt hnorm (by simpa [dist_eq_norm] using hx)
    have ha := abs_lt.mp hxi
    dsimp [corrugationCubeCenter] at ha
    have hk0 : (0:ℝ) ≤ (k i:ℝ) := by positivity
    have hk1 : (k i:ℝ)+1 ≤ n := by exact_mod_cast (k i).isLt
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
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_RealScaledCubeIntegration
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open MeasureTheory Set Function Metric
noncomputable section

lemma realScaledCube_isCompact (n : ℕ) (c : Fin n → ℝ) (r : ℝ) :
    IsCompact (realScaledCube n c r) :=
  (realFinCube_isCompact n).image (continuous_const.add (continuous_id.const_smul r))

lemma realScaledCube_integral (n : ℕ) (c : Fin n → ℝ) {r : ℝ} (hr : 0 < r)
    (F : (Fin n → ℝ) → ℝ) :
    (∫ y in realScaledCube n c r, F y) = r^n*(∫ x in realFinCube n, F (c+r • x)) := by
  let L : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) := r • ContinuousLinearMap.id ℝ (Fin n → ℝ)
  have hd (x : Fin n → ℝ) : HasFDerivAt (fun y ↦ c+r • y) L x :=
    L.hasFDerivAt.const_add c
  have hi : Injective (fun x : Fin n → ℝ ↦ c+r • x) := by
    intro x y h
    exact (smul_right_injective (Fin n → ℝ) hr.ne') (add_left_cancel h)
  have h := integral_image_eq_integral_abs_det_fderiv_smul volume
    (realFinCube_isCompact n).measurableSet (fun x _ ↦ (hd x).hasFDerivWithinAt) hi.injOn F
  have hdet : |L.det|=r^n := by
    simp [L,ContinuousLinearMap.det,LinearMap.det_smul,abs_of_pos hr]
  simpa only [realScaledCube,hdet,smul_eq_mul,integral_const_mul] using h

lemma realScaledCube_eq_closedBall (n : ℕ) (c : Fin n → ℝ) {r : ℝ} (hr : 0 < r) :
    realScaledCube n c r = closedBall c r := by
  have hunit : realFinCube n = closedBall (0 : Fin n → ℝ) 1 := by
    rw [closedBall_pi _ (by norm_num : (0:ℝ) ≤ 1)]
    simp [realFinCube,Real.closedBall_eq_Icc]
  ext y
  constructor
  · rintro ⟨x,hx,rfl⟩
    rw [hunit,mem_closedBall,dist_zero_right] at hx
    rw [mem_closedBall,dist_eq_norm,add_sub_cancel_left,norm_smul,
      Real.norm_eq_abs,abs_of_pos hr]
    nlinarith
  · intro hy
    refine ⟨r⁻¹ • (y-c),?_,?_⟩
    · rw [hunit,mem_closedBall,dist_zero_right,norm_smul,Real.norm_eq_abs,
        abs_of_pos (inv_pos.mpr hr)]
      have h : ‖y-c‖ ≤ r := by simpa only [mem_closedBall,dist_eq_norm] using hy
      exact (mul_le_mul_of_nonneg_left h (inv_nonneg.mpr hr.le)).trans_eq
        (inv_mul_cancel₀ hr.ne')
    · dsimp
      rw [smul_smul,mul_inv_cancel₀ hr.ne',one_smul,add_sub_cancel]

lemma realScaledCube_mass (n : ℕ) (c : Fin n → ℝ) {r : ℝ} (hr : 0 < r) :
    (volume.restrict (realScaledCube n c r)).real univ = (2*r)^n := by
  have h := realScaledCube_integral n c hr (fun _ ↦ (1:ℝ))
  simpa only [integral_const,smul_eq_mul,mul_one,one_mul,realFinCube_mass,mul_pow,mul_comm] using h

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_RealCubeCellPartition
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Yau.Jets MeasureTheory Set Function Metric
noncomputable section

lemma realCubeCell_closedBall {n : ℕ} (hn : 0 < n) (k : Fin 4 → Fin n) :
    realCubeCell n k = closedBall (corrugationCubeCenter (fun _ ↦ -1) 2 n k) ((2/(n:ℝ))/2) := by
  have hnR : (0:ℝ)<n := by exact_mod_cast hn
  rw [realCubeCell,realScaledCube_eq_closedBall 4 _ (div_pos zero_lt_one hnR)]
  congr 1
  ring

lemma realCubeCell_isCompact (n : ℕ) (k : Fin 4 → Fin n) : IsCompact (realCubeCell n k) :=
  realScaledCube_isCompact 4 _ _

lemma realCubeCell_subset {n : ℕ} (hn : 0 < n) (k : Fin 4 → Fin n) :
    realCubeCell n k ⊆ realFinCube 4 := by
  have hnR : (0:ℝ)<n := by exact_mod_cast hn
  rw [realCubeCell_closedBall hn k,← closure_ball _ (by positivity : (2/(n:ℝ))/2 ≠ 0)]
  have hb := (corrugationCube_ball_inside (fun _ ↦ -1) (by norm_num : (0:ℝ)<2) hn k).trans
    interior_subset
  have he : Icc (fun _ : Fin 4 ↦ (-1:ℝ)) (fun i ↦ (-1:ℝ)+2) = realFinCube 4 := by
    norm_num [realFinCube]
  rw [he] at hb
  exact closure_minimal hb (realFinCube_isCompact 4).isClosed

theorem realCubeCell_cover {n : ℕ} (hn : 0 < n) :
    (⋃ k : Fin 4 → Fin n, realCubeCell n k) = realFinCube 4 := by
  apply Subset.antisymm
  · exact iUnion_subset (realCubeCell_subset hn)
  · intro x hx
    have hx' : x ∈ Icc (fun _ : Fin 4 ↦ (-1:ℝ)) (fun i ↦ (-1:ℝ)+2) := by
      simpa [realFinCube,show (-1:ℝ)+2=1 by norm_num] using hx
    obtain ⟨k,hk⟩ := corrugationCube_closed_cover (fun _ ↦ -1) (by norm_num : (0:ℝ)<2) hn x hx'
    exact mem_iUnion.mpr ⟨k,by rwa [realCubeCell_closedBall hn k]⟩

lemma real_closedBall_ae_ball (c : Yau.Jets.Coord) (r : ℝ) :
    closedBall c r =ᵐ[volume] ball c r := by
  rw [ae_eq_set,closedBall_sdiff_ball,sdiff_eq_empty.mpr ball_subset_closedBall,measure_empty]
  exact ⟨Measure.addHaar_sphere volume c r,rfl⟩

lemma realCubeCell_pairwise_aedisjoint {n : ℕ} (hn : 0 < n) :
    Pairwise (AEDisjoint volume on (realCubeCell n)) := by
  intro k j hkj
  change AEDisjoint volume (realCubeCell n k) (realCubeCell n j)
  rw [realCubeCell_closedBall hn k,realCubeCell_closedBall hn j]
  exact (corrugationCube_balls_disjoint (fun _ ↦ -1) (by norm_num : (0:ℝ)<2) hn k j hkj).aedisjoint.congr
    (real_closedBall_ae_ball _ _) (real_closedBall_ae_ball _ _)

theorem realCubeCell_integral_sum {n : ℕ} (hn : 0 < n)
    (F : Yau.Jets.Coord → ℝ) (hF : IntegrableOn F (realFinCube 4)) :
    (∫ x in realFinCube 4, F x) = ∑ k : Fin 4 → Fin n, ∫ x in realCubeCell n k, F x := by
  have hi : IntegrableOn F (⋃ k : Fin 4 → Fin n, realCubeCell n k) := by
    rwa [realCubeCell_cover hn]
  have h := integral_iUnion_ae (fun k ↦ (realCubeCell_isCompact n k).measurableSet.nullMeasurableSet)
    (realCubeCell_pairwise_aedisjoint hn) hi
  simpa only [realCubeCell_cover hn,tsum_fintype] using h

lemma realCubeCell_mass {n : ℕ} (hn : 0 < n) (k : Fin 4 → Fin n) :
    (volume.restrict (realCubeCell n k)).real univ = (2/(n:ℝ))^4 := by
  have hnR : (0:ℝ)<n := by exact_mod_cast hn
  simpa only [realCubeCell,mul_one_div] using
    realScaledCube_mass 4 (corrugationCubeCenter (fun _ ↦ -1) 2 n k) (div_pos zero_lt_one hnR)

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_RealIntegralSquare
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open MeasureTheory Set
noncomputable section

lemma real_integral_square_le {X : Type*} [MeasurableSpace X] (mu : Measure X) [IsFiniteMeasure mu]
    (hm : 0 < mu.real univ) (f : X → ℝ) (hf : Integrable f mu)
    (hf2 : Integrable (fun x ↦ f x^2) mu) :
    (∫ x, f x ∂mu)^2 ≤ mu.real univ*(∫ x, f x^2 ∂mu) := by
  let m := mu.real univ
  let I := ∫ x, f x ∂mu
  let q := I/m
  have hq : m*q=I := mul_div_cancel₀ I hm.ne'
  have he : (fun x ↦ (f x-q)^2) = fun x ↦ (f x^2-(2*q)*f x)+q^2 := by
    funext x
    ring
  have hnonneg : 0 ≤ ∫ x, (f x-q)^2 ∂mu := integral_nonneg (fun x ↦ sq_nonneg (f x-q))
  have hsub : Integrable (fun x ↦ f x^2-(2*q)*f x) mu := hf2.sub (hf.const_mul _)
  rw [he,integral_add hsub (integrable_const _),
    integral_sub hf2 (hf.const_mul _),integral_const_mul,integral_const] at hnonneg
  change 0 ≤ (∫ x, f x^2 ∂mu)-(2*q)*I+m*q^2 at hnonneg
  have hmul := mul_nonneg hm.le hnonneg
  have hpoly : m*((∫ x, f x^2 ∂mu)-(2*q)*I+m*q^2) =
      m*(∫ x, f x^2 ∂mu)-I^2 := by
    calc
      _ = m*(∫ x, f x^2 ∂mu)-2*(m*q)*I+(m*q)^2 := by ring
      _ = _ := by rw [hq]; ring
  rw [hpoly] at hmul
  exact sub_nonneg.mp hmul

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_RealMeanSquareDecomposition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open MeasureTheory Set
noncomputable section

theorem real_mean_square_decomposition {X : Type*} [MeasurableSpace X]
    (mu : Measure X) [IsFiniteMeasure mu] (hm : 0 < mu.real univ)
    (f : X → ℝ) (hf : Integrable f mu) (hf2 : Integrable (fun x ↦ f x^2) mu)
    (c : ℝ) :
    (∫ x, (f x-c)^2 ∂mu) =
      (∫ x, (f x-(∫ y, f y ∂mu)/mu.real univ)^2 ∂mu) +
        mu.real univ*((∫ y, f y ∂mu)/mu.real univ-c)^2 := by
  have hexpand (d : ℝ) : (∫ x, (f x-d)^2 ∂mu) =
      (∫ x, f x^2 ∂mu)-2*d*(∫ x, f x ∂mu)+mu.real univ*d^2 := by
    have he : (fun x ↦ (f x-d)^2) = fun x ↦ (f x^2-(2*d)*f x)+d^2 := by
      funext x; ring
    have hs : Integrable (fun x ↦ f x^2-(2*d)*f x) mu := hf2.sub (hf.const_mul _)
    rw [he,integral_add hs (integrable_const _),
      integral_sub hf2 (hf.const_mul (2*d)),integral_const_mul,integral_const]
    rfl
  rw [hexpand,hexpand]
  field_simp
  ring

theorem real_mean_square_contraction {X : Type*} [MeasurableSpace X]
    (mu : Measure X) [IsFiniteMeasure mu] (hm : 0 < mu.real univ)
    (f : X → ℝ) (hf : Integrable f mu) (hf2 : Integrable (fun x ↦ f x^2) mu) :
    mu.real univ*((∫ x, f x ∂mu)/mu.real univ)^2 ≤ ∫ x, f x^2 ∂mu := by
  have h := real_integral_square_le mu hm f hf hf2
  apply (mul_le_mul_iff_right₀ hm).mp
  calc
    _ = (∫ x, f x ∂mu)^2 := by field_simp
    _ ≤ _ := by simpa [mul_comm] using h

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_RealCubeVarianceTensorization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open MeasureTheory Set Function
noncomputable section

theorem real_interval_cube_variance_le (n : ℕ)
    (F : ℝ × (Fin n → ℝ) → ℝ) (hF : Continuous F) :
    (∫ t in Icc (-1:ℝ) 1, ∫ z in realFinCube n,
      (F (t,z)-(∫ s in Icc (-1:ℝ) 1, ∫ y in realFinCube n, F (s,y))/(2*2^n))^2) ≤
    (∫ t in Icc (-1:ℝ) 1, ∫ z in realFinCube n,
      (F (t,z)-(∫ y in realFinCube n, F (t,y))/2^n)^2) +
    (∫ z in realFinCube n, ∫ t in Icc (-1:ℝ) 1,
      (F (t,z)-(∫ s in Icc (-1:ℝ) 1, F (s,z))/2)^2) := by
  let m : ℝ := 2^n
  have hm : 0 < m := pow_pos (by norm_num) n
  let : IsFiniteMeasure (volume.restrict (realFinCube n)) :=
    isFiniteMeasure_restrict.mpr (realFinCube_isCompact n).measure_ne_top
  let R : ℝ → ℝ := fun t ↦ (∫ z in realFinCube n, F (t,z))/m
  let C : (Fin n → ℝ) → ℝ := fun z ↦ (∫ t in Icc (-1:ℝ) 1, F (t,z))/2
  let M : ℝ := (∫ t in Icc (-1:ℝ) 1, ∫ z in realFinCube n, F (t,z))/(2*m)
  have hR : Continuous R := (real_interval_cube_integral_continuous n F hF).div_const m
  have hC : Continuous C := (real_cube_interval_integral_continuous n F hF).div_const 2
  have hmean : (∫ z in realFinCube n, C z)/m = M := by
    dsimp [C,M]
    rw [integral_div,← real_interval_cube_integral_swap n F hF]
    ring
  have hFC : Continuous (fun p : ℝ × (Fin n → ℝ) ↦ (F p-C p.2)^2) :=
    (hF.sub (hC.comp continuous_snd)).pow 2
  have hFR : Continuous (fun p : ℝ × (Fin n → ℝ) ↦ (F p-R p.1)^2) :=
    (hF.sub (hR.comp continuous_fst)).pow 2
  have hFM : Continuous (fun p : ℝ × (Fin n → ℝ) ↦ (F p-M)^2) :=
    (hF.sub continuous_const).pow 2
  have hpt (t : ℝ) : m*(R t-M)^2 ≤ ∫ z in realFinCube n, (F (t,z)-C z)^2 := by
    have hc : Continuous (fun z ↦ F (t,z)-C z) :=
      (hF.comp (continuous_const.prodMk continuous_id)).sub hC
    have h := real_mean_square_contraction (volume.restrict (realFinCube n))
      (by rw [realFinCube_mass]; exact hm) _
      (realFinCube_integrable n _ hc) (realFinCube_integrable n _ (hc.pow 2))
    have hi : IntegrableOn (fun z ↦ F (t,z)) (realFinCube n) :=
      realFinCube_integrable n _ (hF.comp (continuous_const.prodMk continuous_id))
    rw [realFinCube_mass,integral_sub hi
      (realFinCube_integrable n _ hC),sub_div,hmean] at h
    exact h
  have hbound := setIntegral_mono_on (μ := volume) (s := Icc (-1:ℝ) 1)
    (((continuous_const : Continuous (fun _ : ℝ ↦ m)).mul
      ((hR.sub (continuous_const : Continuous (fun _ : ℝ ↦ M))).pow 2)).continuousOn.integrableOn_Icc)
    ((real_interval_cube_integral_continuous n _ hFC).continuousOn.integrableOn_Icc)
    measurableSet_Icc (fun t _ ↦ hpt t)
  have hdecomp (t : ℝ) : (∫ z in realFinCube n, (F (t,z)-M)^2) =
      (∫ z in realFinCube n, (F (t,z)-R t)^2)+m*(R t-M)^2 := by
    have hc : Continuous (fun z : Fin n → ℝ ↦ F (t,z)) :=
      hF.comp (continuous_const.prodMk continuous_id)
    have h := real_mean_square_decomposition (volume.restrict (realFinCube n))
      (by rw [realFinCube_mass]; exact hm) _
      (realFinCube_integrable n _ hc) (realFinCube_integrable n _ (hc.pow 2)) M
    simpa only [realFinCube_mass] using h
  change (∫ t in Icc (-1:ℝ) 1, ∫ z in realFinCube n, (F (t,z)-M)^2) ≤
    (∫ t in Icc (-1:ℝ) 1, ∫ z in realFinCube n, (F (t,z)-R t)^2)+
      (∫ z in realFinCube n, ∫ t in Icc (-1:ℝ) 1, (F (t,z)-C z)^2)
  simp_rw [hdecomp]
  have hiR : IntegrableOn (fun t ↦ ∫ z in realFinCube n, (F (t,z)-R t)^2)
      (Icc (-1:ℝ) 1) :=
    (real_interval_cube_integral_continuous n _ hFR).continuousOn.integrableOn_Icc
  have hiM : IntegrableOn (fun t ↦ m*(R t-M)^2) (Icc (-1:ℝ) 1) :=
    (continuous_const.mul ((hR.sub continuous_const).pow 2)).continuousOn.integrableOn_Icc
  rw [integral_add hiR hiM]
  exact add_le_add le_rfl (hbound.trans_eq (real_interval_cube_integral_swap n _ hFC))

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_RealFinCubeSlices
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Function
open scoped ContDiff
noncomputable section

lemma real_finCons_smooth (n : ℕ) :
    ContDiff ℝ ∞ (fun p : ℝ × (Fin n → ℝ) ↦ (Fin.cons p.1 p.2 : Fin (n+1) → ℝ)) := by
  apply contDiff_pi.mpr
  intro i
  refine Fin.cases ?_ (fun j ↦ ?_) i
  · simpa using (contDiff_fst : ContDiff ℝ ∞ (fun p : ℝ × (Fin n → ℝ) ↦ p.1))
  · simpa [Function.comp_def] using (contDiff_apply ℝ ℝ j).comp
      (contDiff_snd : ContDiff ℝ ∞ (fun p : ℝ × (Fin n → ℝ) ↦ p.2))

lemma real_finCube_slice_smooth (n : ℕ) (W : (Fin (n+1) → ℝ) → ℝ)
    (hW : ContDiff ℝ ∞ W) (t : ℝ) :
    ContDiff ℝ ∞ (fun z ↦ W (Fin.cons t z)) :=
  hW.comp ((real_finCons_smooth n).comp (contDiff_const.prodMk contDiff_id))

lemma real_finCube_line_smooth (n : ℕ) (W : (Fin (n+1) → ℝ) → ℝ)
    (hW : ContDiff ℝ ∞ W) (z : Fin n → ℝ) :
    ContDiff ℝ ∞ (fun t ↦ W (Fin.cons t z)) :=
  hW.comp ((real_finCons_smooth n).comp (contDiff_id.prodMk contDiff_const))

lemma real_coordPartial_eq_deriv_update (n : ℕ) (W : (Fin n → ℝ) → ℝ)
    (hW : ContDiff ℝ ∞ W) (z : Fin n → ℝ) (i : Fin n) :
    Yau.coordPartial W z i = deriv (fun t ↦ W (update z i t)) (z i) := by
  have hd := (hW.differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) (update z i (z i))).hasFDerivAt.comp_hasDerivAt
    (z i) (hasDerivAt_update z i (z i))
  simpa [Yau.coordPartial,Function.comp_def] using hd.deriv.symm

lemma real_finCube_slice_partial (n : ℕ) (W : (Fin (n+1) → ℝ) → ℝ)
    (hW : ContDiff ℝ ∞ W) (t : ℝ) (z : Fin n → ℝ) (i : Fin n) :
    Yau.coordPartial (fun y ↦ W (Fin.cons t y)) z i =
      Yau.coordPartial W (Fin.cons t z) i.succ := by
  rw [real_coordPartial_eq_deriv_update n _ (real_finCube_slice_smooth n W hW t),
    real_coordPartial_eq_deriv_update (n+1) W hW]
  have he (s : ℝ) : (Fin.cons t (update z i s) : Fin (n+1) → ℝ) =
      update (Fin.cons t z : Fin (n+1) → ℝ) i.succ s := by
    ext j
    refine Fin.cases ?_ (fun k ↦ ?_) j
    · simp [Ne.symm (Fin.succ_ne_zero i)]
    · by_cases h : k=i
      · subst k; simp
      · simp [h]
  simp only [he,Fin.cons_succ]

lemma real_finCube_line_deriv (n : ℕ) (W : (Fin (n+1) → ℝ) → ℝ)
    (hW : ContDiff ℝ ∞ W) (t : ℝ) (z : Fin n → ℝ) :
    deriv (fun s ↦ W (Fin.cons s z)) t = Yau.coordPartial W (Fin.cons t z) 0 := by
  rw [real_coordPartial_eq_deriv_update (n+1) W hW]
  have he (s : ℝ) : update (Fin.cons t z : Fin (n+1) → ℝ) 0 s = Fin.cons s z := by
    ext j
    refine Fin.cases ?_ (fun k ↦ ?_) j <;> simp
  simp only [he,Fin.cons_zero]

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_RealIntervalDerivativeControl
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open MeasureTheory Set
open scoped ContDiff
noncomputable section

lemma real_interval_integral_square_le (f : ℝ → ℝ) (hf : Continuous f)
    {a b : ℝ} (hab : a < b) :
    (∫ x in Icc a b, f x)^2 ≤ (b-a)*(∫ x in Icc a b, f x^2) := by
  have hm : (volume.restrict (Icc a b)).real univ=b-a := by simp [hab.le]
  have hpos : 0 < (volume.restrict (Icc a b)).real univ := by rw [hm]; linarith
  have h := real_integral_square_le (volume.restrict (Icc a b)) hpos f
    hf.continuousOn.integrableOn_Icc (hf.pow 2).continuousOn.integrableOn_Icc
  rwa [hm] at h

lemma real_interval_derivative_control (f : ℝ → ℝ) (hf : ContDiff ℝ ∞ f)
    {a b : ℝ} (hab : a < b) (x y : ℝ) (hx : x ∈ Icc a b) (hy : y ∈ Icc a b) :
    (f x-f y)^2 ≤ (b-a)*(∫ t in Icc a b, (deriv f t)^2) := by
  have hd : Continuous (fun t ↦ |deriv f t|) := (hf.continuous_deriv (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).abs
  have hordered (c d : ℝ) (hc : c ∈ Icc a b) (hd' : d ∈ Icc a b) (hcd : c ≤ d) :
      |f d-f c| ≤ ∫ t in Icc a b, |deriv f t| := by
    have hh := norm_sub_le_integral_of_norm_deriv_le_of_le hcd hf.continuous.continuousOn
      (hf.differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).differentiableOn
      (Filter.Eventually.of_forall (fun t _ ↦ by rw [Real.norm_eq_abs])) (hd.intervalIntegrable c d)
    rw [intervalIntegral.integral_of_le hcd] at hh
    have hmono : (∫ t in Ioc c d, |deriv f t|) ≤ ∫ t in Icc a b, |deriv f t| := by
      apply setIntegral_mono_set hd.continuousOn.integrableOn_Icc
        (Filter.Eventually.of_forall (fun t ↦ abs_nonneg (deriv f t)))
      exact Filter.Eventually.of_forall (fun t ht ↦ ⟨hc.1.trans ht.1.le,ht.2.trans hd'.2⟩)
    exact (show |f d-f c| ≤ ∫ t in Ioc c d, |deriv f t| by simpa only [Real.norm_eq_abs] using hh).trans hmono
  have hvar : |f x-f y| ≤ ∫ t in Icc a b, |deriv f t| := by
    rcases le_total y x with h | h
    · exact hordered y x hy hx h
    · simpa only [abs_sub_comm] using hordered x y hx hy h
  have hsq := real_interval_integral_square_le (fun t ↦ |deriv f t|) hd hab
  simp only [sq_abs] at hsq
  have hn : 0 ≤ ∫ t in Icc a b, |deriv f t| := integral_nonneg (fun t ↦ abs_nonneg _)
  have hh := sq_le_sq₀ (abs_nonneg (f x-f y)) hn |>.mpr hvar
  rw [sq_abs] at hh
  exact hh.trans hsq

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_RealIntervalPoincare
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open MeasureTheory Set
open scoped ContDiff
noncomputable section

theorem real_interval_poincare (f : ℝ → ℝ) (hf : ContDiff ℝ ∞ f)
    {a b : ℝ} (hab : a < b) :
    (∫ x in Icc a b, (f x-(∫ y in Icc a b, f y)/(b-a))^2) ≤
      (b-a)^2*(∫ x in Icc a b, (deriv f x)^2) := by
  let L := b-a
  let c := (∫ y in Icc a b, f y)/L
  let D := ∫ x in Icc a b, (deriv f x)^2
  have hL : 0 < L := sub_pos.mpr hab
  have hm : (volume.restrict (Icc a b)).real univ=L := by
    simp [hab.le,L]
  have hpt (x : ℝ) (hx : x ∈ Icc a b) : (f x-c)^2 ≤ L*D := by
    have hdiff : (∫ y in Icc a b, f x-f y) = L*(f x-c) := by
      rw [integral_sub (integrable_const _) hf.continuous.continuousOn.integrableOn_Icc,integral_const]
      change (volume.restrict (Icc a b)).real univ*f x-(∫ y in Icc a b, f y) = L*(f x-c)
      rw [hm]
      dsimp [c]
      field_simp
    have hcs := real_interval_integral_square_le (fun y ↦ f x-f y) (continuous_const.sub hf.continuous) hab
    rw [hdiff] at hcs
    have hbound := setIntegral_mono_on (μ := volume)
      ((continuous_const.sub hf.continuous).pow 2).continuousOn.integrableOn_Icc
      (integrable_const (L*D)) measurableSet_Icc
      (fun y hy ↦ real_interval_derivative_control f hf hab x y hx hy)
    rw [integral_const] at hbound
    change (∫ y in Icc a b, (f x-f y)^2) ≤ (volume.restrict (Icc a b)).real univ*(L*D) at hbound
    rw [hm] at hbound
    have hh := hcs.trans (mul_le_mul_of_nonneg_left hbound hL.le)
    apply (mul_le_mul_iff_right₀ (sq_pos_of_pos hL)).mp
    nlinarith [hh]
  have hfinal := setIntegral_mono_on (μ := volume) ((hf.continuous.sub continuous_const).pow 2).continuousOn.integrableOn_Icc
    (integrable_const (L*D)) measurableSet_Icc hpt
  rw [integral_const] at hfinal
  change (∫ x in Icc a b, (f x-c)^2) ≤ (volume.restrict (Icc a b)).real univ*(L*D) at hfinal
  rw [hm] at hfinal
  change (∫ x in Icc a b, (f x-c)^2) ≤ L^2*D
  nlinarith [hfinal]

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_RealFinCubePoincare
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open MeasureTheory Set Function
open scoped ContDiff
noncomputable section

theorem real_finCube_poincare (n : ℕ) (W : (Fin n → ℝ) → ℝ)
    (hW : ContDiff ℝ ∞ W) :
    (∫ x in realFinCube n, (W x-(∫ y in realFinCube n, W y)/2^n)^2) ≤
      4*(∫ x in realFinCube n, ∑ i, (Yau.coordPartial W x i)^2) := by
  induction n with
  | zero => simp [realFinCube_integral_zero]
  | succ n ih =>
    let F : ℝ × (Fin n → ℝ) → ℝ := fun p ↦ W (Fin.cons p.1 p.2)
    have hF : Continuous F := hW.continuous.comp (real_finCons_smooth n).continuous
    let R : ℝ → ℝ := fun t ↦ (∫ z in realFinCube n, F (t,z))/2^n
    let C : (Fin n → ℝ) → ℝ := fun z ↦ (∫ t in Icc (-1:ℝ) 1, F (t,z))/2
    have hR : Continuous R := (real_interval_cube_integral_continuous n F hF).div_const _
    have hC : Continuous C := (real_cube_interval_integral_continuous n F hF).div_const _
    have hVR : Continuous (fun p : ℝ × (Fin n → ℝ) ↦ (F p-R p.1)^2) :=
      (hF.sub (hR.comp continuous_fst)).pow 2
    have hVC : Continuous (fun p : ℝ × (Fin n → ℝ) ↦ (F p-C p.2)^2) :=
      (hF.sub (hC.comp continuous_snd)).pow 2
    let E0 : ℝ × (Fin n → ℝ) → ℝ := fun p ↦ (Yau.coordPartial W (Fin.cons p.1 p.2) 0)^2
    let ET : ℝ × (Fin n → ℝ) → ℝ := fun p ↦ ∑ i : Fin n,
      (Yau.coordPartial W (Fin.cons p.1 p.2) i.succ)^2
    have hE0 : Continuous E0 :=
      ((Yau.real_coordPartial_smooth W hW 0).continuous.comp (real_finCons_smooth n).continuous).pow 2
    have hET : Continuous ET := continuous_finsetSum _ (fun i _ ↦
      ((Yau.real_coordPartial_smooth W hW i.succ).continuous.comp (real_finCons_smooth n).continuous).pow 2)
    have htail (t : ℝ) : (∫ z in realFinCube n, (F (t,z)-R t)^2) ≤
        4*(∫ z in realFinCube n, ET (t,z)) := by
      have h := ih (fun z ↦ W (Fin.cons t z)) (real_finCube_slice_smooth n W hW t)
      simpa only [real_finCube_slice_partial n W hW] using h
    have hhead (z : Fin n → ℝ) : (∫ t in Icc (-1:ℝ) 1, (F (t,z)-C z)^2) ≤
        4*(∫ t in Icc (-1:ℝ) 1, E0 (t,z)) := by
      have h := real_interval_poincare (fun t ↦ W (Fin.cons t z))
        (real_finCube_line_smooth n W hW z) (by norm_num : (-1:ℝ)<1)
      simp only [real_finCube_line_deriv n W hW] at h
      norm_num at h
      exact h
    have ht := setIntegral_mono_on (μ := volume) (s := Icc (-1:ℝ) 1)
      ((real_interval_cube_integral_continuous n _ hVR).continuousOn.integrableOn_Icc)
      (((real_interval_cube_integral_continuous n ET hET).const_mul 4).continuousOn.integrableOn_Icc)
      measurableSet_Icc (fun t _ ↦ htail t)
    have hh := setIntegral_mono_on (μ := volume)
      (realFinCube_integrable n _ (real_cube_interval_integral_continuous n _ hVC))
      (realFinCube_integrable n _ ((real_cube_interval_integral_continuous n E0 hE0).const_mul 4))
      (realFinCube_isCompact n).measurableSet (fun z _ ↦ hhead z)
    rw [integral_const_mul] at ht hh
    have hvar := (real_interval_cube_variance_le n F hF).trans (add_le_add ht hh)
    rw [← real_interval_cube_integral_swap n E0 hE0] at hvar
    have he (t : ℝ) : (∫ z in realFinCube n, ∑ i : Fin (n+1),
        (Yau.coordPartial W (Fin.cons t z) i)^2) =
        (∫ z in realFinCube n, E0 (t,z))+(∫ z in realFinCube n, ET (t,z)) := by
      simp_rw [Fin.sum_univ_succ]
      exact integral_add
        (realFinCube_integrable n _ (hE0.comp (continuous_const.prodMk continuous_id)))
        (realFinCube_integrable n _ (hET.comp (continuous_const.prodMk continuous_id)))
    have hWC : Continuous (fun x ↦ (W x-(∫ y in realFinCube (n+1), W y)/2^(n+1))^2) :=
      (hW.continuous.sub continuous_const).pow 2
    have hWE : Continuous (fun x ↦ ∑ i, (Yau.coordPartial W x i)^2) :=
      continuous_finsetSum _ (fun i _ ↦ (Yau.real_coordPartial_smooth W hW i).continuous.pow 2)
    rw [realFinCube_integral_succ n _ hWC,
      realFinCube_integral_succ n W hW.continuous,
      realFinCube_integral_succ n _ hWE]
    simp_rw [he]
    rw [integral_add
      ((real_interval_cube_integral_continuous n E0 hE0).continuousOn.integrableOn_Icc)
      ((real_interval_cube_integral_continuous n ET hET).continuousOn.integrableOn_Icc)]
    rw [show (2:ℝ)^(n+1)=2*2^n by rw [pow_succ]; ring]
    calc
      _ ≤ 4*(∫ t in Icc (-1:ℝ) 1, ∫ z in realFinCube n, ET (t,z))+
          4*(∫ t in Icc (-1:ℝ) 1, ∫ z in realFinCube n, E0 (t,z)) := hvar
      _ = _ := by ring

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_RealScaledCubePoincare
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open MeasureTheory Set Function
open scoped ContDiff
noncomputable section

lemma real_affine_coordPartial (n : ℕ) (W : (Fin n → ℝ) → ℝ)
    (hW : ContDiff ℝ ∞ W) (c : Fin n → ℝ) (r : ℝ) (x : Fin n → ℝ) (i : Fin n) :
    Yau.coordPartial (fun y ↦ W (c+r • y)) x i = r*Yau.coordPartial W (c+r • x) i := by
  let L : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) := r • ContinuousLinearMap.id ℝ (Fin n → ℝ)
  have hd : HasFDerivAt (fun y ↦ c+r • y) L x := L.hasFDerivAt.const_add c
  have h := ((hW.differentiable (by simp) (c+r • x)).hasFDerivAt.comp x hd).fderiv
  simp only [Function.comp_def] at h
  simp [Yau.coordPartial,h,L]

theorem real_scaledCube_poincare (n : ℕ) (c : Fin n → ℝ) {r : ℝ} (hr : 0 < r)
    (W : (Fin n → ℝ) → ℝ) (hW : ContDiff ℝ ∞ W) :
    (∫ x in realScaledCube n c r,
      (W x-(∫ y in realScaledCube n c r, W y)/(2*r)^n)^2) ≤
      4*r^2*(∫ x in realScaledCube n c r, ∑ i, (Yau.coordPartial W x i)^2) := by
  have hm : (∫ y in realScaledCube n c r, W y)/(2*r)^n =
      (∫ y in realFinCube n, W (c+r • y))/2^n := by
    rw [realScaledCube_integral n c hr,mul_pow]
    field_simp
  have h := real_finCube_poincare n (fun x ↦ W (c+r • x))
    (hW.comp (contDiff_const.add (contDiff_id.const_smul r)))
  simp_rw [real_affine_coordPartial n W hW,mul_pow,← Finset.mul_sum] at h
  rw [integral_const_mul] at h
  rw [hm,realScaledCube_integral n c hr,realScaledCube_integral n c hr]
  calc
    _ ≤ r^n*(4*(r^2*(∫ x in realFinCube n, ∑ i, (Yau.coordPartial W (c+r • x) i)^2))) :=
      mul_le_mul_of_nonneg_left h (pow_nonneg hr.le n)
    _ = _ := by ring

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_RealCubeCellApproximation
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Yau.Jets MeasureTheory Set Function
open scoped ContDiff
noncomputable section

lemma realCubeCell_poincare {n : ℕ} (hn : 0 < n) (k : Fin 4 → Fin n)
    (W : Yau.Jets.Coord → ℝ) (hW : ContDiff ℝ ∞ W) :
    (∫ x in realCubeCell n k, (W x-realCubeCellMean W n k)^2) ≤
      (4/(n:ℝ)^2)*(∫ x in realCubeCell n k, ∑ i, (Yau.coordPartial W x i)^2) := by
  have hnR : (0:ℝ)<n := by exact_mod_cast hn
  have h := real_scaledCube_poincare 4 (corrugationCubeCenter (fun _ ↦ -1) 2 n k)
    (div_pos zero_lt_one hnR) W hW
  simpa only [realCubeCell,realCubeCellMean,mul_one_div,div_pow,one_pow,mul_one_div] using h

theorem realCubeCell_total_error {n : ℕ} (hn : 0 < n)
    (W : Yau.Jets.Coord → ℝ) (hW : ContDiff ℝ ∞ W) :
    (∑ k : Fin 4 → Fin n, ∫ x in realCubeCell n k, (W x-realCubeCellMean W n k)^2) ≤
      (4/(n:ℝ)^2)*(∫ x in realFinCube 4, ∑ i, (Yau.coordPartial W x i)^2) := by
  have h := Finset.sum_le_sum (fun k (_ : k ∈ (Finset.univ : Finset (Fin 4 → Fin n))) ↦
    realCubeCell_poincare hn k W hW)
  rw [← Finset.mul_sum,← realCubeCell_integral_sum hn] at h
  · exact h
  · exact realFinCube_integrable 4 _
      (continuous_finsetSum _ (fun i _ ↦ (Yau.real_coordPartial_smooth W hW i).continuous.pow 2))

lemma realCubeCell_mean_square_le {n : ℕ} (hn : 0 < n) (k : Fin 4 → Fin n)
    (W : Yau.Jets.Coord → ℝ) (hW : Continuous W) :
    (2/(n:ℝ))^4*(realCubeCellMean W n k)^2 ≤ ∫ x in realCubeCell n k, W x^2 := by
  have hnR : (0:ℝ)<n := by exact_mod_cast hn
  let : IsFiniteMeasure (volume.restrict (realCubeCell n k)) :=
    isFiniteMeasure_restrict.mpr (realCubeCell_isCompact n k).measure_ne_top
  have h := real_mean_square_contraction (volume.restrict (realCubeCell n k))
    (by rw [realCubeCell_mass hn]; positivity) W
    (hW.continuousOn.integrableOn_compact (realCubeCell_isCompact n k))
    ((hW.pow 2).continuousOn.integrableOn_compact (realCubeCell_isCompact n k))
  simpa only [realCubeCell_mass hn,realCubeCellMean] using h

lemma realCubeCell_mean_bound {n : ℕ} (hn : 0 < n) (k : Fin 4 → Fin n)
    (W : Yau.Jets.Coord → ℝ) (hW : Continuous W) {C : ℝ} (hC : 0 ≤ C)
    (hbound : (∫ x in realFinCube 4, W x^2) ≤ C) :
    |realCubeCellMean W n k| ≤ C/(2/(n:ℝ))^4+1 := by
  have hnR : (0:ℝ)<n := by exact_mod_cast hn
  have hm : 0 < (2/(n:ℝ))^4 := by positivity
  have hi := setIntegral_mono_set (realFinCube_integrable 4 _ (hW.pow 2))
    (Filter.Eventually.of_forall (fun x ↦ sq_nonneg (W x)))
    (realCubeCell_subset hn k).eventuallyLE
  have hs := (realCubeCell_mean_square_le hn k W hW).trans (hi.trans hbound)
  have hs' : (realCubeCellMean W n k)^2 ≤ C/(2/(n:ℝ))^4 := by
    apply (le_div_iff₀ hm).mpr
    simpa only [mul_comm] using hs
  have hv : 0 ≤ C/(2/(n:ℝ))^4 := div_nonneg hC hm.le
  rw [abs_le]
  constructor <;> nlinarith [sq_nonneg (realCubeCellMean W n k-1),sq_nonneg (realCubeCellMean W n k+1)]

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_RealCubeCellDistance
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open MeasureTheory Set Function
open scoped ContDiff
noncomputable section

lemma realCubeCellMean_sub (n : ℕ) (k : Fin 4 → Fin n)
    (W V : Yau.Jets.Coord → ℝ) (hW : Continuous W) (hV : Continuous V) :
    realCubeCellMean (fun x ↦ W x-V x) n k = realCubeCellMean W n k-realCubeCellMean V n k := by
  unfold realCubeCellMean
  rw [integral_sub (hW.continuousOn.integrableOn_compact (realCubeCell_isCompact n k))
    (hV.continuousOn.integrableOn_compact (realCubeCell_isCompact n k)),sub_div]

theorem realCubeCell_square_decomposition {n : ℕ} (hn : 0 < n)
    (W : Yau.Jets.Coord → ℝ) (hW : Continuous W) :
    (∫ x in realFinCube 4, W x^2) =
      (∑ k : Fin 4 → Fin n, ∫ x in realCubeCell n k, (W x-realCubeCellMean W n k)^2)+
      ∑ k : Fin 4 → Fin n, (2/(n:ℝ))^4*(realCubeCellMean W n k)^2 := by
  rw [realCubeCell_integral_sum hn (fun x ↦ W x^2) (realFinCube_integrable 4 _ (hW.pow 2)),← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k _
  have hnR : (0:ℝ)<n := by exact_mod_cast hn
  let : IsFiniteMeasure (volume.restrict (realCubeCell n k)) :=
    isFiniteMeasure_restrict.mpr (realCubeCell_isCompact n k).measure_ne_top
  have h := real_mean_square_decomposition (volume.restrict (realCubeCell n k))
    (by rw [realCubeCell_mass hn]; positivity) W
    (hW.continuousOn.integrableOn_compact (realCubeCell_isCompact n k))
    ((hW.pow 2).continuousOn.integrableOn_compact (realCubeCell_isCompact n k)) 0
  simpa only [sub_zero,realCubeCell_mass hn,realCubeCellMean] using h

theorem realCubeCell_square_bound {n : ℕ} (hn : 0 < n)
    (W : Yau.Jets.Coord → ℝ) (hW : ContDiff ℝ ∞ W) :
    (∫ x in realFinCube 4, W x^2) ≤
      (4/(n:ℝ)^2)*(∫ x in realFinCube 4, ∑ i, (Yau.coordPartial W x i)^2)+
      ∑ k : Fin 4 → Fin n, (2/(n:ℝ))^4*(realCubeCellMean W n k)^2 := by
  rw [realCubeCell_square_decomposition hn W hW.continuous]
  exact add_le_add (realCubeCell_total_error hn W hW) le_rfl

lemma real_cube_energy_sub (W V : Yau.Jets.Coord → ℝ)
    (hW : ContDiff ℝ ∞ W) (hV : ContDiff ℝ ∞ V) :
    (∫ x in realFinCube 4, ∑ i, (Yau.coordPartial (fun y ↦ W y-V y) x i)^2) ≤
      2*((∫ x in realFinCube 4, ∑ i, (Yau.coordPartial W x i)^2)+
        (∫ x in realFinCube 4, ∑ i, (Yau.coordPartial V x i)^2)) := by
  have hp (x : Yau.Jets.Coord) (i : Fin 4) :
      Yau.coordPartial (fun y ↦ W y-V y) x i = Yau.coordPartial W x i-Yau.coordPartial V x i := by
    simp only [Yau.coordPartial,fderiv_fun_sub (hW.differentiable (by simp) x)
      (hV.differentiable (by simp) x),_root_.sub_apply]
  have hc (F : Yau.Jets.Coord → ℝ) (hF : ContDiff ℝ ∞ F) :
      Continuous (fun x ↦ ∑ i, (Yau.coordPartial F x i)^2) :=
    continuous_finsetSum _ (fun i _ ↦ (Yau.real_coordPartial_smooth F hF i).continuous.pow 2)
  have hpt (x : Yau.Jets.Coord) : (∑ i, (Yau.coordPartial (fun y ↦ W y-V y) x i)^2) ≤
      2*((∑ i, (Yau.coordPartial W x i)^2)+(∑ i, (Yau.coordPartial V x i)^2)) := by
    simp_rw [hp]
    rw [← Finset.sum_add_distrib,Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    nlinarith [sq_nonneg (Yau.coordPartial W x i+Yau.coordPartial V x i)]
  have h := setIntegral_mono_on (μ := volume)
    (realFinCube_integrable 4 _ (hc _ (hW.sub hV)))
    (realFinCube_integrable 4 _ (((hc W hW).add (hc V hV)).const_mul 2))
    (realFinCube_isCompact 4).measurableSet (fun x _ ↦ hpt x)
  simp only [Pi.add_apply] at h
  rw [integral_const_mul,integral_add (realFinCube_integrable 4 _ (hc W hW))
    (realFinCube_integrable 4 _ (hc V hV))] at h
  exact h

theorem realCubeCell_distance_bound {n : ℕ} (hn : 0 < n)
    (W V : Yau.Jets.Coord → ℝ) (hW : ContDiff ℝ ∞ W) (hV : ContDiff ℝ ∞ V) :
    (∫ x in realFinCube 4, (W x-V x)^2) ≤
      (8/(n:ℝ)^2)*((∫ x in realFinCube 4, ∑ i, (Yau.coordPartial W x i)^2)+
        (∫ x in realFinCube 4, ∑ i, (Yau.coordPartial V x i)^2))+
      ∑ k : Fin 4 → Fin n, (2/(n:ℝ))^4*(realCubeCellMean W n k-realCubeCellMean V n k)^2 := by
  have h := realCubeCell_square_bound hn (fun x ↦ W x-V x) (hW.sub hV)
  simp_rw [realCubeCellMean_sub n _ W V hW.continuous hV.continuous] at h
  have he := mul_le_mul_of_nonneg_left (real_cube_energy_sub W V hW hV)
    (show 0 ≤ 4/(n:ℝ)^2 by positivity)
  have ht := h.trans (add_le_add he le_rfl)
  rw [← mul_assoc (4/(n:ℝ)^2) 2,show (4/(n:ℝ)^2)*2=8/(n:ℝ)^2 by ring] at ht
  exact ht

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_RealFiniteWeightedCauchy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Filter
open scoped Topology

theorem real_finite_weighted_cauchy {I : Type*} [Fintype I]
    (a : ℕ → I → ℝ) (f w : I → ℝ) (hw : ∀ i, 0 ≤ w i)
    (ha : ∀ i, Tendsto (fun j ↦ a j i) atTop (𝓝 (f i))) :
    ∀ eps > 0, ∃ N : ℕ, ∀ i ≥ N, ∀ j ≥ N,
      (∑ k, w k*(a i k-a j k)^2) < eps := by
  classical
  let S : ℕ → ℝ := fun j ↦ ∑ k, w k*(a j k-f k)^2
  have ht : Tendsto S atTop (𝓝 0) := by
    have h : Tendsto S atTop (𝓝 (∑ k, w k*(f k-f k)^2)) :=
      tendsto_finsetSum (Finset.univ : Finset I) (fun k _ ↦
      tendsto_const_nhds.mul (((ha k).sub tendsto_const_nhds).pow 2))
    simpa only [sub_self,zero_pow (by decide : 2≠0),mul_zero,Finset.sum_const_zero] using h
  intro eps heps
  obtain ⟨N,hN⟩ := eventually_atTop.mp (ht.eventually_lt_const (show 0 < eps/4 by linarith))
  refine ⟨N,fun i hi j hj ↦ ?_⟩
  have hb : (∑ k, w k*(a i k-a j k)^2) ≤ 2*(S i+S j) := by
    dsimp [S]
    rw [← Finset.sum_add_distrib,Finset.mul_sum]
    apply Finset.sum_le_sum
    intro k _
    have hsq : (a i k-a j k)^2 ≤ 2*((a i k-f k)^2+(a j k-f k)^2) := by
      nlinarith [sq_nonneg (a i k+a j k-2*f k)]
    calc
      _ ≤ w k*(2*((a i k-f k)^2+(a j k-f k)^2)) := mul_le_mul_of_nonneg_left hsq (hw k)
      _ = _ := by ring
  exact hb.trans_lt (by linarith [hN i hi,hN j hj])

end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_RealCubeEnergyCompactness
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open MeasureTheory Set Filter
open scoped ContDiff Topology
noncomputable section

theorem real_countable_cube_energy_subsequence {P : Type*} [Countable P]
    (W : P → ℕ → Yau.Jets.Coord → ℝ)
    (hW : ∀ p j, ContDiff ℝ ∞ (W p j)) (C : P → ℝ) (hC : ∀ p, 0 < C p)
    (hbound : ∀ p j, (∫ x in realFinCube 4, (W p j x)^2)+
      (∫ x in realFinCube 4, ∑ i, (Yau.coordPartial (W p j) x i)^2) ≤ C p) :
    ∃ nu : ℕ → ℕ, StrictMono nu ∧ ∀ p, ∀ eps > 0, ∃ N : ℕ,
      ∀ i ≥ N, ∀ j ≥ N, (∫ x in realFinCube 4, (W p (nu i) x-W p (nu j) x)^2) < eps := by
  have hs (p : P) (j : ℕ) : (∫ x in realFinCube 4, (W p j x)^2) ≤ C p :=
    (le_add_of_nonneg_right (integral_nonneg (fun x ↦ Finset.sum_nonneg (fun i _ ↦ sq_nonneg _)))).trans (hbound p j)
  have he (p : P) (j : ℕ) : (∫ x in realFinCube 4, ∑ i, (Yau.coordPartial (W p j) x i)^2) ≤ C p :=
    (le_add_of_nonneg_left (integral_nonneg (fun x ↦ sq_nonneg (W p j x)))).trans (hbound p j)
  let I := P × ((n : ℕ) × (Fin 4 → Fin (n+1)))
  let a : ℕ → I → ℝ := fun j k ↦ realCubeCellMean (W k.1 j) (k.2.1+1) k.2.2
  let B : I → ℝ := fun k ↦ C k.1/(2/((k.2.1+1:ℕ):ℝ))^4+1
  have hb (j : ℕ) (k : I) : |a j k| ≤ B k :=
    realCubeCell_mean_bound (Nat.succ_pos k.2.1) k.2.2 (W k.1 j) (hW k.1 j).continuous (hC k.1).le (hs k.1 j)
  obtain ⟨f,nu,hnu,ht⟩ := real_countable_bounded_subsequence a B hb
  refine ⟨nu,hnu,?_⟩
  intro p eps heps
  obtain ⟨m,hm⟩ := exists_nat_gt (32*C p/eps)
  have hnR : (1:ℝ) ≤ ((m+1:ℕ):ℝ) := by exact_mod_cast (Nat.succ_le_succ (Nat.zero_le m))
  have hn0 : (0:ℝ) < ((m+1:ℕ):ℝ) := zero_lt_one.trans_le hnR
  have hsize : 16*C p/((m+1:ℕ):ℝ)^2 < eps/2 := by
    have hbig : 32*C p/eps < ((m+1:ℕ):ℝ) := hm.trans (by exact_mod_cast Nat.lt_succ_self m)
    have hh := (div_lt_iff₀ heps).mp hbig
    have hsquare : ((m+1:ℕ):ℝ) ≤ ((m+1:ℕ):ℝ)^2 := by nlinarith
    apply (div_lt_iff₀ (sq_pos_of_pos hn0)).mpr
    nlinarith [mul_le_mul_of_nonneg_left hsquare heps.le]
  obtain ⟨N,hN⟩ := real_finite_weighted_cauchy
    (fun (j : ℕ) (k : Fin 4 → Fin (m+1)) ↦ realCubeCellMean (W p (nu j)) (m+1) k)
    (fun k ↦ f ⟨p,m,k⟩) (fun _ ↦ (2/((m+1:ℕ):ℝ))^4)
    (fun _ ↦ by positivity) (fun k ↦ ht ⟨p,m,k⟩) (eps/2) (by linarith)
  refine ⟨N,fun i hi j hj ↦ ?_⟩
  have h := realCubeCell_distance_bound (Nat.succ_pos m) (W p (nu i)) (W p (nu j)) (hW p (nu i)) (hW p (nu j))
  have henergy := mul_le_mul_of_nonneg_left (add_le_add (he p (nu i)) (he p (nu j)))
    (show 0 ≤ 8/((m+1:ℕ):ℝ)^2 by positivity)
  have henergy' : (8/((m+1:ℕ):ℝ)^2)*
      ((∫ x in realFinCube 4, ∑ k, (Yau.coordPartial (W p (nu i)) x k)^2)+
        (∫ x in realFinCube 4, ∑ k, (Yau.coordPartial (W p (nu j)) x k)^2)) < eps/2 := by
    apply henergy.trans_lt
    calc
      _ = 16*C p/((m+1:ℕ):ℝ)^2 := by ring
      _ < _ := hsize
  exact h.trans_lt (by linarith [henergy',hN i hi j hj])

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Charts_SphereEnergyCompactness
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Manifold Yau.Geometry MeasureTheory Set
open scoped ContDiff
noncomputable section

theorem sphere_energy_subsequence (A : IntrinsicTensor) (hA : IntrinsicTensorSmooth A)
    (hs : ∀ x alpha beta, A x alpha beta = A x beta alpha)
    (hp : ∀ x alpha, alpha ≠ 0 → 0 < A x alpha alpha)
    (rho : Base → ℝ) (hr : Continuous rho) (hrp : ∀ x, 0 < rho x)
    (W : ℕ → Base → ℝ) (hW : ∀ j, ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ (W j))
    {C : ℝ} (hC : 0 < C)
    (hbound : ∀ j, sphereWeightedPairing rho (W j) (W j)+sphereDirichletForm A (W j) (W j) ≤ C) :
    ∃ nu : ℕ → ℕ, StrictMono nu ∧ ∀ eps > 0, ∃ N : ℕ, ∀ i ≥ N, ∀ j ≥ N,
      sphereWeightedPairing rho (W (nu i)-W (nu j)) (W (nu i)-W (nu j)) < eps := by
  classical
  obtain ⟨P,R,hR,hcomp⟩ := sphere_finite_chart_l2_comparison rho hr hrp
  let I := {p // p ∈ P}
  choose K hK hKb using (fun p : I ↦ sphere_chart_cube_energy_bound A hA hs hp rho hr hrp p.val)
  let F : I → ℕ → Yau.Jets.Coord → ℝ := fun p j ↦ W j ∘ sphereChartCoordMap p.val
  have hF (p : I) (j : ℕ) : ContDiff ℝ ∞ (F p j) := spherePullback_smooth (W j) (hW j) p.val
  have hb (p : I) (j : ℕ) : (∫ x in realFinCube 4, (F p j x)^2)+
      (∫ x in realFinCube 4, ∑ i, (Yau.coordPartial (F p j) x i)^2) ≤ K p*C :=
    (hKb p (W j) (hW j)).trans (mul_le_mul_of_nonneg_left (hbound j) (hK p).le)
  obtain ⟨nu,hnu,hlocal⟩ := real_countable_cube_energy_subsequence F hF (fun p ↦ K p*C)
    (fun p ↦ mul_pos (hK p) hC) hb
  refine ⟨nu,hnu,?_⟩
  intro eps heps
  let delta := eps/(R*((Fintype.card I:ℝ)+1))
  have hd : 0 < delta := div_pos heps (mul_pos hR (by positivity))
  choose Ns hNs using (fun p : I ↦ hlocal p delta hd)
  let N := Finset.univ.sup Ns
  refine ⟨N,fun i hi j hj ↦ ?_⟩
  have hpt (p : I) : (∫ x in realFinCube 4, (F p (nu i) x-F p (nu j) x)^2) ≤ delta := by
    have hpN : Ns p ≤ N := Finset.le_sup (f := Ns) (Finset.mem_univ p)
    exact (hNs p i (hpN.trans hi) j (hpN.trans hj)).le
  have hsum : (∑ p : I, ∫ x in realFinCube 4, (F p (nu i) x-F p (nu j) x)^2) ≤
      (Fintype.card I:ℝ)*delta := by
    simpa using Finset.sum_le_sum (fun p (_ : p ∈ (Finset.univ : Finset I)) ↦ hpt p)
  have h := (hcomp (W (nu i)-W (nu j)) ((hW (nu i)).continuous.sub (hW (nu j)).continuous)).trans
    (mul_le_mul_of_nonneg_left hsum hR.le)
  apply h.trans_lt
  have heq : R*((Fintype.card I:ℝ)+1)*delta=eps := by
    dsimp [delta]
    field_simp
  nlinarith [mul_pos hR hd]

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

local instance sphereEnergyL2MapMeasurable_r03b2c7_1 : MeasurableSpace Base := borel Base
local instance sphereEnergyL2MapBorel_r03b2c7_1 : BorelSpace Base := ⟨rfl⟩
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
-- module Solutions.OAIQ237_NY.NodalSets_Charts_SphereEnergyL2Compact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open MeasureTheory Filter Metric Set
open scoped Topology
noncomputable section

local instance sphereEnergyL2CompactMeasurable_r03b2c7_1 : MeasurableSpace Base := borel Base
local instance sphereEnergyL2CompactBorel_r03b2c7_1 : BorelSpace Base := ⟨rfl⟩
theorem sphereEnergyL2_smooth_subsequence (d : SphereEnergyData)
    (u : ℕ → SphereEnergySmooth d) {C : ℝ} (hC : 0 < C) (hb : ∀ j, ‖u j‖ ≤ C) :
    ∃ nu : ℕ → ℕ, StrictMono nu ∧ CauchySeq (fun j ↦ sphereEnergyL2Linear d (u (nu j))) := by
  obtain ⟨nu,hnu,hc⟩ := sphere_energy_subsequence d.tensor d.smooth d.symm d.pos
    d.density d.continuous d.positive (fun j ↦ SphereEnergySmooth.toSmooth d (u j))
    (fun j ↦ (SphereEnergySmooth.toSmooth d (u j)).property) (sq_pos_of_pos hC)
    (fun j ↦ by rw [← SphereEnergySmooth.norm_sq]; nlinarith [hb j,norm_nonneg (u j)])
  refine ⟨nu,hnu,Metric.cauchySeq_iff.mpr ?_⟩
  intro eps heps
  obtain ⟨N,hN⟩ := hc (eps^2) (sq_pos_of_pos heps)
  refine ⟨N,fun i hi j hj ↦ ?_⟩
  have h := hN i hi j hj
  have heq := sphereEnergyL2Linear_norm_sq d (u (nu i)-u (nu j))
  rw [map_sub] at heq
  rw [dist_eq_norm]
  change sphereWeightedPairing d.density
    (SphereEnergySmooth.toSmooth d (u (nu i)-u (nu j)))
    (SphereEnergySmooth.toSmooth d (u (nu i)-u (nu j))) < eps^2 at h
  nlinarith [norm_nonneg (sphereEnergyL2Linear d (u (nu i))-sphereEnergyL2Linear d (u (nu j)))]

theorem sphereEnergyL2_bounded_subsequence (d : SphereEnergyData)
    (z : ℕ → SphereEnergyHilbert d) {C : ℝ} (hC : 0 < C) (hb : ∀ j, ‖z j‖ ≤ C) :
    ∃ nu : ℕ → ℕ, StrictMono nu ∧ ∃ v : SphereWeightedL2 d,
      Tendsto (fun j ↦ sphereEnergyL2Map d (z (nu j))) atTop (𝓝 v) := by
  have he (j : ℕ) : 0 < 1/((j:ℝ)+1) := by positivity
  choose u hu using (fun j ↦ (sphereEnergyToCompletion_dense d).exists_dist_lt (z j) (he j))
  have hu_bound (j : ℕ) : ‖u j‖ ≤ C+1 := by
    have hn : ‖sphereEnergyToCompletion d (u j)‖ ≤ ‖z j‖ + 1/((j:ℝ)+1) :=
      norm_le_norm_add_const_of_dist_le (by rw [dist_comm]; exact (hu j).le)
    rw [(sphereEnergyToCompletion d).norm_map] at hn
    have he1 : 1/((j:ℝ)+1) ≤ 1 := (div_le_one (by positivity)).mpr (by linarith [Nat.cast_nonneg (α := ℝ) j])
    linarith [hb j,hu j]
  obtain ⟨nu,hnu,hc⟩ := sphereEnergyL2_smooth_subsequence d u (by positivity) hu_bound
  obtain ⟨v,hv⟩ := cauchySeq_tendsto_of_complete hc
  refine ⟨nu,hnu,v,hv.congr_dist ?_⟩
  have he0 : Tendsto (fun j : ℕ ↦ 1/((nu j:ℝ)+1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat.comp hnu.tendsto_atTop
  apply squeeze_zero (fun j ↦ dist_nonneg) (fun j ↦ ?_) he0
  rw [← sphereEnergyL2Map_coe,dist_eq_norm,← map_sub]
  have h := sphereEnergyL2Map_apply_norm_le d (sphereEnergyToCompletion d (u (nu j))-z (nu j))
  apply h.trans
  simpa only [← dist_eq_norm,dist_comm] using (hu (nu j)).le

theorem sphereEnergyL2Map_compact (d : SphereEnergyData) : IsCompactOperator (sphereEnergyL2Map d) := by
  apply (isCompactOperator_iff_isCompact_closure_image_closedBall
    (sphereEnergyL2Map d).toLinearMap zero_lt_one).mpr
  apply IsSeqCompact.isCompact
  intro y hy
  have he (j : ℕ) : 0 < 1/((j:ℝ)+1) := by positivity
  have ha (j : ℕ) := Metric.mem_closure_iff.mp (hy j) _ (he j)
  choose w hw hd using ha
  choose z hz hzw using hw
  have hb (j : ℕ) : ‖z j‖ ≤ (1:ℝ) := by simpa only [mem_closedBall,dist_zero_right] using hz j
  obtain ⟨nu,hnu,v,hv⟩ := sphereEnergyL2_bounded_subsequence d z zero_lt_one hb
  have hconv : Tendsto (y ∘ nu) atTop (𝓝 v) := by
    apply hv.congr_dist
    apply squeeze_zero (fun j ↦ dist_nonneg) (fun j ↦ ?_)
      (tendsto_one_div_add_atTop_nhds_zero_nat.comp hnu.tendsto_atTop)
    have hh := (hd (nu j)).le
    rw [← hzw (nu j)] at hh
    simpa only [Function.comp_apply,dist_comm] using! hh
  refine ⟨v,?_,nu,hnu,hconv⟩
  exact isClosed_closure.mem_of_tendsto hconv (Eventually.of_forall (fun j ↦ hy (nu j)))

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

local instance sphereWeakResolventMeasurable_r03b2c7_1 : MeasurableSpace Base := borel Base
local instance sphereWeakResolventBorel_r03b2c7_1 : BorelSpace Base := ⟨rfl⟩
theorem sphereL2Resolvent_compact_oai (d : SphereEnergyData) : IsCompactOperator (sphereL2Resolvent d) :=
  (sphereEnergyL2Map_compact d).comp_clm (sphereWeakSolution d)

end
end Yau.Target

end OAI
end

theorem solution : type_of% @OAI.Yau.Target.sphereL2Resolvent_compact_oai := @OAI.Yau.Target.sphereL2Resolvent_compact_oai
