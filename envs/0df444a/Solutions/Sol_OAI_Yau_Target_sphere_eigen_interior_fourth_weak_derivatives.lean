-- Prove2me | solution 1 for OAI.Yau.Target.sphere_eigen_interior_fourth_weak_derivatives
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T00:38:37.188067+00:00
-- url     : https://prove2.me/submissions/e54434d8-e7e3-4483-85ec-2bbd67c30fa5

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
import Theorems.Thm_OAI_Yau_Target_sphere_eigen_hessian_localized_energy
import Theorems.Thm_OAI_Yau_Target_sphere_same_third_difference_bound

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

local instance sphereEnergyL2MapMeasurable_rba70d4_1 : MeasurableSpace Base := borel Base
local instance sphereEnergyL2MapBorel_rba70d4_1 : BorelSpace Base := ⟨rfl⟩
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

theorem sphereEnergyL2Map_norm_le (d : SphereEnergyData) : ‖sphereEnergyL2Map d‖ ≤ 1 := by
  apply LinearMap.opNorm_extendOfNorm_le (sphereEnergyToCompletion_dense d) zero_le_one
  intro u
  simpa using sphereEnergyL2Linear_norm_le d u

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

end Yau

end

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

local instance sphereWeakResolventMeasurable_rba70d4_1 : MeasurableSpace Base := borel Base
local instance sphereWeakResolventBorel_rba70d4_1 : BorelSpace Base := ⟨rfl⟩
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

local instance sphereChartDivergenceDataMeasurable_rba70d4_1 : MeasurableSpace Base := borel Base
local instance sphereChartDivergenceDataBorel_rba70d4_1 : BorelSpace Base := ⟨rfl⟩
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
-- module Solutions.OAIQ237_NY.NodalSets_Coefficients_RealFiniteCoefficientL2Bound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau
open MeasureTheory Set
noncomputable section

theorem real_L2_add_square_bound {α : Type*} [MeasurableSpace α] (mu : Measure α)
    (u v : α → ℝ) (hu : MemLp u 2 mu) (hv : MemLp v 2 mu) :
    (∫ x, (u x+v x)^2 ∂mu) ≤ 2*(∫ x, (u x)^2 ∂mu)+2*(∫ x, (v x)^2 ∂mu) := by
  rw [← integral_const_mul,← integral_const_mul,
    ← integral_add (hu.integrable_sq.const_mul 2) (hv.integrable_sq.const_mul 2)]
  apply integral_mono (hu.add hv).integrable_sq
    ((hu.integrable_sq.const_mul 2).add (hv.integrable_sq.const_mul 2))
  intro x
  change (u x+v x)^2 ≤ 2*(u x)^2+2*(v x)^2
  nlinarith [sq_nonneg (u x-v x)]

theorem real_compact_finite_coefficient_L2_bound {n m : ℕ} {K : Set (Coord n)}
    (hK : IsCompact K) (A : Coord n → Fin m → ℝ) (hA : ∀ j, Continuous (fun x ↦ A x j)) :
    ∃ C > 0, ∀ U : Fin m → Coord n → ℝ, (∀ j, MemLp (U j) 2 (volume.restrict K)) →
      MemLp (fun x ↦ ∑ j, A x j*U j x) 2 (volume.restrict K) ∧
      (∫ x in K, (∑ j, A x j*U j x)^2) ≤ C*(∑ j, ∫ x in K, (U j x)^2) := by
  obtain ⟨B,hB,hb⟩ := (hK.image (continuous_pi hA)).isBounded.exists_pos_norm_le
  refine ⟨((m:ℝ)+1)*B^2,by positivity,fun U hU ↦ ?_⟩
  have hprod (j : Fin m) : MemLp (fun x ↦ A x j*U j x) 2 (volume.restrict K) := by
    obtain ⟨_,_,hbound⟩ := real_compact_multiplier_bound hK (fun x ↦ A x j) (hA j)
    exact (hbound (U j) (hU j)).1
  have hsum : MemLp (fun x ↦ ∑ j, A x j*U j x) 2 (volume.restrict K) :=
    memLp_finsetSum Finset.univ (fun j _ ↦ hprod j)
  refine ⟨hsum,?_⟩
  have hisum := integrable_finsetSum Finset.univ (fun j _ ↦ (hU j).integrable_sq)
  rw [← integral_finsetSum Finset.univ (fun j _ ↦ (hU j).integrable_sq),← integral_const_mul]
  apply setIntegral_mono_on hsum.integrable_sq (hisum.const_mul _) hK.measurableSet
  intro x hx
  have hcoef (j : Fin m) : (A x j)^2 ≤ B^2 := by
    have ht := (norm_le_pi_norm (A x) j).trans (hb _ ⟨x,hx,rfl⟩)
    rw [Real.norm_eq_abs] at ht
    nlinarith [sq_abs (A x j),abs_nonneg (A x j)]
  have hcoefsum := Finset.sum_le_sum (s := Finset.univ) (fun j _ ↦ hcoef j)
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at hcoefsum
  have hCS := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun j ↦ A x j) (fun j ↦ U j x)
  have hn : 0 ≤ ∑ j, (U j x)^2 := Finset.sum_nonneg (fun _ _ ↦ sq_nonneg _)
  have hmul := mul_le_mul_of_nonneg_right hcoefsum hn
  have hextra := mul_nonneg (sq_nonneg B) hn
  nlinarith only [hCS,hmul,hextra]

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
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_RealCommutatorDerivativeBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau
open MeasureTheory Set
open scoped ContDiff
noncomputable section

theorem real_localized_commutator_derivative_bound {n : ℕ} {K : Set (Coord n)}
    (hK : IsCompact K) (C : Coord n → Fin n → Fin n → ℝ)
    (hC : ∀ a j, ContDiff ℝ ∞ (fun x ↦ C x a j))
    (chi : Coord n → ℝ) (hc : ContDiff ℝ ∞ chi) (hs : tsupport chi ⊆ K)
    (k j i : Fin n) :
    ∃ B > 0, ∀ (U : Fin n → Coord n → ℝ) (H : Fin n → Fin n → Coord n → ℝ),
      (∀ a, MemLp (U a) 2 (volume.restrict K)) →
      (∀ a l, MemLp (H a l) 2 (volume.restrict K)) →
      let G := realWeakGradientCommutator C U k j
      let DG := realWeakGradientCommutatorDerivative C U H k j i
      MemLp (fun x ↦ chi x*DG x+coordPartial chi x i*G x) 2 volume ∧
      (∫ x, (chi x*DG x+coordPartial chi x i*G x)^2) ≤
        B*((∑ a, ∫ x in K, (U a x)^2)+(∑ a, ∫ x in K, (H a i x)^2)) := by
  let A := fun x a ↦ chi x*coordPartial (fun y ↦ C y a j) x k
  let D := fun x a ↦ chi x*coordPartial (fun y ↦ coordPartial (fun z ↦ C z a j) y k) x i+
    coordPartial chi x i*coordPartial (fun y ↦ C y a j) x k
  have hA (a : Fin n) : Continuous (fun x ↦ A x a) :=
    hc.continuous.mul (real_coordPartial_smooth _ (hC a j) k).continuous
  have hD (a : Fin n) : Continuous (fun x ↦ D x a) :=
    (hc.continuous.mul (real_coordPartial_smooth _ (real_coordPartial_smooth _ (hC a j) k) i).continuous).add
      ((real_coordPartial_smooth chi hc i).continuous.mul (real_coordPartial_smooth _ (hC a j) k).continuous)
  obtain ⟨B1,hB1,hb1⟩ := real_compact_finite_coefficient_L2_bound hK A hA
  obtain ⟨B2,hB2,hb2⟩ := real_compact_finite_coefficient_L2_bound hK D hD
  refine ⟨2*(B1+B2),by positivity,fun U H hU hH ↦ ?_⟩
  dsimp only
  let S := fun x ↦ chi x*realWeakGradientCommutatorDerivative C U H k j i x+
    coordPartial chi x i*realWeakGradientCommutator C U k j x
  have heq : S = fun x ↦ (∑ a, A x a*H a i x)+(∑ a, D x a*U a x) := by
    funext x
    dsimp [S,realWeakGradientCommutator,realWeakGradientCommutatorDerivative]
    simp only [Finset.mul_sum,← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro a _
    dsimp [A,D]
    ring
  have h1 := hb1 (fun a ↦ H a i) (fun a ↦ hH a i)
  have h2 := hb2 U hU
  have hloc : MemLp S 2 (volume.restrict K) := by rw [heq]; exact h1.1.add h2.1
  have hz (x : Coord n) (hx : x ∉ K) : S x=0 := by
    have hdz : coordPartial chi x i=0 := image_eq_zero_of_notMem_tsupport
      (f := fun y ↦ coordPartial chi y i)
      (fun ht ↦ hx (hs (tsupport_fderiv_apply_subset ℝ (Pi.single i 1) ht)))
    dsimp [S]
    rw [image_eq_zero_of_notMem_tsupport (fun ht ↦ hx (hs ht)),hdz,zero_mul,zero_mul,add_zero]
  have hglob : MemLp S 2 volume := by
    have hind : K.indicator S=S := by
      funext x
      by_cases hx : x ∈ K
      · exact indicator_of_mem hx S
      · rw [indicator_of_notMem hx,hz x hx]
    rw [← hind]
    exact (memLp_indicator_iff_restrict hK.measurableSet).mpr hloc
  refine ⟨hglob,?_⟩
  change (∫ x, (S x)^2) ≤ _
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := K) (fun x hx ↦ by rw [hz x hx]; norm_num)]
  rw [heq]
  have ha := real_L2_add_square_bound (volume.restrict K) _ _ h1.1 h2.1
  have h0U : 0 ≤ ∑ a, ∫ x in K, (U a x)^2 := Finset.sum_nonneg (fun _ _ ↦ integral_nonneg (fun _ ↦ sq_nonneg _))
  have h0H : 0 ≤ ∑ a, ∫ x in K, (H a i x)^2 := Finset.sum_nonneg (fun _ _ ↦ integral_nonneg (fun _ ↦ sq_nonneg _))
  nlinarith [h1.2,h2.2,mul_nonneg hB1.le h0U,mul_nonneg hB2.le h0H]

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

theorem real_hessian_difference_cutoffs :
    ∃ eta chi : Jets.Coord → ℝ,
      ContDiff ℝ ∞ eta ∧ ContDiff ℝ ∞ chi ∧ HasCompactSupport eta ∧ HasCompactSupport chi ∧
      tsupport eta ⊆ interior (realCenteredCube 4 (3/8)) ∧
      tsupport chi ⊆ interior (realCenteredCube 4 (1/2)) ∧
      (∀ x, 0 ≤ eta x ∧ eta x ≤ 1) ∧ (∀ x, 0 ≤ chi x ∧ chi x ≤ 1) ∧
      (∀ x ∈ realCenteredCube 4 (1/4), eta =ᶠ[𝓝 x] (fun _ ↦ 1)) ∧
      ∀ (i : Fin 4) (h : ℝ), |h| ≤ 1/32 → ∀ x ∈ tsupport eta,
        x ∈ interior (realCenteredCube 4 (1/2)) ∧
        x+Pi.single i h ∈ interior (realCenteredCube 4 (1/2)) ∧
        chi =ᶠ[𝓝 x] (fun _ ↦ 1) ∧ chi =ᶠ[𝓝 (x+Pi.single i h)] (fun _ ↦ 1) := by
  obtain ⟨eta,he,hec,hes,heb,he1⟩ := real_cube_smooth_cutoff (1/4) (5/16) (by norm_num)
  obtain ⟨chi,hc,hcc,hcs,hcb,hc1⟩ := real_cube_smooth_cutoff (7/16) (15/32) (by norm_num)
  refine ⟨eta,chi,he,hc,hec,hcc,hes.trans (realCenteredCube_subset_interior (by norm_num)),
    hcs.trans (realCenteredCube_subset_interior (by norm_num)),heb,hcb,he1,?_⟩
  intro i h hh x hx
  have hxsmall := hes hx
  have hxouter : x ∈ realCenteredCube 4 (7/16) := realCenteredCube_mono (by norm_num) hxsmall
  have hxt : x+Pi.single i h ∈ realCenteredCube 4 (7/16) := by
    apply realCenteredCube_shift i (h := -h) (r := 5/16)
      (by simpa only [abs_neg] using (show |h| ≤ (7/16:ℝ)-5/16 by linarith))
    simpa only [Pi.single_neg,add_neg_cancel_right] using hxsmall
  exact ⟨realCenteredCube_subset_interior (by norm_num) hxouter,
    realCenteredCube_subset_interior (by norm_num) hxt,hc1 x hxouter,hc1 _ hxt⟩

end Yau

end

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
-- module Solutions.OAIQ237_NY.NodalSets_Spectral_SphereEigenForcingDerivativeBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open MeasureTheory Yau.Geometry Set
open scoped ContDiff
noncomputable section

theorem sphere_half_cube_gradient_bound (d : SphereEnergyData) (p : Base) :
    ∃ C > 0, ∀ (z : SphereEnergyHilbert d) (k : Fin 4),
      MemLp (sphereChartDerivativeMap d p k z) 2 (volume.restrict (Yau.realCenteredCube 4 (1/2))) ∧
      (∫ x in Yau.realCenteredCube 4 (1/2), ((sphereChartDerivativeMap d p k z) x)^2) ≤ C*‖z‖^2 := by
  obtain ⟨D,hD,hd⟩ := sphereChartDerivativeMap_bound d p
  refine ⟨D^2,sq_pos_of_pos hD,fun z k ↦ ?_⟩
  have hsub : Yau.realCenteredCube 4 (1/2) ⊆ realFinCube 4 := Yau.realCenteredCube_mono (by norm_num)
  have hmem := (Lp.memLp (sphereChartDerivativeMap d p k z)).mono_measure
    (Measure.restrict_mono hsub le_rfl)
  refine ⟨hmem,?_⟩
  have hmono := integral_mono_measure (Measure.restrict_mono hsub (le_refl volume))
    (Filter.Eventually.of_forall (fun x ↦ sq_nonneg ((sphereChartDerivativeMap d p k z) x)))
    (Lp.memLp (sphereChartDerivativeMap d p k z)).integrable_sq
  have hnorm : ‖sphereChartDerivativeMap d p k z‖^2 =
      ∫ x in realFinCube 4, ((sphereChartDerivativeMap d p k z) x)^2 := by
    simpa only [Lp.toLp_coeFn] using Yau.real_toLp_norm_sq _ (Lp.memLp (sphereChartDerivativeMap d p k z))
  rw [← hnorm] at hmono
  have hb := hd k z
  have hsq : ‖sphereChartDerivativeMap d p k z‖^2 ≤ (D*‖z‖)^2 :=
    pow_le_pow_left₀ (norm_nonneg _) hb 2
  simpa only [mul_pow] using hmono.trans hsq

theorem sphere_eigen_forcing_derivative_bound (d : SphereEnergyData) (p : Base)
    (hrho : ContDiff ℝ ∞ (fun x ↦ d.density (sphereChartCoordMap p x)))
    (mu : ℝ) (k : Fin 4) :
    ∃ C > 0, ∀ f : SphereWeightedL2 d,
      MemLp (sphereEigenForcingDerivative d p mu f k) 2
        (volume.restrict (Yau.realCenteredCube 4 (1/2))) ∧
      (∫ x in Yau.realCenteredCube 4 (1/2), (sphereEigenForcingDerivative d p mu f k x)^2) ≤
        C*(‖f‖^2+‖sphereWeakSolution d f‖^2) := by
  let Q := Yau.realCenteredCube 4 (1/2)
  have hQ : IsCompact Q := Yau.realCenteredCube_isCompact 4 (1/2)
  have ha : ContDiff ℝ ∞ (sphereEigenForcingCoefficient d p mu) :=
    contDiff_const.mul (roundCoordDensity_smooth.mul hrho)
  obtain ⟨A,hA,hAb⟩ := Yau.real_compact_multiplier_bound hQ _ ha.continuous
  obtain ⟨B,hB,hBb⟩ := Yau.real_compact_multiplier_bound hQ
    (fun x ↦ Yau.coordPartial (sphereEigenForcingCoefficient d p mu) x k)
    (Yau.real_coordPartial_smooth _ ha k).continuous
  obtain ⟨D,hD,hd⟩ := sphere_half_cube_gradient_bound d p
  obtain ⟨E,hE,he⟩ := sphereWeightedL2_compact_chart_bound d p hQ
  refine ⟨2*(A*D+B*E),by positivity,fun f ↦ ?_⟩
  have h1 := hAb (sphereChartDerivativeMap d p k (sphereWeakSolution d f)) (hd _ k).1
  have h2 := hBb (fun x ↦ (sphereL2Resolvent d f) (sphereChartCoordMap p x)) (he _).1
  refine ⟨h1.1.add h2.1,?_⟩
  have hadd := Yau.real_L2_add_square_bound (volume.restrict Q) _ _ h1.1 h2.1
  have hn : ‖sphereL2Resolvent d f‖ ≤ ‖f‖ := by
    have ht := (sphereL2Resolvent d).le_opNorm f
    exact ht.trans (by simpa using mul_le_mul_of_nonneg_right (sphereL2Resolvent_norm_le d) (norm_nonneg f))
  have hn2 : ‖sphereL2Resolvent d f‖^2 ≤ ‖f‖^2 := pow_le_pow_left₀ (norm_nonneg _) hn 2
  have h1b := h1.2.trans (mul_le_mul_of_nonneg_left (hd _ k).2 hA.le)
  have h2b := h2.2.trans (mul_le_mul_of_nonneg_left ((he _).2.trans
    (mul_le_mul_of_nonneg_left hn2 hE.le)) hB.le)
  change (∫ x in Q, (sphereEigenForcingDerivative d p mu f k x)^2) ≤ _
  dsimp only [sphereEigenForcingDerivative]
  nlinarith [h1b,h2b,mul_nonneg (mul_nonneg hA.le hD.le) (sq_nonneg ‖f‖),
    mul_nonneg (mul_nonneg hB.le hE.le) (sq_nonneg ‖sphereWeakSolution d f‖)]

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Spectral_SphereEigenHessianDifferenceBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open MeasureTheory Yau.Geometry Set
open scoped ContDiff
noncomputable section

theorem sphere_eigen_hessian_difference_bound (d : SphereEnergyData) (p : Base)
    (hrho : ContDiff ℝ ∞ (fun x ↦ d.density (sphereChartCoordMap p x)))
    (mu : ℝ) (hmu : mu ≠ 0) :
    ∃ C1 > 0, ∃ C > 0, ∀ (f : SphereWeightedL2 d), sphereL2Resolvent d f=mu • f →
      ∃ H : Fin 4 → Fin 4 → Lp ℝ 2 (volume.restrict (Yau.realCenteredCube 4 (1/2))),
        (∑ a, ∑ j, ‖H a j‖^2) ≤ C1*(‖f‖^2+‖sphereWeakSolution d f‖^2) ∧
        (∀ a j psi, ContDiff ℝ ∞ psi → HasCompactSupport psi →
          tsupport psi ⊆ Yau.realCenteredCube 4 (1/2) →
          (∫ x in Yau.realCenteredCube 4 (1/2),
            (sphereChartDerivativeMap d p a (sphereWeakSolution d f)) x*Yau.coordPartial psi x j) =
            -(∫ x in Yau.realCenteredCube 4 (1/2), H a j x*psi x)) ∧
        ∀ (k i : Fin 4) (h : ℝ), |h| ≤ 1/32 →
          (∀ a, MemLp (Yau.realDifferenceQuotient i h (H k a)) 2
            (volume.restrict (Yau.realCenteredCube 4 (1/4)))) ∧
          (∑ a, ∫ x in Yau.realCenteredCube 4 (1/4), (Yau.realDifferenceQuotient i h (H k a) x)^2) ≤
            C*(‖f‖^2+‖sphereWeakSolution d f‖^2) := by
  obtain ⟨C1,hC1,m,hm,K,hK,henergy⟩ := sphere_eigen_hessian_localized_energy d p hrho
  obtain ⟨eta,chi,he,hchi,hec,hchic,hes,hchis,heb,hchib,he1,hend⟩ := Yau.real_hessian_difference_cutoffs
  let Q := Yau.realCenteredCube 4 (1/2)
  let Q0 := Yau.realCenteredCube 4 (1/4)
  have hQ : IsCompact Q := Yau.realCenteredCube_isCompact 4 (1/2)
  have hQ0 : IsCompact Q0 := Yau.realCenteredCube_isCompact 4 (1/4)
  have hcs : tsupport chi ⊆ Q := hchis.trans interior_subset
  have hetab (x : Yau.Jets.Coord) : |eta x| ≤ 1 := by rw [abs_of_nonneg (heb x).1]; exact (heb x).2
  have hends (i : Fin 4) (h : ℝ) (hh : |h| ≤ 1/32) (x : Yau.Jets.Coord) (hx : x ∈ tsupport eta) :
      x ∈ Q ∧ x+Pi.single i h ∈ Q ∧ chi x=1 ∧ chi (x+Pi.single i h)=1 := by
    have ht := hend i h hh x hx
    exact ⟨interior_subset ht.1,interior_subset ht.2.1,ht.2.2.1.eq_of_nhds,ht.2.2.2.eq_of_nhds⟩
  obtain ⟨D,hD,hUb⟩ := sphere_half_cube_gradient_bound d p
  obtain ⟨CW,hCW,hWb⟩ := Yau.real_indicator_weighted_bound hQ eta he.continuous
  choose CF hCF hFb using fun k ↦ sphere_eigen_forcing_derivative_bound d p hrho mu k
  obtain ⟨F0,hF0,hFmax⟩ := Yau.real_finite_positive_majorant CF
  choose CG hCG hGb using fun k j i ↦ Yau.real_localized_commutator_derivative_bound hQ
    (sphereChartPrincipalDensity d p) (sphereChartPrincipalDensity_smooth d p) chi hchi hcs k j i
  obtain ⟨G0,hG0,hGmax⟩ := Yau.real_finite_positive_majorant
    (fun t : Fin 4 × Fin 4 × Fin 4 ↦ CG t.1 t.2.1 t.2.2)
  choose CR hCR hRb using fun i a ↦ Yau.real_weighted_local_difference_bound hQ
    (fun x ↦ Yau.coordPartial eta x a) chi (Yau.real_coordPartial_smooth eta he a).continuous
    (hec.fderiv_apply ℝ (Pi.single a 1)) hchi hcs i
  obtain ⟨R0,hR0,hRmax⟩ := Yau.real_finite_positive_majorant (fun t : Fin 4 × Fin 4 ↦ CR t.1 t.2)
  let C := (4/m)*((16/m)*(F0+4*G0*(4*D+C1))+K*CW*C1+(K+m)*4*R0*(D+C1))
  refine ⟨C1,hC1,C,by dsimp [C] <;> positivity,fun f heigen ↦ ?_⟩
  obtain ⟨H,hbound,hweak,hweighted⟩ := henergy mu hmu f heigen
  refine ⟨H,hbound,hweak,fun k i h hh ↦ ?_⟩
  let E := ‖f‖^2+‖sphereWeakSolution d f‖^2
  have hE : 0 ≤ E := by dsimp [E] <;> positivity
  let U := fun a ↦ (sphereChartDerivativeMap d p a (sphereWeakSolution d f) : Yau.Jets.Coord → ℝ)
  let V := fun a ↦ Q.indicator (H k a)
  let q := Yau.realDifferenceQuotient i h (Q.indicator (U k))
  let T := fun a x ↦ eta x*Yau.realDifferenceQuotient i h (V a) x
  let W := fun a x ↦ eta x*V a x
  let R := fun a x ↦ Yau.coordPartial eta x a*q x
  let G := Yau.realWeakGradientCommutator (sphereChartPrincipalDensity d p) U k
  let DG := Yau.realWeakGradientCommutatorDerivative (sphereChartPrincipalDensity d p) U (fun a j ↦ H a j) k
  let F := Q.indicator (sphereEigenForcingDerivative d p mu f k)
  have hwt := hweighted k eta chi he hec hetab hes hchi hcs i h hh (hends i h hh)
  have hUn (a : Fin 4) : (∫ x in Q, (U a x)^2) ≤ D*E :=
    (hUb _ a).2.trans (mul_le_mul_of_nonneg_left (by dsimp [E] <;> nlinarith [sq_nonneg ‖f‖]) hD.le)
  have hUsum : (∑ a, ∫ x in Q, (U a x)^2) ≤ 4*D*E := by
    have ht := Finset.sum_le_sum (s := Finset.univ) (fun a _ ↦ hUn a)
    simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_ofNat,mul_assoc] using ht
  have hHnorm (a j : Fin 4) : (∫ x in Q, (H a j x)^2)=‖H a j‖^2 := by
    symm
    simpa only [Lp.toLp_coeFn] using Yau.real_toLp_norm_sq _ (Lp.memLp (H a j))
  have hHrow (a : Fin 4) : (∑ j, ∫ x in Q, (H a j x)^2) ≤ C1*E := by
    simp_rw [hHnorm]
    exact (Finset.single_le_sum (f := fun b ↦ ∑ j, ‖H b j‖^2)
      (fun b _ ↦ Finset.sum_nonneg (fun j _ ↦ sq_nonneg _)) (Finset.mem_univ a)).trans hbound
  have hHcol (j : Fin 4) : (∑ a, ∫ x in Q, (H a j x)^2) ≤ C1*E := by
    simp_rw [hHnorm]
    exact (Finset.sum_le_sum (fun a _ ↦ Finset.single_le_sum (f := fun l ↦ ‖H a l‖^2)
      (fun l _ ↦ sq_nonneg _) (Finset.mem_univ j))).trans hbound
  have hHone (a j : Fin 4) : (∫ x in Q, (H a j x)^2) ≤ C1*E :=
    (Finset.single_le_sum (f := fun l ↦ ∫ x in Q, (H a l x)^2)
      (fun l _ ↦ integral_nonneg (fun x ↦ sq_nonneg _)) (Finset.mem_univ j)).trans (hHrow a)
  have hWsum : (∑ a, ∫ x, (W a x)^2) ≤ CW*C1*E := by
    have ht := Finset.sum_le_sum (s := Finset.univ) (fun a _ ↦ (hWb (H k a) (Lp.memLp _)).2)
    simp only [← Finset.mul_sum] at ht
    exact ht.trans (by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left (hHrow k) hCW.le)
  have hRone (a : Fin 4) : (∫ x, (R a x)^2) ≤ R0*(D+C1)*E := by
    have ht := (hRb i a (U k) (H k i) (hUb _ k).1 (Lp.memLp _) (hweak k i) h
      (fun x hx ↦ hends i h hh x (tsupport_fderiv_apply_subset ℝ (Pi.single a 1) hx))).2
    have hb := (add_le_add (hUn k) (hHone k i))
    have hc := (mul_le_mul_of_nonneg_left hb (hCR i a).le)
    have hmax := mul_le_mul_of_nonneg_right (hRmax (i,a))
      (show 0 ≤ (D+C1)*E by positivity)
    have heq : D*E+C1*E=(D+C1)*E := by ring
    rw [heq] at hc
    exact ht.trans (hc.trans (by simpa only [mul_assoc] using hmax))
  have hRsum : (∑ a, ∫ x, (R a x)^2) ≤ 4*R0*(D+C1)*E := by
    have ht := Finset.sum_le_sum (s := Finset.univ) (fun a _ ↦ hRone a)
    simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_ofNat,mul_assoc] using ht
  have hGone (j : Fin 4) : (∫ x, (chi x*DG j i x+Yau.coordPartial chi x i*G j x)^2) ≤
      G0*(4*D+C1)*E := by
    have ht := (hGb k j i U (fun a l ↦ H a l) (fun a ↦ (hUb _ a).1) (fun a l ↦ Lp.memLp _)).2
    have hb := mul_le_mul_of_nonneg_left (add_le_add hUsum (hHcol i)) (hCG k j i).le
    have heq : 4*D*E+C1*E=(4*D+C1)*E := by ring
    rw [heq] at hb
    have hmax := mul_le_mul_of_nonneg_right (hGmax (k,j,i))
      (show 0 ≤ (4*D+C1)*E by positivity)
    exact ht.trans (hb.trans (by simpa only [mul_assoc] using hmax))
  have hGsum : (∑ j, ∫ x, (chi x*DG j i x+Yau.coordPartial chi x i*G j x)^2) ≤
      4*G0*(4*D+C1)*E := by
    have ht := Finset.sum_le_sum (s := Finset.univ) (fun j _ ↦ hGone j)
    simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_ofNat,mul_assoc] using ht
  have hFint : (∫ x, (F x)^2) ≤ F0*E := by
    have hind : (fun x ↦ (F x)^2)=Q.indicator (fun x ↦ (sphereEigenForcingDerivative d p mu f k x)^2) := by
      funext x
      by_cases hx : x ∈ Q
      · simp only [F,indicator_of_mem hx]
      · simp only [F,indicator_of_notMem hx,zero_pow (by decide : (2:ℕ)≠0)]
    change (∫ x, (fun y ↦ (F y)^2) x) ≤ _
    rw [hind,integral_indicator hQ.measurableSet]
    exact (hFb k f).2.trans (mul_le_mul_of_nonneg_right (hFmax k) hE)
  have hglobal : (∑ a, ∫ x, (T a x)^2) ≤ C*E := by
    have ht := add_le_add (add_le_add
      (mul_le_mul_of_nonneg_left (add_le_add hFint hGsum) (show 0 ≤ 16/m by positivity))
      (mul_le_mul_of_nonneg_left hWsum hK.le))
      (mul_le_mul_of_nonneg_left hRsum (add_nonneg hK.le hm.le))
    have hb := hwt.2.trans (mul_le_mul_of_nonneg_left ht (show 0 ≤ 4/m by positivity))
    have hcform : (4/m)*((16/m)*(F0*E+4*G0*(4*D+C1)*E)+
        K*(CW*C1*E)+(K+m)*(4*R0*(D+C1)*E))=C*E := by
      dsimp [C]
      ring
    exact hb.trans_eq hcform
  have hident (a : Fin 4) (x : Yau.Jets.Coord) (hx : x ∈ Q0) :
      Yau.realDifferenceQuotient i h (H k a) x=T a x := by
    have hxQ : x ∈ Q := Yau.realCenteredCube_mono (by norm_num) hx
    have htQ : x+Pi.single i h ∈ Q := by
      apply Yau.realCenteredCube_shift i (h := -h) (r := 1/4)
        (by simpa only [abs_neg] using (show |h| ≤ (1/2:ℝ)-1/4 by linarith))
      simpa only [Pi.single_neg,add_neg_cancel_right] using hx
    dsimp [T,V]
    rw [(he1 x hx).eq_of_nhds,one_mul]
    simp only [Yau.realDifferenceQuotient,indicator_of_mem hxQ,indicator_of_mem htQ]
  refine ⟨fun a ↦ ?_,?_⟩
  · apply ((hwt.1 a).1.restrict Q0).ae_eq
    filter_upwards [ae_restrict_mem hQ0.measurableSet] with x hx
    exact (hident a x hx).symm
  · apply le_trans (Finset.sum_le_sum (fun a _ ↦ ?_)) hglobal
    have hEq : (∫ x in Q0, (Yau.realDifferenceQuotient i h (H k a) x)^2)=
        ∫ x in Q0, (T a x)^2 := by
      apply setIntegral_congr_fun hQ0.measurableSet
      intro x hx
      change (Yau.realDifferenceQuotient i h (H k a) x)^2=(T a x)^2
      rw [hident a x hx]
    rw [hEq]
    exact setIntegral_le_integral (hwt.1 a).1.integrable_sq
      (Filter.Eventually.of_forall (fun x ↦ sq_nonneg _))

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Spectral_SphereEigenInteriorH3
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open MeasureTheory Yau.Geometry Set
open scoped ContDiff
noncomputable section

theorem sphere_eigen_interior_third_weak_derivatives (d : SphereEnergyData) (p : Base)
    (hrho : ContDiff ℝ ∞ (fun x ↦ d.density (sphereChartCoordMap p x)))
    (mu : ℝ) (hmu : mu ≠ 0) :
    ∃ C2 > 0, ∃ C3 > 0, ∀ (f : SphereWeightedL2 d), sphereL2Resolvent d f=mu • f →
      ∃ H : Fin 4 → Fin 4 → Lp ℝ 2 (volume.restrict (Yau.realCenteredCube 4 (1/2))),
      ∃ J : Fin 4 → Fin 4 → Fin 4 → Lp ℝ 2 (volume.restrict (Yau.realCenteredCube 4 (1/4))),
        (∑ a, ∑ k, ‖H a k‖^2) ≤ C2*(‖f‖^2+‖sphereWeakSolution d f‖^2) ∧
        (∀ a k psi, ContDiff ℝ ∞ psi → HasCompactSupport psi →
          tsupport psi ⊆ Yau.realCenteredCube 4 (1/2) →
          (∫ x in Yau.realCenteredCube 4 (1/2),
            (sphereChartDerivativeMap d p a (sphereWeakSolution d f)) x*Yau.coordPartial psi x k) =
            -(∫ x in Yau.realCenteredCube 4 (1/2), H a k x*psi x)) ∧
        (∑ a, ∑ k, ∑ i, ‖J a k i‖^2) ≤ C3*(‖f‖^2+‖sphereWeakSolution d f‖^2) ∧
        ∀ a k i psi, ContDiff ℝ ∞ psi → HasCompactSupport psi →
          tsupport psi ⊆ Yau.realCenteredCube 4 (1/4) →
          IntegrableOn (fun x ↦ H a k x*Yau.coordPartial psi x i) (Yau.realCenteredCube 4 (1/4)) ∧
          IntegrableOn (fun x ↦ J a k i x*psi x) (Yau.realCenteredCube 4 (1/4)) ∧
          (∫ x in Yau.realCenteredCube 4 (1/4), H a k x*Yau.coordPartial psi x i) =
            -(∫ x in Yau.realCenteredCube 4 (1/4), J a k i x*psi x) := by
  obtain ⟨C2,hC2,C,hC,hall⟩ := sphere_eigen_hessian_difference_bound d p hrho mu hmu
  refine ⟨C2,hC2,64*C,by positivity,fun f heigen ↦ ?_⟩
  obtain ⟨H,hbound,hweak,hdiff⟩ := hall f heigen
  let E := ‖f‖^2+‖sphereWeakSolution d f‖^2
  have hE : 0 ≤ E := by dsimp [E] <;> positivity
  have hder (a k i : Fin 4) :
      ∃ J : Lp ℝ 2 (volume.restrict (Yau.realCenteredCube 4 (1/4))), ‖J‖^2 ≤ C*E ∧
        ∀ psi : Yau.Jets.Coord → ℝ, ContDiff ℝ ∞ psi → HasCompactSupport psi →
          tsupport psi ⊆ Yau.realCenteredCube 4 (1/4) →
          IntegrableOn (fun x ↦ H a k x*Yau.coordPartial psi x i) (Yau.realCenteredCube 4 (1/4)) ∧
          IntegrableOn (fun x ↦ J x*psi x) (Yau.realCenteredCube 4 (1/4)) ∧
          (∫ x in Yau.realCenteredCube 4 (1/4), H a k x*Yau.coordPartial psi x i) =
            -(∫ x in Yau.realCenteredCube 4 (1/4), J x*psi x) := by
    apply Yau.real_nested_weak_derivative_of_difference_bound (1/2) (1/4) (1/32)
      (by norm_num) (by norm_num) (by norm_num) (H a k) (Lp.memLp _) i (C*E) (mul_nonneg hC.le hE)
      (fun h hh ↦ (hdiff a i h hh).1 k)
    intro h hh
    exact (Finset.single_le_sum (f := fun l ↦ ∫ x in Yau.realCenteredCube 4 (1/4),
      (Yau.realDifferenceQuotient i h (H a l) x)^2)
      (fun l _ ↦ integral_nonneg (fun x ↦ sq_nonneg _)) (Finset.mem_univ k)).trans (hdiff a i h hh).2
  choose J hJ hpair using hder
  refine ⟨H,J,hbound,hweak,?_,hpair⟩
  have ht := Finset.sum_le_sum (s := Finset.univ) (fun a _ ↦
    Finset.sum_le_sum (s := Finset.univ) (fun k _ ↦
      Finset.sum_le_sum (s := Finset.univ) (fun i _ ↦ hJ a k i)))
  norm_num only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_ofNat] at ht
  have hscale : 4*(4*(4*(C*E)))=(64*C)*E := by ring
  exact ht.trans_eq hscale

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Spectral_SphereEigenInteriorH4
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open MeasureTheory Yau.Geometry Set
open scoped ContDiff
noncomputable section

theorem sphere_eigen_interior_fourth_weak_derivatives_oai (d : SphereEnergyData) (p : Base)
    (hrho : ContDiff ℝ ∞ (fun x ↦ d.density (sphereChartCoordMap p x)))
    (mu : ℝ) (hmu : mu ≠ 0) :
    ∃ C2 > 0, ∃ C3 > 0, ∃ C4 > 0, ∀ (f : SphereWeightedL2 d), sphereL2Resolvent d f=mu • f →
      ∃ H : Fin 4 → Fin 4 → Lp ℝ 2 (volume.restrict (Yau.realCenteredCube 4 (1/2))),
      ∃ J : Fin 4 → Fin 4 → Fin 4 → Lp ℝ 2 (volume.restrict (Yau.realCenteredCube 4 (1/4))),
      ∃ L : Fin 4 → Fin 4 → Fin 4 → Fin 4 → Lp ℝ 2 (volume.restrict (Yau.realCenteredCube 4 (1/8))),
        (∑ a, ∑ k, ‖H a k‖^2) ≤ C2*(‖f‖^2+‖sphereWeakSolution d f‖^2) ∧
        (∀ a k psi, ContDiff ℝ ∞ psi → HasCompactSupport psi →
          tsupport psi ⊆ Yau.realCenteredCube 4 (1/2) →
          (∫ x in Yau.realCenteredCube 4 (1/2),
            (sphereChartDerivativeMap d p a (sphereWeakSolution d f)) x*Yau.coordPartial psi x k) =
            -(∫ x in Yau.realCenteredCube 4 (1/2), H a k x*psi x)) ∧
        (∑ a, ∑ k, ∑ i, ‖J a k i‖^2) ≤ C3*(‖f‖^2+‖sphereWeakSolution d f‖^2) ∧
        (∀ a k i psi, ContDiff ℝ ∞ psi → HasCompactSupport psi →
          tsupport psi ⊆ Yau.realCenteredCube 4 (1/4) →
          IntegrableOn (fun x ↦ H a k x*Yau.coordPartial psi x i) (Yau.realCenteredCube 4 (1/4)) ∧
          IntegrableOn (fun x ↦ J a k i x*psi x) (Yau.realCenteredCube 4 (1/4)) ∧
          (∫ x in Yau.realCenteredCube 4 (1/4), H a k x*Yau.coordPartial psi x i) =
            -(∫ x in Yau.realCenteredCube 4 (1/4), J a k i x*psi x)) ∧
        (∑ a, ∑ k, ∑ l, ∑ i, ‖L a k l i‖^2) ≤ C4*(‖f‖^2+‖sphereWeakSolution d f‖^2) ∧
        ∀ a k l i psi, ContDiff ℝ ∞ psi → HasCompactSupport psi →
          tsupport psi ⊆ Yau.realCenteredCube 4 (1/8) →
          IntegrableOn (fun x ↦ J a k l x*Yau.coordPartial psi x i) (Yau.realCenteredCube 4 (1/8)) ∧
          IntegrableOn (fun x ↦ L a k l i x*psi x) (Yau.realCenteredCube 4 (1/8)) ∧
          (∫ x in Yau.realCenteredCube 4 (1/8), J a k l x*Yau.coordPartial psi x i) =
            -(∫ x in Yau.realCenteredCube 4 (1/8), L a k l i x*psi x) := by
  obtain ⟨C2,hC2,C3,hC3,hall⟩ := sphere_eigen_interior_third_weak_derivatives d p hrho mu hmu
  obtain ⟨C,hC,hbound⟩ := sphere_same_third_difference_bound d p hrho mu hmu C2 C3 hC2.le hC3.le
  refine ⟨C2,hC2,C3,hC3,256*C,by positivity,fun f heigen ↦ ?_⟩
  obtain ⟨H,J,hH,hsecond,hJ,hthird⟩ := hall f heigen
  have hdiff := hbound f heigen H J hsecond
    (fun a k l psi hp hc hs ↦ (hthird a k l psi hp hc hs).2.2) hH hJ
  let E := ‖f‖^2+‖sphereWeakSolution d f‖^2
  have hE : 0 ≤ E := by dsimp [E] <;> positivity
  have hder (a k l i : Fin 4) :
      ∃ L : Lp ℝ 2 (volume.restrict (Yau.realCenteredCube 4 (1/8))), ‖L‖^2 ≤ C*E ∧
        ∀ psi : Yau.Jets.Coord → ℝ, ContDiff ℝ ∞ psi → HasCompactSupport psi →
          tsupport psi ⊆ Yau.realCenteredCube 4 (1/8) →
          IntegrableOn (fun x ↦ J a k l x*Yau.coordPartial psi x i) (Yau.realCenteredCube 4 (1/8)) ∧
          IntegrableOn (fun x ↦ L x*psi x) (Yau.realCenteredCube 4 (1/8)) ∧
          (∫ x in Yau.realCenteredCube 4 (1/8), J a k l x*Yau.coordPartial psi x i) =
            -(∫ x in Yau.realCenteredCube 4 (1/8), L x*psi x) := by
    apply Yau.real_nested_weak_derivative_of_difference_bound (1/4) (1/8) (1/64)
      (by norm_num) (by norm_num) (by norm_num) (J a k l) (Lp.memLp _) i (C*E) (mul_nonneg hC.le hE)
      (fun h hh ↦ (hdiff a k i h hh).1 l)
    intro h hh
    exact (Finset.single_le_sum (f := fun b ↦ ∫ x in Yau.realCenteredCube 4 (1/8),
      (Yau.realDifferenceQuotient i h (J a k b) x)^2)
      (fun b _ ↦ integral_nonneg (fun x ↦ sq_nonneg _)) (Finset.mem_univ l)).trans (hdiff a k i h hh).2
  choose L hL hpair using hder
  refine ⟨H,J,L,hH,hsecond,hJ,hthird,?_,hpair⟩
  have ht := Finset.sum_le_sum (s := Finset.univ) (fun a _ ↦
    Finset.sum_le_sum (s := Finset.univ) (fun k _ ↦
      Finset.sum_le_sum (s := Finset.univ) (fun l _ ↦
        Finset.sum_le_sum (s := Finset.univ) (fun i _ ↦ hL a k l i))))
  norm_num only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_ofNat] at ht
  exact ht.trans_eq (by ring)

end
end Yau.Target

end OAI
end

theorem solution : type_of% @OAI.Yau.Target.sphere_eigen_interior_fourth_weak_derivatives_oai := @OAI.Yau.Target.sphere_eigen_interior_fourth_weak_derivatives_oai
