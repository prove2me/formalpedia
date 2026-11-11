-- Prove2me | solution 1 for OAI.Yau.Target.sphere_resolvent_interior_gradient_difference_bound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T00:34:59.41632+00:00
-- url     : https://prove2.me/submissions/3bcd7641-d243-4dc0-af1b-6c8464c15024

import Mathlib
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
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
import Theorems.Thm_OAI_Yau_Target_sphere_resolvent_H1_difference_test_literal

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

local instance sphereEnergyL2MapMeasurable_ra06f3c_1 : MeasurableSpace Base := borel Base
local instance sphereEnergyL2MapBorel_ra06f3c_1 : BorelSpace Base := ⟨rfl⟩
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

local instance sphereCompactChartTestingMeasurable_ra06f3c_1 : MeasurableSpace Base := borel Base
local instance sphereCompactChartTestingBorel_ra06f3c_1 : BorelSpace Base := ⟨rfl⟩
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

local instance sphereChartWeakDerivativeMeasurable_ra06f3c_1 : MeasurableSpace Base := borel Base
local instance sphereChartWeakDerivativeBorel_ra06f3c_1 : BorelSpace Base := ⟨rfl⟩
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
-- module Solutions.OAIQ237_NY.NodalSets_Charts_SphereChartCutoffWeak
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open MeasureTheory Yau.Geometry Set
open scoped ContDiff
noncomputable section

local instance sphereChartCutoffWeakMeasurable_ra06f3c_1 : MeasurableSpace Base := borel Base
local instance sphereChartCutoffWeakBorel_ra06f3c_1 : BorelSpace Base := ⟨rfl⟩
theorem sphere_chart_cutoff_weak (d : SphereEnergyData) (p : Base) (z : SphereEnergyHilbert d)
    (eta : Yau.Jets.Coord → ℝ) (he : ContDiff ℝ ∞ eta)
    (hs : tsupport eta ⊆ realFinCube 4) :
    let v := fun x ↦ eta x*(sphereEnergyL2Map d z) (sphereChartCoordMap p x)
    let G := fun i x ↦ eta x*(sphereChartDerivativeMap d p i z) x +
      Yau.coordPartial eta x i*(sphereEnergyL2Map d z) (sphereChartCoordMap p x)
    MemLp v 2 volume ∧ ∀ i : Fin 4, MemLp (G i) 2 volume ∧
      ∀ phi : Yau.Jets.Coord → ℝ, ContDiff ℝ ∞ phi → HasCompactSupport phi →
        Integrable (fun x ↦ v x*Yau.coordPartial phi x i) ∧ Integrable (fun x ↦ G i x*phi x) ∧
        (∫ x, v x*Yau.coordPartial phi x i) = -(∫ x, G i x*phi x) := by
  dsimp only
  let w := fun x ↦ (sphereEnergyL2Map d z) (sphereChartCoordMap p x)
  have hw : MemLp w 2 (volume.restrict (realFinCube 4)) := by
    obtain ⟨_,_,hb⟩ := sphereWeightedL2_compact_chart_bound d p (realFinCube_isCompact 4)
    exact (hb (sphereEnergyL2Map d z)).1
  have hval := Yau.real_compact_localL2_product (realFinCube_isCompact 4) eta w he.continuous hs hw
  refine ⟨hval,?_⟩
  intro i
  have hpart : tsupport (fun x ↦ Yau.coordPartial eta x i) ⊆ realFinCube 4 :=
    (tsupport_fderiv_apply_subset ℝ (Pi.single i 1)).trans hs
  have h1 := Yau.real_compact_localL2_product (realFinCube_isCompact 4) eta
    (sphereChartDerivativeMap d p i z) he.continuous hs (Lp.memLp _)
  have h2 := Yau.real_compact_localL2_product (realFinCube_isCompact 4)
    (fun x ↦ Yau.coordPartial eta x i) w (Yau.real_coordPartial_smooth eta he i).continuous hpart hw
  refine ⟨h1.add h2,?_⟩
  intro phi hp hc
  have hphi := Yau.real_compact_continuous_memLp phi hp.continuous hc
  have hi1 : Integrable (fun x ↦ eta x*(sphereChartDerivativeMap d p i z) x*phi x) := h1.integrable_mul hphi
  have hi2 : Integrable (fun x ↦ Yau.coordPartial eta x i*w x*phi x) := h2.integrable_mul hphi
  have hi3 : Integrable (fun x ↦ eta x*w x*Yau.coordPartial phi x i) := hval.integrable_mul
    (Yau.real_compact_continuous_memLp _ (Yau.real_coordPartial_smooth phi hp i).continuous
      (hc.fderiv_apply ℝ (Pi.single i 1)))
  have hweak := (sphere_chart_weak_derivative d p i z (fun x ↦ eta x*phi x) (he.mul hp)
    hc.mul_left (tsupport_mul_subset_left.trans hs)).2.2
  have he1 : (fun x ↦ (sphereChartDerivativeMap d p i z) x*(eta x*phi x)) =
      fun x ↦ eta x*(sphereChartDerivativeMap d p i z) x*phi x := by funext x; ring
  have he2 : (fun x ↦ w x*Yau.coordPartial (fun y ↦ eta y*phi y) x i) =
      fun x ↦ Yau.coordPartial eta x i*w x*phi x+eta x*w x*Yau.coordPartial phi x i := by
    funext x
    rw [Yau.real_coordPartial_mul eta phi he hp]
    ring
  change (∫ x in realFinCube 4, (sphereChartDerivativeMap d p i z) x*(eta x*phi x)) =
    -(∫ x in realFinCube 4, w x*Yau.coordPartial (fun y ↦ eta y*phi y) x i) at hweak
  rw [he1,he2,integral_add hi2.integrableOn hi3.integrableOn] at hweak
  have hz (x : Yau.Jets.Coord) (hx : x ∉ realFinCube 4) : eta x=0 :=
    image_eq_zero_of_notMem_tsupport (fun h ↦ hx (hs h))
  have hdz (x : Yau.Jets.Coord) (hx : x ∉ realFinCube 4) : Yau.coordPartial eta x i=0 :=
    image_eq_zero_of_notMem_tsupport (f := fun y ↦ Yau.coordPartial eta y i) (fun h ↦ hx (hpart h))
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx ↦ by rw [hz x hx,zero_mul,zero_mul]),
    setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx ↦ by rw [hdz x hx,zero_mul,zero_mul]),
    setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx ↦ by rw [hz x hx,zero_mul,zero_mul])] at hweak
  have heG : (fun x ↦ (eta x*(sphereChartDerivativeMap d p i z) x+Yau.coordPartial eta x i*w x)*phi x) =
      fun x ↦ eta x*(sphereChartDerivativeMap d p i z) x*phi x+Yau.coordPartial eta x i*w x*phi x := by
    funext x
    ring
  refine ⟨hi3,by rw [heG]; exact hi1.add hi2,?_⟩
  change (∫ x, eta x*w x*Yau.coordPartial phi x i) = _
  rw [heG,integral_add hi1 hi2]
  linarith only [hweak]

end
end Yau.Target

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

local instance sphereChartValueMapMeasurable_ra06f3c_1 : MeasurableSpace Base := borel Base
local instance sphereChartValueMapBorel_ra06f3c_1 : BorelSpace Base := ⟨rfl⟩
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
-- module Solutions.OAIQ237_NY.NodalSets_Charts_SphereChartStrongApproximation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Filter Set
open scoped Topology
noncomputable section

theorem sphere_chart_strong_approximation (d : SphereEnergyData) (z : SphereEnergyHilbert d) :
    ∃ u : ℕ → SphereEnergySmooth d,
      Tendsto (fun n ↦ sphereEnergyToCompletion d (u n)) atTop (𝓝 z) ∧
      ∀ p : Base,
        Tendsto (fun n ↦ sphereChartValueMap d p (sphereEnergyL2Linear d (u n))) atTop
          (𝓝 (sphereChartValueMap d p (sphereEnergyL2Map d z))) ∧
        ∀ i : Fin 4, Tendsto (fun n ↦ sphereChartDerivativeLinear d p i (u n)) atTop
          (𝓝 (sphereChartDerivativeMap d p i z)) := by
  obtain ⟨v,hv,hlim⟩ := mem_closure_iff_seq_limit.mp ((sphereEnergyToCompletion_dense d) z)
  choose u hu using hv
  have hlim' : Tendsto (fun n ↦ sphereEnergyToCompletion d (u n)) atTop (𝓝 z) := by
    simpa only [hu] using hlim
  refine ⟨u,hlim',?_⟩
  intro p
  constructor
  · have h := (sphereChartValueMap d p).continuous.continuousAt.tendsto.comp
      ((sphereEnergyL2Map d).continuous.continuousAt.tendsto.comp hlim')
    simpa only [Function.comp_def,sphereEnergyL2Map_coe] using h
  · intro i
    have h := (sphereChartDerivativeMap d p i).continuous.continuousAt.tendsto.comp hlim'
    simpa only [Function.comp_def,sphereChartDerivativeMap_coe] using h

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

local instance sphereChartCutoffApproxMeasurable_ra06f3c_1 : MeasurableSpace Base := borel Base
local instance sphereChartCutoffApproxBorel_ra06f3c_1 : BorelSpace Base := ⟨rfl⟩
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

theorem sphere_chart_cutoff_strong_approximation (d : SphereEnergyData)
    (z : SphereEnergyHilbert d) :
    ∃ u : ℕ → SphereEnergySmooth d,
      Tendsto (fun n ↦ sphereEnergyToCompletion d (u n)) atTop (𝓝 z) ∧
      ∀ (p : Base) (eta : Yau.Jets.Coord → ℝ) (he : ContDiff ℝ ∞ eta)
        (hs : tsupport eta ⊆ realFinCube 4),
        Tendsto (fun n ↦ sphereCutoffValueMap d p eta he hs (sphereEnergyToCompletion d (u n)))
          atTop (𝓝 (sphereCutoffValueMap d p eta he hs z)) ∧
        ∀ i : Fin 4, Tendsto
          (fun n ↦ sphereCutoffDerivativeMap d p eta he hs i (sphereEnergyToCompletion d (u n)))
          atTop (𝓝 (sphereCutoffDerivativeMap d p eta he hs i z)) := by
  obtain ⟨u,hu,_⟩ := sphere_chart_strong_approximation d z
  refine ⟨u,hu,fun p eta he hs ↦ ⟨?_,fun i ↦ ?_⟩⟩
  · exact (sphereCutoffValueMap d p eta he hs).continuous.continuousAt.tendsto.comp hu
  · exact (sphereCutoffDerivativeMap d p eta he hs i).continuous.continuousAt.tendsto.comp hu

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

theorem real_L2_norm_sq_rep {n : ℕ} (u : RealEuclideanL2 n)
    (v : (Fin n → ℝ) → ℝ) (he : (u : (Fin n → ℝ) → ℝ) =ᵐ[volume] v) :
    ‖u‖^2 = ∫ x, (v x)^2 := by
  have h := real_toLp_norm_sq _ (Lp.memLp u)
  simp only [Lp.toLp_coeFn] at h
  rw [h]
  exact integral_congr_ae (he.fun_comp (fun t : ℝ ↦ t^2))

theorem real_difference_norm_bound_limit {n : ℕ} (i : Fin n) (h : ℝ)
    (u g : RealEuclideanL2 n) (v w : ℕ → RealEuclideanL2 n)
    (hv : Tendsto v atTop (𝓝 u)) (hw : Tendsto w atTop (𝓝 g))
    (hb : ∀ k, ‖realL2DifferenceMap i h (v k)‖^2 ≤ ‖w k‖^2) :
    ‖realL2DifferenceMap i h u‖^2 ≤ ‖g‖^2 :=
  le_of_tendsto_of_tendsto
    (((realL2DifferenceMap i h).continuous.continuousAt.tendsto.comp hv).norm.pow 2)
    (hw.norm.pow 2) (Eventually.of_forall hb)

end
end Yau

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
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_RealSmoothDifferenceBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau
open MeasureTheory Set
open scoped ContDiff
noncomputable section

theorem real_line_coord_deriv {n : ℕ} (u : Coord n → ℝ) (hu : ContDiff ℝ ∞ u)
    (i : Fin n) (h t : ℝ) (x : Coord n) :
    deriv (fun s : ℝ ↦ u (x+s • (Pi.single i h : Coord n))) t =
      h*coordPartial u (x+t • (Pi.single i h : Coord n)) i := by
  have hd := (hu.differentiable (by simp) (x+t • (Pi.single i h : Coord n))).hasFDerivAt
  have hp : HasDerivAt (fun s : ℝ ↦ x+s • (Pi.single i h : Coord n)) (Pi.single i h) t := by
    simpa using ((hasDerivAt_id t).smul_const (Pi.single i h : Coord n)).const_add x
  have hh : (Pi.single i h : Coord n)=h • (Pi.single i 1 : Coord n) := by
    ext j
    by_cases hj : j=i <;> simp [hj]
  have hd' := (hd.comp_hasDerivAt t hp).deriv
  simp only [Function.comp_def] at hd'
  rw [hd']
  simp only [coordPartial,hh,map_smul,smul_eq_mul]

theorem realDifferenceQuotient_sq_pointwise {n : ℕ} (u : Coord n → ℝ)
    (hu : ContDiff ℝ ∞ u) (i : Fin n) (h : ℝ) (x : Coord n) :
    (realDifferenceQuotient i h u x)^2 ≤
      ∫ t in Icc (0:ℝ) 1, (coordPartial u (x+t • (Pi.single i h : Coord n)) i)^2 := by
  by_cases hh : h=0
  · subst h
    simp only [realDifferenceQuotient,inv_zero,zero_mul,zero_pow (by decide : 2≠0)]
    exact integral_nonneg (fun _ ↦ sq_nonneg _)
  have hs : ContDiff ℝ ∞ (fun t : ℝ ↦ u (x+t • (Pi.single i h : Coord n))) :=
    hu.comp (contDiff_const.add (contDiff_id.smul contDiff_const))
  have hb := Yau.Geometry.real_interval_derivative_control _ hs
    (by norm_num : (0:ℝ)<1) 1 0 (by norm_num) (by norm_num)
  simp only [one_smul,zero_smul,add_zero,sub_zero,one_mul,real_line_coord_deriv u hu,
    mul_pow] at hb
  rw [integral_const_mul] at hb
  have hb' := mul_le_mul_of_nonneg_left hb (sq_nonneg h⁻¹)
  calc
    _ = h⁻¹^2*(u (x+Pi.single i h)-u x)^2 := mul_pow _ _ _
    _ ≤ h⁻¹^2*(h^2*(∫ t in Icc (0:ℝ) 1, (coordPartial u (x+t • (Pi.single i h : Coord n)) i)^2)) := hb'
    _ = _ := by field_simp

theorem real_translation_square_integrable {n : ℕ} (g : Coord n → ℝ)
    (hg : Continuous g) (hm : MemLp g 2 volume) (v : Coord n) :
    Integrable (fun q : Coord n × ℝ ↦ (g (q.1+q.2 • v))^2)
      (volume.prod (volume.restrict (Icc (0:ℝ) 1))) := by
  have hc : Continuous (fun q : Coord n × ℝ ↦ (g (q.1+q.2 • v))^2) :=
    (hg.comp (continuous_fst.add (continuous_snd.smul continuous_const))).pow 2
  apply (integrable_prod_iff' hc.aestronglyMeasurable).mpr
  constructor
  · exact Filter.Eventually.of_forall (fun t ↦ (hm.comp_measurePreserving
      (measurePreserving_add_right volume (t • v))).integrable_sq)
  · have he : (fun t : ℝ ↦ ∫ x : Coord n, ‖(g (x+t • v))^2‖) =
        fun _ : ℝ ↦ ∫ x : Coord n, (g x)^2 := by
      funext t
      simp only [Real.norm_eq_abs,abs_sq]
      exact integral_add_right_eq_self (fun x ↦ (g x)^2) (t • v)
    rw [he]
    exact integrable_const _

theorem real_smooth_difference_bound {n : ℕ} (u : Coord n → ℝ)
    (hu : ContDiff ℝ ∞ u) (hc : HasCompactSupport u) (i : Fin n) (h : ℝ) :
    MemLp (realDifferenceQuotient i h u) 2 volume ∧
      (∫ x, (realDifferenceQuotient i h u x)^2) ≤ ∫ x, (coordPartial u x i)^2 := by
  have hd := real_coordPartial_smooth u hu i
  have hm := real_compact_continuous_memLp _ hd.continuous (hc.fderiv_apply ℝ (Pi.single i 1))
  have hq := realDifferenceQuotient_memLp i h u (real_compact_continuous_memLp u hu.continuous hc)
  have hp := real_translation_square_integrable _ hd.continuous hm (Pi.single i h)
  refine ⟨hq,?_⟩
  calc
    _ ≤ ∫ x, ∫ t in Icc (0:ℝ) 1, (coordPartial u (x+t • (Pi.single i h : Coord n)) i)^2 :=
      integral_mono hq.integrable_sq hp.integral_prod_left (realDifferenceQuotient_sq_pointwise u hu i h)
    _ = ∫ t in Icc (0:ℝ) 1, ∫ x, (coordPartial u (x+t • (Pi.single i h : Coord n)) i)^2 :=
      integral_integral_swap hp
    _ = _ := by
      simp_rw [integral_add_right_eq_self (fun x ↦ (coordPartial u x i)^2)]
      simp

end
end Yau

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Charts_SphereChartDifferenceBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open MeasureTheory Yau.Geometry Set Filter
open scoped ContDiff Topology
noncomputable section

local instance sphereChartDifferenceMeasurable_ra06f3c_1 : MeasurableSpace Base := borel Base
local instance sphereChartDifferenceBorel_ra06f3c_1 : BorelSpace Base := ⟨rfl⟩
theorem sphere_chart_cutoff_difference_norm_bound (d : SphereEnergyData) (p : Base)
    (z : SphereEnergyHilbert d) (eta : Yau.Jets.Coord → ℝ) (he : ContDiff ℝ ∞ eta)
    (hs : tsupport eta ⊆ realFinCube 4) (i : Fin 4) (h : ℝ) :
    ‖Yau.realL2DifferenceMap i h (sphereCutoffValueMap d p eta he hs z)‖^2 ≤
      ‖sphereCutoffDerivativeMap d p eta he hs i z‖^2 := by
  obtain ⟨u,_,ha⟩ := sphere_chart_cutoff_strong_approximation d z
  have hc : HasCompactSupport eta :=
    (realFinCube_isCompact 4).of_isClosed_subset (isClosed_tsupport eta) hs
  apply Yau.real_difference_norm_bound_limit i h _ _ _ _ (ha p eta he hs).1 ((ha p eta he hs).2 i)
  intro k
  let v : Yau.Jets.Coord → ℝ := fun x ↦ eta x*(SphereEnergySmooth.toSmooth d (u k) : Base → ℝ)
    (sphereChartCoordMap p x)
  have hv : ContDiff ℝ ∞ v := he.mul
    (spherePullback_smooth _ (SphereEnergySmooth.toSmooth d (u k)).property p)
  have hb := (Yau.real_smooth_difference_bound v hv hc.mul_right i h).2
  have hvrep := sphereCutoffValueMap_smooth_ae d p eta he hs (u k)
  have hgrep := sphereCutoffDerivativeMap_smooth_ae d p eta he hs i (u k)
  rw [Yau.real_L2_norm_sq_rep _ _ (Yau.realL2DifferenceMap_ae i h _ v hvrep),
    Yau.real_L2_norm_sq_rep _ _ hgrep]
  exact hb

theorem sphere_chart_cutoff_difference_bound (d : SphereEnergyData) (p : Base)
    (z : SphereEnergyHilbert d) (eta : Yau.Jets.Coord → ℝ) (he : ContDiff ℝ ∞ eta)
    (hs : tsupport eta ⊆ realFinCube 4) (i : Fin 4) (h : ℝ) :
    let v := fun x ↦ eta x*(sphereEnergyL2Map d z) (sphereChartCoordMap p x)
    let G := fun x ↦ eta x*(sphereChartDerivativeMap d p i z) x +
      Yau.coordPartial eta x i*(sphereEnergyL2Map d z) (sphereChartCoordMap p x)
    MemLp (Yau.realDifferenceQuotient i h v) 2 volume ∧
      (∫ x, (Yau.realDifferenceQuotient i h v x)^2) ≤ ∫ x, (G x)^2 := by
  dsimp only
  have hv := sphereCutoffValueMap_ae d p eta he hs z
  have hg := sphereCutoffDerivativeMap_ae d p eta he hs i z
  have hb := sphere_chart_cutoff_difference_norm_bound d p z eta he hs i h
  rw [Yau.real_L2_norm_sq_rep _ _ (Yau.realL2DifferenceMap_ae i h _ _ hv),
    Yau.real_L2_norm_sq_rep _ _ hg] at hb
  exact ⟨Yau.realDifferenceQuotient_memLp i h _ (sphere_chart_cutoff_weak d p z eta he hs).1,hb⟩

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

local instance sphereChartDivergenceDataMeasurable_ra06f3c_1 : MeasurableSpace Base := borel Base
local instance sphereChartDivergenceDataBorel_ra06f3c_1 : BorelSpace Base := ⟨rfl⟩
theorem sphereChartPrincipalDensity_smooth (d : SphereEnergyData) (p : Base) (i j : Fin 4) :
    ContDiff ℝ ∞ (fun x ↦ sphereChartPrincipalDensity d p x i j) :=
  roundCoordDensity_smooth.mul (intrinsicRealPrincipal_smooth d.tensor d.smooth d.symm d.pos p i j)

theorem sphereChartPrincipalDensity_elliptic (d : SphereEnergyData) (p : Base)
    {K : Set Yau.Jets.Coord} (hK : IsCompact K) :
    ∃ c > 0, ∃ C > 0, ∀ x ∈ K, ∀ xi : Fin 4 → ℝ,
      c*(∑ i, xi i^2) ≤ (∑ i, ∑ j, xi i*sphereChartPrincipalDensity d p x i j*xi j) ∧
      (∑ i, ∑ j, xi i*sphereChartPrincipalDensity d p x i j*xi j) ≤ C*(∑ i, xi i^2) := by
  apply compact_matrix_uniform_ellipticity (sphereChartPrincipalDensity d p)
    (fun i j ↦ (sphereChartPrincipalDensity_smooth d p i j).continuous) _ hK
  intro x
  exact (intrinsicRealPrincipal_posDef d.tensor d.symm d.pos p x).smul (roundCoordDensity_pos x)

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

local instance sphereChartFluxL2Measurable_ra06f3c_1 : MeasurableSpace Base := borel Base
local instance sphereChartFluxL2Borel_ra06f3c_1 : BorelSpace Base := ⟨rfl⟩
theorem sphereChartForcingZero_memLp (d : SphereEnergyData) (p : Base)
    (f : SphereWeightedL2 d) : MemLp (sphereChartForcingZero d p f) 2 volume := by
  obtain ⟨_,_,hb⟩ := sphereChartResolventForcing_bound d p (realFinCube_isCompact 4)
  exact (memLp_indicator_iff_restrict (realFinCube_isCompact 4).measurableSet).mpr (hb f).1

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Charts_SphereChartUniformH1Bounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open MeasureTheory Yau.Geometry Set
open scoped ContDiff
noncomputable section

local instance sphereChartUniformH1BoundsMeasurable_ra06f3c_1 : MeasurableSpace Base := borel Base
local instance sphereChartUniformH1BoundsBorel_ra06f3c_1 : BorelSpace Base := ⟨rfl⟩
theorem sphere_cutoff_uniform_H1_bound (d : SphereEnergyData) (p : Base)
    (eta : Yau.Jets.Coord → ℝ) (he : ContDiff ℝ ∞ eta)
    (hs : tsupport eta ⊆ realFinCube 4) :
    ∃ C > 0, ∀ (z : SphereEnergyHilbert d) (i : Fin 4) (h : ℝ),
      (∫ x, (eta x*(sphereChartDerivativeMap d p i z) x+
        Yau.coordPartial eta x i*(sphereEnergyL2Map d z) (sphereChartCoordMap p x))^2) ≤ C*‖z‖^2 ∧
      (∫ x, (Yau.realDifferenceQuotient i h
        (fun y ↦ eta y*(sphereEnergyL2Map d z) (sphereChartCoordMap p y)) x)^2) ≤ C*‖z‖^2 := by
  let C : ℝ := 1+∑ j : Fin 4, ‖sphereCutoffDerivativeMap d p eta he hs j‖^2
  have hC : 0 < C := by dsimp [C] <;> positivity
  refine ⟨C,hC,fun z i h ↦ ?_⟩
  have hi : ‖sphereCutoffDerivativeMap d p eta he hs i‖^2 ≤ C := by
    have ht := Finset.single_le_sum (s := Finset.univ)
      (f := fun j : Fin 4 ↦ ‖sphereCutoffDerivativeMap d p eta he hs j‖^2)
      (fun j _ ↦ sq_nonneg _) (Finset.mem_univ i)
    dsimp [C]
    linarith
  have hn := (sphereCutoffDerivativeMap d p eta he hs i).le_opNorm z
  have hn2 : ‖sphereCutoffDerivativeMap d p eta he hs i z‖^2 ≤ C*‖z‖^2 := by
    have ht := mul_le_mul_of_nonneg_right hi (sq_nonneg ‖z‖)
    nlinarith [norm_nonneg (sphereCutoffDerivativeMap d p eta he hs i z),
      mul_nonneg (norm_nonneg (sphereCutoffDerivativeMap d p eta he hs i)) (norm_nonneg z)]
  rw [Yau.real_L2_norm_sq_rep _ _ (sphereCutoffDerivativeMap_ae d p eta he hs i z)] at hn2
  exact ⟨hn2,(sphere_chart_cutoff_difference_bound d p z eta he hs i h).2.trans hn2⟩

theorem sphere_chart_uniform_gradient_bound (d : SphereEnergyData) (p : Base) :
    ∃ C > 0, ∀ z : SphereEnergyHilbert d,
      (∑ j : Fin 4, ∫ x in realFinCube 4, ((sphereChartDerivativeMap d p j z) x)^2) ≤ C*‖z‖^2 := by
  obtain ⟨B,hB,hb⟩ := sphereChartDerivativeMap_bound d p
  refine ⟨4*B^2,by positivity,fun z ↦ ?_⟩
  have hj (j : Fin 4) :
      (∫ x in realFinCube 4, ((sphereChartDerivativeMap d p j z) x)^2) ≤ B^2*‖z‖^2 := by
    have hn : ‖sphereChartDerivativeMap d p j z‖^2 =
        ∫ x in realFinCube 4, ((sphereChartDerivativeMap d p j z) x)^2 := by
      simpa only [Lp.toLp_coeFn] using Yau.real_toLp_norm_sq _ (Lp.memLp (sphereChartDerivativeMap d p j z))
    rw [← hn]
    have ht := hb j z
    nlinarith [norm_nonneg (sphereChartDerivativeMap d p j z),mul_nonneg hB.le (norm_nonneg z)]
  have ht := Finset.sum_le_sum (s := Finset.univ) (fun j _ ↦ hj j)
  simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_ofNat,mul_assoc] using ht

theorem sphere_chart_forcingZero_uniform_bound (d : SphereEnergyData) (p : Base) :
    ∃ C > 0, ∀ f : SphereWeightedL2 d,
      (∫ x, (sphereChartForcingZero d p f x)^2) ≤ C*(‖f‖^2+‖sphereWeakSolution d f‖^2) := by
  obtain ⟨C,hC,hb⟩ := sphereChartResolventForcing_bound d p (realFinCube_isCompact 4)
  refine ⟨C,hC,fun f ↦ ?_⟩
  have he : (fun x ↦ (sphereChartForcingZero d p f x)^2) =
      (realFinCube 4).indicator (fun x ↦ (sphereChartResolventForcing d p f x)^2) := by
    funext x
    by_cases hx : x ∈ realFinCube 4 <;> simp [sphereChartForcingZero,hx]
  rw [he,integral_indicator (realFinCube_isCompact 4).measurableSet]
  exact (hb f).2

end
end Yau.Target

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

theorem realDifferenceQuotient_mul {n : ℕ} (i : Fin n) (h : ℝ)
    (a u : Coord n → ℝ) (x : Coord n) :
    realDifferenceQuotient i h (fun y ↦ a y*u y) x =
      a (x+Pi.single i h)*realDifferenceQuotient i h u x+
      realDifferenceQuotient i h a x*u x := by
  unfold realDifferenceQuotient
  ring

theorem realDifferenceQuotient_sum {n m : ℕ} (i : Fin n) (h : ℝ)
    (u : Fin m → Coord n → ℝ) (x : Coord n) :
    realDifferenceQuotient i h (fun y ↦ ∑ j, u j y) x =
      ∑ j, realDifferenceQuotient i h (u j) x := by
  simp only [realDifferenceQuotient,mul_sub,Finset.mul_sum,Finset.sum_sub_distrib]

theorem real_coordPartial_eq_zero_of_one {n : ℕ} (eta : Coord n → ℝ) (x : Coord n)
    (he : eta =ᶠ[𝓝 x] (fun _ ↦ 1)) (j : Fin n) : coordPartial eta x j=0 := by
  unfold coordPartial
  rw [he.fderiv_eq]
  simp

theorem real_cutoff_gradient_difference_of_one {n : ℕ} (eta u U : Coord n → ℝ)
    (i j : Fin n) (h : ℝ) (x : Coord n)
    (he : eta =ᶠ[𝓝 x] (fun _ ↦ 1))
    (ht : eta =ᶠ[𝓝 (x+Pi.single i h)] (fun _ ↦ 1)) :
    realDifferenceQuotient i h (fun y ↦ eta y*U y+coordPartial eta y j*u y) x =
      realDifferenceQuotient i h U x := by
  simp only [realDifferenceQuotient,he.eq_of_nhds,ht.eq_of_nhds,
    real_coordPartial_eq_zero_of_one eta x he j,
    real_coordPartial_eq_zero_of_one eta _ ht j,one_mul,zero_mul,add_zero]

open MeasureTheory Set
open scoped ContDiff

end Yau

end

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Charts_SphereFluxDifferenceExpansion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open MeasureTheory Yau.Geometry Set
noncomputable section

theorem sphereChartFluxZero_difference_expansion (d : SphereEnergyData) (p : Base)
    (z : SphereEnergyHilbert d) (i j : Fin 4) (h : ℝ) (x : Yau.Jets.Coord)
    (hx : x ∈ realFinCube 4) (ht : x+Pi.single i h ∈ realFinCube 4) :
    Yau.realDifferenceQuotient i h (sphereChartFluxZero d p z j) x =
      ∑ a, (sphereChartPrincipalDensity d p (x+Pi.single i h) a j*
          Yau.realDifferenceQuotient i h (sphereChartDerivativeMap d p a z) x+
        Yau.realDifferenceQuotient i h (fun y ↦ sphereChartPrincipalDensity d p y a j) x*
          (sphereChartDerivativeMap d p a z) x) := by
  have he : Yau.realDifferenceQuotient i h (sphereChartFluxZero d p z j) x =
      Yau.realDifferenceQuotient i h (sphereChartCompletedFlux d p z j) x := by
    simp only [Yau.realDifferenceQuotient,sphereChartFluxZero,indicator_of_mem hx,indicator_of_mem ht]
  rw [he]
  unfold sphereChartCompletedFlux
  rw [Yau.realDifferenceQuotient_sum]
  apply Finset.sum_congr rfl
  intro a _
  exact Yau.realDifferenceQuotient_mul i h _ _ x

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Coefficients_SphereCoefficientDifferenceBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Yau.Geometry Set
open scoped ContDiff
noncomputable section

theorem sphereChartPrincipalDensity_difference_bound (d : SphereEnergyData) (p : Base) :
    ∃ C > 0, ∀ (i j k : Fin 4) (h : ℝ) (x : Yau.Jets.Coord),
      x ∈ realFinCube 4 → x+(Pi.single k h : Yau.Jets.Coord) ∈ realFinCube 4 →
      |Yau.realDifferenceQuotient k h (fun y ↦ sphereChartPrincipalDensity d p y i j) x| ≤ C := by
  let F : Yau.Jets.Coord → Fin 4 → Fin 4 → Yau.Jets.Coord →L[ℝ] ℝ :=
    fun x i j ↦ fderiv ℝ (fun y ↦ sphereChartPrincipalDensity d p y i j) x
  have hF : Continuous F := continuous_pi (fun i ↦ continuous_pi (fun j ↦
    ((sphereChartPrincipalDensity_smooth d p i j).fderiv_right (m := ∞) (by simp)).continuous))
  obtain ⟨C,hC,hb⟩ := ((realFinCube_isCompact 4).image hF).isBounded.exists_pos_norm_le
  refine ⟨C,hC,?_⟩
  intro i j k h x hx hxt
  have hder (y : Yau.Jets.Coord) (hy : y ∈ realFinCube 4) :
      ‖fderiv ℝ (fun y ↦ sphereChartPrincipalDensity d p y i j) y‖ ≤ C :=
    (norm_le_pi_norm (F y i) j).trans ((norm_le_pi_norm (F y) i).trans (hb _ ⟨y,hy,rfl⟩))
  have hconv : Convex ℝ (realFinCube 4) := convex_pi (fun _ _ ↦ convex_Icc _ _)
  have hd := hconv.norm_image_sub_le_of_norm_fderiv_le
    (fun y _ ↦ (sphereChartPrincipalDensity_smooth d p i j).differentiable (by simp) y) hder hx hxt
  simp only [add_sub_cancel_left,Pi.norm_single,Real.norm_eq_abs] at hd
  by_cases hh : h=0
  · subst h
    simp [Yau.realDifferenceQuotient,hC.le]
  · calc
      _ = |h⁻¹| * |sphereChartPrincipalDensity d p (x+(Pi.single k h : Yau.Jets.Coord)) i j-sphereChartPrincipalDensity d p x i j| :=
        abs_mul _ _
      _ ≤ |h⁻¹| * (C*|h|) := mul_le_mul_of_nonneg_left hd (abs_nonneg _)
      _ = C := by rw [abs_inv]; field_simp [abs_ne_zero.mpr hh]

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_RealDifferenceCoercivity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau
noncomputable section

theorem real_young_coefficient (e B a x y : ℝ) (he : 0 < e) (hB : 0 ≤ B)
    (ha : |a| ≤ B) : -(a*x*y) ≤ e*x^2+(B^2/e)*y^2 := by
  have h0 : -(a*x*y) ≤ B*|x| *|y| := calc
    _ ≤ |a*x*y| := neg_le_abs _
    _ = |a| *|x| *|y| := by rw [abs_mul,abs_mul]
    _ ≤ B*|x| *|y| := mul_le_mul_of_nonneg_right
      (mul_le_mul ha le_rfl (abs_nonneg x) hB) (abs_nonneg y)
  have hs := sq_nonneg (e*|x|-B*|y|)
  have heq : (B^2/e)*e=B^2 := div_mul_cancel₀ _ he.ne'
  have hx := sq_abs x
  have hy := sq_abs y
  have hp := mul_nonneg (sq_nonneg x) (sq_nonneg e)
  have hq := mul_nonneg (sq_nonneg B) (sq_nonneg y)
  apply (mul_le_mul_iff_right₀ he).mp
  nlinarith

theorem real_difference_coercivity (m B : ℝ) (hm : 0 < m) (hB : 0 ≤ B)
    (M N : Fin 4 → Fin 4 → ℝ) (T V R : Fin 4 → ℝ)
    (hM : ∀ a j, |M a j| ≤ B) (hN : ∀ a j, |N a j| ≤ B)
    (hell : m*(∑ j, T j^2) ≤ ∑ a, ∑ j, T a*M a j*T j) :
    (m/2)*(∑ j, T j^2) ≤
      (∑ j, (∑ a, (M a j*T a+N a j*V a))*(T j+2*R j)) +
      (256*B^2/m+4*B)*( (∑ j, V j^2)+(∑ j, R j^2)) := by
  have he : 0 < m/16 := by positivity
  have h1 (a j : Fin 4) : -(2*M a j*T a*R j) ≤
      (m/16)*T a^2+(64*B^2/m)*R j^2 := by
    have h := real_young_coefficient (m/16) B (M a j) (T a) (2*R j) he hB (hM a j)
    first | (convert h using 1 <;> first | (with_reducible_and_instances rfl) | ring) | exact (le_of_eq (by ring)).trans (h.trans (le_of_eq (by ring)))
  have h2 (a j : Fin 4) : -(N a j*V a*T j) ≤
      (m/16)*T j^2+(16*B^2/m)*V a^2 := by
    have h := real_young_coefficient (m/16) B (N a j) (T j) (V a) he hB (hN a j)
    first | (convert h using 1 <;> first | (with_reducible_and_instances rfl) | ring) | exact (le_of_eq (by ring)).trans (h.trans (le_of_eq (by ring)))
  have h3 (a j : Fin 4) : -(2*N a j*V a*R j) ≤ B*(V a^2+R j^2) := by
    have ha : -(2*N a j*V a*R j) ≤ 2*B*|V a| *|R j| := calc
      _ ≤ |2*N a j*V a*R j| := neg_le_abs _
      _ = 2*|N a j| *|V a| *|R j| := by simp only [abs_mul,abs_of_nonneg (show (0:ℝ) ≤ 2 by norm_num)]
      _ ≤ 2*B*|V a| *|R j| := by gcongr; exact hN a j
    have hsq := mul_nonneg hB (sq_nonneg (|V a|-|R j|))
    nlinarith [sq_abs (V a),sq_abs (R j)]
  have hs1 := Finset.sum_le_sum (s := Finset.univ) (fun j _ ↦
    Finset.sum_le_sum (s := Finset.univ) (fun a _ ↦ h1 a j))
  have hs2 := Finset.sum_le_sum (s := Finset.univ) (fun j _ ↦
    Finset.sum_le_sum (s := Finset.univ) (fun a _ ↦ h2 a j))
  have hs3 := Finset.sum_le_sum (s := Finset.univ) (fun j _ ↦
    Finset.sum_le_sum (s := Finset.univ) (fun a _ ↦ h3 a j))
  simp only [mul_add,Finset.sum_add_distrib,
    Finset.sum_neg_distrib,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at hs1 hs2 hs3
  simp only [← mul_assoc,← Finset.mul_sum] at hs1 hs2 hs3
  norm_num only [Nat.cast_ofNat] at hs1 hs2 hs3
  have hid : (∑ j, (∑ a, (M a j*T a+N a j*V a))*(T j+2*R j)) =
      (∑ a, ∑ j, T a*M a j*T j) +
      (∑ j, ∑ a, 2*M a j*T a*R j) +
      (∑ j, ∑ a, N a j*V a*T j) +
      (∑ j, ∑ a, 2*N a j*V a*R j) := by
    rw [Finset.sum_comm (f := fun a j ↦ T a*M a j*T j)]
    simp only [Finset.sum_mul,← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro a _
    ring
  rw [hid]
  have hV : 0 ≤ ∑ j, V j^2 := Finset.sum_nonneg (fun _ _ ↦ sq_nonneg _)
  have hcoef : 0 ≤ 192*B^2/m := by positivity
  have hrest := mul_nonneg hcoef hV
  simp only [div_eq_mul_inv] at hs1 hs2 hrest ⊢
  nlinarith only [hell,hs1,hs2,hs3,hrest]

end
end Yau

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Charts_SphereDifferenceCoercivity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open MeasureTheory Yau.Geometry Set Filter
open scoped ContDiff Topology
noncomputable section

local instance sphereDifferenceCoercivityMeasurable_ra06f3c_1 : MeasurableSpace Base := borel Base
local instance sphereDifferenceCoercivityBorel_ra06f3c_1 : BorelSpace Base := ⟨rfl⟩
theorem sphereChartPrincipalDensity_entries_bound (d : SphereEnergyData) (p : Base) :
    ∃ B > 0, ∀ x ∈ realFinCube 4, ∀ a j : Fin 4,
      |sphereChartPrincipalDensity d p x a j| ≤ B := by
  have hc : Continuous (sphereChartPrincipalDensity d p) := continuous_pi (fun a ↦
    continuous_pi (fun j ↦ (sphereChartPrincipalDensity_smooth d p a j).continuous))
  obtain ⟨B,hB,hb⟩ := ((realFinCube_isCompact 4).image hc).isBounded.exists_pos_norm_le
  refine ⟨B,hB,fun x hx a j ↦ ?_⟩
  exact (norm_le_pi_norm (sphereChartPrincipalDensity d p x a) j).trans
    ((norm_le_pi_norm (sphereChartPrincipalDensity d p x) a).trans (hb _ ⟨x,hx,rfl⟩))

theorem sphere_difference_square_test_derivative (d : SphereEnergyData) (p : Base)
    (z : SphereEnergyHilbert d) (eta theta : Yau.Jets.Coord → ℝ)
    (ht : ContDiff ℝ ∞ theta) (i j : Fin 4) (h : ℝ)
    (h1 : ∀ x ∈ tsupport theta, eta =ᶠ[𝓝 x] (fun _ ↦ 1) ∧
      eta =ᶠ[𝓝 (x+Pi.single i h)] (fun _ ↦ 1)) (x : Yau.Jets.Coord) :
    theta x*theta x*Yau.realDifferenceQuotient i h
      (fun y ↦ eta y*(sphereChartDerivativeMap d p j z) y+
        Yau.coordPartial eta y j*(sphereEnergyL2Map d z) (sphereChartCoordMap p y)) x+
      Yau.coordPartial (fun y ↦ theta y*theta y) x j*Yau.realDifferenceQuotient i h
        (fun y ↦ eta y*(sphereEnergyL2Map d z) (sphereChartCoordMap p y)) x =
    theta x*(theta x*Yau.realDifferenceQuotient i h (sphereChartDerivativeMap d p j z) x+
      2*(Yau.coordPartial theta x j*Yau.realDifferenceQuotient i h
        (fun y ↦ eta y*(sphereEnergyL2Map d z) (sphereChartCoordMap p y)) x)) := by
  rw [Yau.real_coordPartial_mul theta theta ht ht]
  by_cases hx : x ∈ tsupport theta
  · rw [Yau.real_cutoff_gradient_difference_of_one eta _ _ i j h x (h1 x hx).1 (h1 x hx).2]
    ring
  · rw [image_eq_zero_of_notMem_tsupport hx]
    ring

theorem sphere_difference_pointwise_coercivity (d : SphereEnergyData) (p : Base) :
    ∃ m > 0, ∃ K > 0,
      ∀ (z : SphereEnergyHilbert d) (eta theta : Yau.Jets.Coord → ℝ)
        (_ : ContDiff ℝ ∞ theta)
        (_ : tsupport theta ⊆ Yau.realCenteredCube 4 (3/4))
        (i : Fin 4) (h : ℝ) (_ : |h| ≤ 1/8)
        (_ : ∀ x ∈ tsupport theta, eta =ᶠ[𝓝 x] (fun _ ↦ 1) ∧
          eta =ᶠ[𝓝 (x+Pi.single i h)] (fun _ ↦ 1)),
      let q := Yau.realDifferenceQuotient i h
        (fun y ↦ eta y*(sphereEnergyL2Map d z) (sphereChartCoordMap p y))
      let T := fun j x ↦ theta x*Yau.realDifferenceQuotient i h (sphereChartDerivativeMap d p j z) x
      let V := fun j x ↦ theta x*(sphereChartDerivativeMap d p j z) x
      let R := fun j x ↦ Yau.coordPartial theta x j*q x
      let P := fun j x ↦ theta x*(T j x+2*R j x)
      ∀ x, (m/2)*(∑ j, (T j x)^2) ≤
        (∑ j, Yau.realDifferenceQuotient i h (sphereChartFluxZero d p z j) x*P j x)+
          K*((∑ j, (V j x)^2)+(∑ j, (R j x)^2)) := by
  obtain ⟨m,hm,C,hC,hell⟩ := sphereChartPrincipalDensity_elliptic d p (realFinCube_isCompact 4)
  obtain ⟨B,hB,hb⟩ := sphereChartPrincipalDensity_entries_bound d p
  obtain ⟨D,hD,hd⟩ := sphereChartPrincipalDensity_difference_bound d p
  let E := B+D
  have hE : 0 < E := by dsimp [E] <;> positivity
  refine ⟨m,hm,256*E^2/m+4*E,by positivity,?_⟩
  intro z eta theta ht hts i h hh h1
  dsimp only
  intro x
  by_cases hx : x ∈ tsupport theta
  · have hx0 : x ∈ realFinCube 4 := Yau.realCenteredCube_mono (by norm_num) (hts hx)
    have hxt : x+Pi.single i h ∈ realFinCube 4 := by
      apply Yau.realCenteredCube_shift i (h := -h) (r := 3/4)
        (by simpa only [abs_neg] using (show |h| ≤ (1:ℝ)-3/4 by linarith))
      simpa only [Pi.single_neg,add_neg_cancel_right] using hts hx
    let T : Fin 4 → ℝ := fun j ↦ theta x*Yau.realDifferenceQuotient i h (sphereChartDerivativeMap d p j z) x
    let V : Fin 4 → ℝ := fun j ↦ theta x*(sphereChartDerivativeMap d p j z) x
    let R : Fin 4 → ℝ := fun j ↦ Yau.coordPartial theta x j*
      Yau.realDifferenceQuotient i h (fun y ↦ eta y*(sphereEnergyL2Map d z) (sphereChartCoordMap p y)) x
    have hmB (a j : Fin 4) : |sphereChartPrincipalDensity d p (x+Pi.single i h) a j| ≤ E :=
      (hb _ hxt a j).trans (by dsimp [E] <;> linarith)
    have hnB (a j : Fin 4) :
        |Yau.realDifferenceQuotient i h (fun y ↦ sphereChartPrincipalDensity d p y a j) x| ≤ E :=
      (hd a j i h x hx0 hxt).trans (by dsimp [E] <;> linarith)
    have hellT := (hell (x+Pi.single i h) hxt T).1
    have hc := Yau.real_difference_coercivity m E hm hE.le
    specialize hc (sphereChartPrincipalDensity d p (x+Pi.single i h))
      (fun a j ↦ Yau.realDifferenceQuotient i h (fun y ↦ sphereChartPrincipalDensity d p y a j) x)
      T V R
    specialize hc hmB hnB hellT
    have heq (j : Fin 4) :
        Yau.realDifferenceQuotient i h (sphereChartFluxZero d p z j) x*
          (theta x*(T j+2*R j)) =
        (∑ a, (sphereChartPrincipalDensity d p (x+Pi.single i h) a j*T a+
          Yau.realDifferenceQuotient i h (fun y ↦ sphereChartPrincipalDensity d p y a j) x*V a))*(T j+2*R j) := by
      rw [sphereChartFluxZero_difference_expansion d p z i j h x hx0 hxt]
      rw [← mul_assoc]
      congr 1
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro a _
      dsimp [T,V]
      ring
    simp_rw [← heq] at hc
    exact hc
  · have hz := image_eq_zero_of_notMem_tsupport hx
    have hdz (j : Fin 4) : Yau.coordPartial theta x j=0 :=
      image_eq_zero_of_notMem_tsupport (f := fun y ↦ Yau.coordPartial theta y j)
        (fun hs ↦ hx (tsupport_fderiv_apply_subset ℝ (Pi.single j 1) hs))
    simp only [hz,hdz,zero_mul,mul_zero,zero_pow (by decide : (2:ℕ)≠0),Finset.sum_const_zero,add_zero,le_refl]

end
end Yau.Target

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

local instance sphereDifferenceTestMeasurable_ra06f3c_1 : MeasurableSpace Base := borel Base
local instance sphereDifferenceTestBorel_ra06f3c_1 : BorelSpace Base := ⟨rfl⟩
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
-- module Solutions.OAIQ237_NY.NodalSets_Charts_SphereDifferenceTestWeak
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open MeasureTheory Yau.Geometry Set Filter
open scoped ContDiff Topology
noncomputable section

theorem sphere_difference_test_strong_approximation (d : SphereEnergyData) (z : SphereEnergyHilbert d) :
    ∃ u : ℕ → SphereEnergySmooth d,
      Tendsto (fun n ↦ sphereEnergyToCompletion d (u n)) atTop (𝓝 z) ∧
      ∀ (p : Base) (eta theta : Yau.Jets.Coord → ℝ) (he : ContDiff ℝ ∞ eta) (ht : ContDiff ℝ ∞ theta)
        (hes : tsupport eta ⊆ realFinCube 4) (hts : tsupport theta ⊆ realFinCube 4) (i : Fin 4) (h : ℝ),
        Tendsto (fun n ↦ sphereDifferenceTestMap d p eta theta he ht hes hts i h (sphereEnergyToCompletion d (u n)))
          atTop (𝓝 (sphereDifferenceTestMap d p eta theta he ht hes hts i h z)) ∧
        ∀ j : Fin 4, Tendsto
          (fun n ↦ sphereDifferenceTestDerivativeMap d p eta theta he ht hes hts i h j (sphereEnergyToCompletion d (u n)))
          atTop (𝓝 (sphereDifferenceTestDerivativeMap d p eta theta he ht hes hts i h j z)) := by
  obtain ⟨u,hu,_⟩ := sphere_chart_strong_approximation d z
  refine ⟨u,hu,fun p eta theta he ht hes hts i h ↦ ⟨?_,fun j ↦ ?_⟩⟩
  · exact (sphereDifferenceTestMap d p eta theta he ht hes hts i h).continuous.continuousAt.tendsto.comp hu
  · exact (sphereDifferenceTestDerivativeMap d p eta theta he ht hes hts i h j).continuous.continuousAt.tendsto.comp hu

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Charts_SphereDifferenceTestBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open MeasureTheory Yau.Geometry Set
open scoped ContDiff
noncomputable section

theorem sphere_difference_test_difference_bound (d : SphereEnergyData) (p : Base)
    (z : SphereEnergyHilbert d) (eta theta : Yau.Jets.Coord → ℝ)
    (he : ContDiff ℝ ∞ eta) (ht : ContDiff ℝ ∞ theta)
    (hes : tsupport eta ⊆ realFinCube 4) (hts : tsupport theta ⊆ realFinCube 4)
    (i : Fin 4) (h : ℝ) (j : Fin 4) (t : ℝ) :
    ‖Yau.realL2DifferenceMap j t (sphereDifferenceTestMap d p eta theta he ht hes hts i h z)‖^2 ≤
      ‖sphereDifferenceTestDerivativeMap d p eta theta he ht hes hts i h j z‖^2 := by
  obtain ⟨u,_,hu⟩ := sphere_difference_test_strong_approximation d z
  apply Yau.real_difference_norm_bound_limit j t _ _ _ _
    (hu p eta theta he ht hes hts i h).1 ((hu p eta theta he ht hes hts i h).2 j)
  intro k
  let v : Yau.Jets.Coord → ℝ := fun x ↦ eta x*(SphereEnergySmooth.toSmooth d (u k) : Base → ℝ) (sphereChartCoordMap p x)
  let phi : Yau.Jets.Coord → ℝ := fun x ↦ theta x*Yau.realDifferenceQuotient i h v x
  have hv : ContDiff ℝ ∞ v := he.mul (spherePullback_smooth _ (SphereEnergySmooth.toSmooth d (u k)).property p)
  have hp : ContDiff ℝ ∞ phi := ht.mul (Yau.realDifferenceQuotient_smooth i h v hv)
  have hc : HasCompactSupport theta := (realFinCube_isCompact 4).of_isClosed_subset (isClosed_tsupport theta) hts
  have hval := sphereDifferenceTestMap_smooth_ae d p eta theta he ht hes hts i h (u k)
  have hder := sphereDifferenceTestDerivativeMap_smooth_ae d p eta theta he ht hes hts i h j (u k)
  rw [Yau.real_L2_norm_sq_rep _ _ (Yau.realL2DifferenceMap_ae j t _ _ hval),
    Yau.real_L2_norm_sq_rep _ _ hder]
  exact (Yau.real_smooth_difference_bound phi hp hc.mul_right j t).2

end
end Yau.Target

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

theorem real_interior_difference_cutoffs :
    ∃ eta theta : Jets.Coord → ℝ,
      ContDiff ℝ ∞ eta ∧ ContDiff ℝ ∞ theta ∧ HasCompactSupport eta ∧ HasCompactSupport theta ∧
      tsupport eta ⊆ realCenteredCube 4 1 ∧ tsupport theta ⊆ realCenteredCube 4 (3/4) ∧
      (∀ x, 0 ≤ eta x ∧ eta x ≤ 1) ∧ (∀ x, 0 ≤ theta x ∧ theta x ≤ 1) ∧
      (∀ x ∈ realCenteredCube 4 (1/2), theta =ᶠ[𝓝 x] (fun _ ↦ 1)) ∧
      ∀ (i : Fin 4) (h : ℝ), |h| ≤ 1/8 → ∀ x ∈ tsupport theta,
        eta =ᶠ[𝓝 x] (fun _ ↦ 1) ∧ eta =ᶠ[𝓝 (x+Pi.single i h)] (fun _ ↦ 1) := by
  obtain ⟨eta,he,hec,hes,heb,he1⟩ := real_cube_smooth_cutoff (7/8) 1 (by norm_num)
  obtain ⟨theta,ht,htc,hts,htb,ht1⟩ := real_cube_smooth_cutoff (1/2) (3/4) (by norm_num)
  refine ⟨eta,theta,he,ht,hec,htc,hes,hts,heb,htb,ht1,?_⟩
  intro i h hh x hx
  have hxt : x ∈ realCenteredCube 4 (3/4) := hts hx
  refine ⟨he1 x (realCenteredCube_mono (by norm_num) hxt),he1 _ ?_⟩
  have hz : (x+Pi.single i h)+(Pi.single i (-h) : Jets.Coord)=x := by
    simp only [Pi.single_neg,add_neg_cancel_right]
  apply realCenteredCube_shift i (h := -h) (r := 3/4)
    (by simpa only [abs_neg] using (show |h| ≤ (7/8:ℝ)-3/4 by linarith))
  rw [hz]
  exact hxt

end
end Yau

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Charts_SphereInteriorDifferenceL2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open MeasureTheory Yau.Geometry Set Filter
open scoped ContDiff Topology
noncomputable section

local instance sphereInteriorDifferenceL2Measurable_ra06f3c_1 : MeasurableSpace Base := borel Base
local instance sphereInteriorDifferenceL2Borel_ra06f3c_1 : BorelSpace Base := ⟨rfl⟩
theorem sphere_chart_interior_difference_memLp (d : SphereEnergyData) (p : Base)
    (z : SphereEnergyHilbert d) (i j : Fin 4) (h : ℝ) (hh : |h| ≤ 1/8) :
    MemLp (Yau.realDifferenceQuotient i h (sphereChartDerivativeMap d p j z)) 2
      (volume.restrict (Yau.realCenteredCube 4 (1/2))) := by
  obtain ⟨eta,theta,he,ht,hec,htc,hes,hts,heb,htb,ht1,he1⟩ :=
    Yau.real_interior_difference_cutoffs
  have hes' : tsupport eta ⊆ realFinCube 4 := hes
  have hg := (sphere_chart_cutoff_weak d p z eta he hes').2 j
  have hm := (Yau.realDifferenceQuotient_memLp i h _ hg.1).mono_measure
    (Measure.restrict_le_self (s := Yau.realCenteredCube 4 (1/2)))
  apply hm.ae_eq
  apply (ae_restrict_iff' (Yau.realCenteredCube_isCompact 4 (1/2)).measurableSet).mpr
  apply Filter.Eventually.of_forall
  intro x hx
  have hxθ : x ∈ tsupport theta := subset_tsupport theta (by
    change theta x ≠ 0
    rw [(ht1 x hx).eq_of_nhds]
    norm_num)
  obtain ⟨hex,het⟩ := he1 i h hh x hxθ
  exact Yau.real_cutoff_gradient_difference_of_one eta _ _ i j h x hex het

theorem sphere_chart_weighted_difference_memLp (d : SphereEnergyData) (p : Base)
    (z : SphereEnergyHilbert d) (eta theta : Yau.Jets.Coord → ℝ)
    (he : ContDiff ℝ ∞ eta) (ht : Continuous theta)
    (hes : tsupport eta ⊆ realFinCube 4) (htc : HasCompactSupport theta)
    (i j : Fin 4) (h : ℝ)
    (h1 : ∀ x ∈ tsupport theta, eta =ᶠ[𝓝 x] (fun _ ↦ 1) ∧
      eta =ᶠ[𝓝 (x+Pi.single i h)] (fun _ ↦ 1)) :
    MemLp (fun x ↦ theta x*Yau.realDifferenceQuotient i h (sphereChartDerivativeMap d p j z) x)
      2 volume := by
  have hg := (sphere_chart_cutoff_weak d p z eta he hes).2 j
  have hm := Yau.realDifferenceQuotient_memLp i h _ hg.1
  have hb := Yau.real_compact_localL2_product htc theta _ ht (Subset.rfl)
    (hm.mono_measure Measure.restrict_le_self)
  apply hb.ae_eq
  apply Filter.Eventually.of_forall
  intro x
  dsimp only
  by_cases hx : x ∈ tsupport theta
  · exact congrArg (fun t : ℝ ↦ theta x*t)
      (Yau.real_cutoff_gradient_difference_of_one eta _ _ i j h x (h1 x hx).1 (h1 x hx).2)
  · rw [image_eq_zero_of_notMem_tsupport hx,zero_mul,zero_mul]

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_RealCompactGradientMultiplier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau
open MeasureTheory Set
open scoped ContDiff
noncomputable section

theorem real_compact_gradient_multiplier_bound {n : ℕ} (theta : Coord n → ℝ)
    (ht : ContDiff ℝ ∞ theta) (hc : HasCompactSupport theta) :
    ∃ B > 0, ∀ (u : Coord n → ℝ), MemLp u 2 volume →
      (∀ j : Fin n, MemLp (fun x ↦ coordPartial theta x j*u x) 2 volume) ∧
      (∑ j : Fin n, ∫ x, (coordPartial theta x j*u x)^2) ≤ B*(∫ x, (u x)^2) := by
  let L (j : Fin n) : RealEuclideanL2 n →L[ℝ] RealEuclideanL2 n :=
    realGlobalCompactMap hc (fun x ↦ coordPartial theta x j)
      (real_coordPartial_smooth theta ht j).continuous (tsupport_fderiv_apply_subset ℝ (Pi.single j 1))
  let B : ℝ := 1+∑ j : Fin n, ‖L j‖^2
  refine ⟨B,by dsimp [B] <;> positivity,fun u hu ↦ ?_⟩
  have hrep (j : Fin n) : (L j (hu.toLp u) : Coord n → ℝ) =ᵐ[volume]
      fun x ↦ coordPartial theta x j*u x :=
    realGlobalCompactMap_ae hc _ (real_coordPartial_smooth theta ht j).continuous
      (tsupport_fderiv_apply_subset ℝ (Pi.single j 1)) _ _ hu.coeFn_toLp
  have hj (j : Fin n) : (∫ x, (coordPartial theta x j*u x)^2) ≤ ‖L j‖^2*(∫ x, (u x)^2) := by
    rw [← real_L2_norm_sq_rep _ _ (hrep j),← real_toLp_norm_sq u hu]
    have hn := (L j).le_opNorm (hu.toLp u)
    nlinarith [norm_nonneg (L j (hu.toLp u)),mul_nonneg (norm_nonneg (L j)) (norm_nonneg (hu.toLp u))]
  refine ⟨fun j ↦ (memLp_congr_ae (hrep j)).mp (Lp.memLp _),?_⟩
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun j _ ↦ hj j)
  rw [← Finset.sum_mul] at hs
  have hi : 0 ≤ ∫ x, (u x)^2 := integral_nonneg (fun _ ↦ sq_nonneg _)
  dsimp only [B]
  nlinarith

end
end Yau

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Charts_SphereSquareDifferenceTestBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open MeasureTheory Yau.Geometry Set Filter
open scoped ContDiff Topology
noncomputable section

local instance sphereSquareDifferenceTestBoundMeasurable_ra06f3c_1 : MeasurableSpace Base := borel Base
local instance sphereSquareDifferenceTestBoundBorel_ra06f3c_1 : BorelSpace Base := ⟨rfl⟩
theorem sphere_square_difference_test_bound (d : SphereEnergyData) (p : Base)
    (z : SphereEnergyHilbert d) (eta theta : Yau.Jets.Coord → ℝ)
    (he : ContDiff ℝ ∞ eta) (ht : ContDiff ℝ ∞ theta)
    (hes : tsupport eta ⊆ realFinCube 4) (hts : tsupport theta ⊆ realFinCube 4)
    (hθ : ∀ x, 0 ≤ theta x ∧ theta x ≤ 1) (i : Fin 4) (h : ℝ)
    (h1 : ∀ x ∈ tsupport theta, eta =ᶠ[𝓝 x] (fun _ ↦ 1) ∧
      eta =ᶠ[𝓝 (x+Pi.single i h)] (fun _ ↦ 1)) :
    let q := Yau.realDifferenceQuotient i h
      (fun y ↦ eta y*(sphereEnergyL2Map d z) (sphereChartCoordMap p y))
    let T := fun j x ↦ theta x*Yau.realDifferenceQuotient i h (sphereChartDerivativeMap d p j z) x
    let R := fun j x ↦ Yau.coordPartial theta x j*q x
    let P := fun j x ↦ theta x*(T j x+2*R j x)
    let phi := fun x ↦ (theta x*theta x)*q x
    let b := Yau.realDifferenceQuotient i (-h) phi
    (∀ j : Fin 4, MemLp (T j) 2 volume ∧ MemLp (R j) 2 volume ∧ MemLp (P j) 2 volume) ∧
      MemLp b 2 volume ∧
      (∫ x, (b x)^2) ≤ 2*(∑ j, ∫ x, (T j x)^2)+8*(∑ j, ∫ x, (R j x)^2) := by
  dsimp only
  let q := Yau.realDifferenceQuotient i h
    (fun y ↦ eta y*(sphereEnergyL2Map d z) (sphereChartCoordMap p y))
  let T := fun j x ↦ theta x*Yau.realDifferenceQuotient i h (sphereChartDerivativeMap d p j z) x
  let R := fun j x ↦ Yau.coordPartial theta x j*q x
  let P := fun j x ↦ theta x*(T j x+2*R j x)
  let beta := fun x ↦ theta x*theta x
  have hbs : tsupport beta ⊆ realFinCube 4 := tsupport_mul_subset_left.trans hts
  have htc : HasCompactSupport theta := (realFinCube_isCompact 4).of_isClosed_subset (isClosed_tsupport theta) hts
  have hq : MemLp q 2 volume := Yau.realDifferenceQuotient_memLp i h _ (sphere_chart_cutoff_weak d p z eta he hes).1
  have hT (j : Fin 4) : MemLp (T j) 2 volume :=
    sphere_chart_weighted_difference_memLp d p z eta theta he ht.continuous hes htc i j h h1
  obtain ⟨_,_,hRb⟩ := Yau.real_compact_gradient_multiplier_bound theta ht htc
  have hR (j : Fin 4) : MemLp (R j) 2 volume := (hRb q hq).1 j
  have hrep (j : Fin 4) :
      (sphereDifferenceTestDerivativeMap d p eta beta he (ht.mul ht) hes hbs i h j z : Yau.Jets.Coord → ℝ)
      =ᵐ[volume] P j := by
    apply (sphereDifferenceTestDerivativeMap_ae d p eta beta he (ht.mul ht) hes hbs i h j z).trans
    exact Filter.Eventually.of_forall (sphere_difference_square_test_derivative d p z eta theta ht i j h h1)
  have hP (j : Fin 4) : MemLp (P j) 2 volume := (memLp_congr_ae (hrep j)).mp (Lp.memLp _)
  have hv := sphereDifferenceTestMap_ae d p eta beta he (ht.mul ht) hes hbs i h z
  have hd := Yau.realL2DifferenceMap_ae i (-h) _ _ hv
  have hbound := sphere_difference_test_difference_bound d p z eta beta he (ht.mul ht) hes hbs i h i (-h)
  rw [Yau.real_L2_norm_sq_rep _ _ hd,Yau.real_L2_norm_sq_rep _ _ (hrep i)] at hbound
  have hpw (x : Yau.Jets.Coord) : (P i x)^2 ≤ 2*(T i x)^2+8*(R i x)^2 := by
    have hθsq : (theta x)^2 ≤ 1 := by nlinarith [(hθ x).1,(hθ x).2]
    have hle : (P i x)^2 ≤ (T i x+2*R i x)^2 := by
      dsimp only [P]
      rw [mul_pow]
      exact mul_le_of_le_one_left (sq_nonneg _) hθsq
    nlinarith [sq_nonneg (T i x-2*R i x)]
  have hpi := integral_mono (hP i).integrable_sq
    (((hT i).integrable_sq.const_mul 2).add ((hR i).integrable_sq.const_mul 8)) hpw
  dsimp only [Pi.add_apply] at hpi
  rw [integral_add ((hT i).integrable_sq.const_mul 2) ((hR i).integrable_sq.const_mul 8),
    integral_const_mul,integral_const_mul] at hpi
  have hiT : (∫ x, (T i x)^2) ≤ ∑ j, ∫ x, (T j x)^2 :=
    Finset.single_le_sum (s := Finset.univ) (f := fun j : Fin 4 ↦ ∫ x, (T j x)^2)
      (fun j _ ↦ integral_nonneg (fun _ ↦ sq_nonneg _)) (Finset.mem_univ i)
  have hiR : (∫ x, (R i x)^2) ≤ ∑ j, ∫ x, (R j x)^2 :=
    Finset.single_le_sum (s := Finset.univ) (f := fun j : Fin 4 ↦ ∫ x, (R j x)^2)
      (fun j _ ↦ integral_nonneg (fun _ ↦ sq_nonneg _)) (Finset.mem_univ i)
  refine ⟨fun j ↦ ⟨hT j,hR j,hP j⟩,(memLp_congr_ae hd).mp (Lp.memLp _),?_⟩
  exact hbound.trans (hpi.trans (by linarith))

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Charts_SphereWeightedGradientBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open MeasureTheory Yau.Geometry Set
noncomputable section

theorem sphere_weighted_gradient_bound (d : SphereEnergyData) (p : Base) :
    ∃ C > 0, ∀ (z : SphereEnergyHilbert d) (theta : Yau.Jets.Coord → ℝ),
      Continuous theta → tsupport theta ⊆ realFinCube 4 →
      (∀ x, 0 ≤ theta x ∧ theta x ≤ 1) →
      (∀ j : Fin 4, MemLp (fun x ↦ theta x*(sphereChartDerivativeMap d p j z) x) 2 volume) ∧
      (∑ j : Fin 4, ∫ x, (theta x*(sphereChartDerivativeMap d p j z) x)^2) ≤ C*‖z‖^2 := by
  obtain ⟨C,hC,hb⟩ := sphere_chart_uniform_gradient_bound d p
  refine ⟨C,hC,fun z theta ht hs hθ ↦ ?_⟩
  have hj (j : Fin 4) := Yau.real_compact_localL2_product (realFinCube_isCompact 4)
    theta (sphereChartDerivativeMap d p j z) ht hs (Lp.memLp _)
  refine ⟨hj,le_trans (Finset.sum_le_sum (fun j _ ↦ ?_)) (hb z)⟩
  have he : (∫ x, (theta x*(sphereChartDerivativeMap d p j z) x)^2) =
      ∫ x in realFinCube 4, (theta x*(sphereChartDerivativeMap d p j z) x)^2 := by
    symm
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    rw [image_eq_zero_of_notMem_tsupport (fun ht ↦ hx (hs ht)),zero_mul,zero_pow (by decide)]
  rw [he]
  apply integral_mono (hj j).integrable_sq.integrableOn (Lp.memLp _).integrable_sq
  intro x
  have hsq : (theta x)^2 ≤ 1 := by nlinarith [(hθ x).1,(hθ x).2]
  dsimp only
  rw [mul_pow]
  exact mul_le_of_le_one_left (sq_nonneg _) hsq

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_RealDifferenceEnergyBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau
open MeasureTheory
noncomputable section

theorem real_integral_young {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (u v : α → ℝ) (hu : MemLp u 2 μ) (hv : MemLp v 2 μ)
    (e : ℝ) (he : 0 < e) :
    -(∫ x, u x*v x ∂μ) ≤ e*(∫ x, (v x)^2 ∂μ)+(1/e)*(∫ x, (u x)^2 ∂μ) := by
  rw [← integral_neg,← integral_const_mul,← integral_const_mul,
    ← integral_add (hv.integrable_sq.const_mul e) (hu.integrable_sq.const_mul (1/e))]
  apply integral_mono (hu.integrable_mul hv).neg
    ((hv.integrable_sq.const_mul e).add (hu.integrable_sq.const_mul (1/e)))
  intro x
  change -(u x*v x) ≤ e*(v x)^2+(1/e)*(u x)^2
  simpa only [one_mul,one_pow,mul_comm (v x) (u x)] using
    real_young_coefficient e 1 1 (v x) (u x) he (by norm_num) (by norm_num)

theorem real_difference_energy_absorption {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (m K : ℝ) (hm : 0 < m) (T V R D P : Fin 4 → α → ℝ) (F b : α → ℝ)
    (hT : ∀ j, MemLp (T j) 2 μ) (hV : ∀ j, MemLp (V j) 2 μ)
    (hR : ∀ j, MemLp (R j) 2 μ) (hDP : ∀ j, Integrable (fun x ↦ D j x*P j x) μ)
    (hF : MemLp F 2 μ) (hb : MemLp b 2 μ)
    (hlow : ∀ x, (m/2)*(∑ j, (T j x)^2) ≤
      (∑ j, D j x*P j x)+K*((∑ j, (V j x)^2)+(∑ j, (R j x)^2)))
    (htest : (∫ x, (b x)^2 ∂μ) ≤
      2*(∑ j, ∫ x, (T j x)^2 ∂μ)+8*(∑ j, ∫ x, (R j x)^2 ∂μ))
    (heq : (∑ j, ∫ x, D j x*P j x ∂μ)=-(∫ x, F x*b x ∂μ)) :
    (∑ j, ∫ x, (T j x)^2 ∂μ) ≤ (4/m)*
      ((8/m)*(∫ x, (F x)^2 ∂μ)+K*(∑ j, ∫ x, (V j x)^2 ∂μ)+
        (K+m)*(∑ j, ∫ x, (R j x)^2 ∂μ)) := by
  have hiT := integrable_finsetSum Finset.univ (fun j _ ↦ (hT j).integrable_sq)
  have hiV := integrable_finsetSum Finset.univ (fun j _ ↦ (hV j).integrable_sq)
  have hiR := integrable_finsetSum Finset.univ (fun j _ ↦ (hR j).integrable_sq)
  have hiD := integrable_finsetSum Finset.univ (fun j _ ↦ hDP j)
  have hiVR : Integrable (fun x ↦ (∑ j, (V j x)^2)+(∑ j, (R j x)^2)) μ := hiV.add hiR
  have hiK : Integrable (fun x ↦ K*((∑ j, (V j x)^2)+(∑ j, (R j x)^2))) μ := hiVR.const_mul K
  have hl := integral_mono (hiT.const_mul (m/2)) (hiD.add hiK) hlow
  dsimp only [Pi.add_apply] at hl
  rw [integral_const_mul,integral_add hiD hiK,
    integral_const_mul,integral_add hiV hiR,
    integral_finsetSum _ (fun j _ ↦ (hT j).integrable_sq),
    integral_finsetSum _ (fun j _ ↦ (hV j).integrable_sq),
    integral_finsetSum _ (fun j _ ↦ (hR j).integrable_sq),
    integral_finsetSum _ (fun j _ ↦ hDP j),heq] at hl
  have hy := real_integral_young μ F b hF hb (m/8) (by positivity)
  have hb' := mul_le_mul_of_nonneg_left htest (show 0 ≤ m/8 by positivity)
  have hc : 1/(m/8)=8/m := by ring
  rw [hc] at hy
  have hpre : (m/4)*(∑ j, ∫ x, (T j x)^2 ∂μ) ≤
      (8/m)*(∫ x, (F x)^2 ∂μ)+K*(∑ j, ∫ x, (V j x)^2 ∂μ)+
        (K+m)*(∑ j, ∫ x, (R j x)^2 ∂μ) := by linarith
  have hscale := mul_le_mul_of_nonneg_left hpre (show 0 ≤ 4/m by positivity)
  have hcancel : (4/m)*(m/4)=1 := by field_simp
  simpa only [← mul_assoc,hcancel,one_mul] using hscale

end
end Yau

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Charts_SphereInteriorGradientDifferenceBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open MeasureTheory Yau.Geometry Set Filter
open scoped ContDiff Topology
noncomputable section

local instance sphereInteriorGradientDifferenceBoundMeasurable_ra06f3c_1 : MeasurableSpace Base := borel Base
local instance sphereInteriorGradientDifferenceBoundBorel_ra06f3c_1 : BorelSpace Base := ⟨rfl⟩
theorem sphere_resolvent_interior_gradient_difference_bound_oai (d : SphereEnergyData) (p : Base) :
    ∃ C0 > 0, ∀ (f : SphereWeightedL2 d) (i : Fin 4) (h : ℝ), |h| ≤ 1/8 →
      (∀ j : Fin 4, MemLp
        (Yau.realDifferenceQuotient i h (sphereChartDerivativeMap d p j (sphereWeakSolution d f))) 2
        (volume.restrict (Yau.realCenteredCube 4 (1/2)))) ∧
      (∑ j : Fin 4, ∫ x in Yau.realCenteredCube 4 (1/2),
        (Yau.realDifferenceQuotient i h (sphereChartDerivativeMap d p j (sphereWeakSolution d f)) x)^2)
        ≤ C0*(‖f‖^2+‖sphereWeakSolution d f‖^2) := by
  obtain ⟨eta,theta,he,ht,hec,htc,hes,hts,heb,htb,ht1,he1⟩ := Yau.real_interior_difference_cutoffs
  have hes' : tsupport eta ⊆ realFinCube 4 := hes
  have hts' : tsupport theta ⊆ realFinCube 4 := hts.trans (Yau.realCenteredCube_mono (by norm_num))
  obtain ⟨m,hm,K,hK,hcoer⟩ := sphere_difference_pointwise_coercivity d p
  obtain ⟨CV,hCV,hVb⟩ := sphere_weighted_gradient_bound d p
  obtain ⟨CQ,hCQ,hQb⟩ := sphere_cutoff_uniform_H1_bound d p eta he hes'
  obtain ⟨CR,hCR,hRb⟩ := Yau.real_compact_gradient_multiplier_bound theta ht htc
  obtain ⟨CF,hCF,hFb⟩ := sphere_chart_forcingZero_uniform_bound d p
  let C0 : ℝ := (4/m)*((8/m)*CF+K*CV+(K+m)*(CR*CQ))
  refine ⟨C0,by dsimp [C0] <;> positivity,fun f i h hh ↦ ?_⟩
  let z := sphereWeakSolution d f
  let v := fun x ↦ eta x*(sphereEnergyL2Map d z) (sphereChartCoordMap p x)
  let q := Yau.realDifferenceQuotient i h v
  let T := fun j x ↦ theta x*Yau.realDifferenceQuotient i h (sphereChartDerivativeMap d p j z) x
  let V := fun j x ↦ theta x*(sphereChartDerivativeMap d p j z) x
  let R := fun j x ↦ Yau.coordPartial theta x j*q x
  let P := fun j x ↦ theta x*(T j x+2*R j x)
  let beta := fun x ↦ theta x*theta x
  let phi := fun x ↦ beta x*q x
  let b := Yau.realDifferenceQuotient i (-h) phi
  let D := fun j ↦ Yau.realDifferenceQuotient i h (sphereChartFluxZero d p z j)
  let F := sphereChartForcingZero d p f
  have hlocal := he1 i h hh
  have htest := sphere_square_difference_test_bound d p z eta theta he ht hes' hts' htb i h hlocal
  change (∀ j, MemLp (T j) 2 volume ∧ MemLp (R j) 2 volume ∧ MemLp (P j) 2 volume) ∧
    MemLp b 2 volume ∧ (∫ x, (b x)^2) ≤ 2*(∑ j, ∫ x, (T j x)^2)+8*(∑ j, ∫ x, (R j x)^2) at htest
  have hV := hVb z theta ht.continuous hts' htb
  have hq : MemLp q 2 volume := (sphere_chart_cutoff_difference_bound d p z eta he hes' i h).1
  have hRb' := hRb q hq
  have hRbound : (∑ j, ∫ x, (R j x)^2) ≤ (CR*CQ)*‖z‖^2 := by
    exact hRb'.2.trans (by simpa only [mul_assoc] using
      mul_le_mul_of_nonneg_left (hQb z i h).2 hCR.le)
  have hbs : tsupport beta ⊆ Yau.realCenteredCube 4 (3/4) := tsupport_mul_subset_left.trans hts
  have hlit := sphere_resolvent_H1_difference_test_literal d f p z eta beta he (ht.mul ht)
    hes' (3/4) (by norm_num) hbs i h (by linarith)
  dsimp only at hlit
  have hDP (j : Fin 4) : Integrable (fun x ↦ D j x*P j x) := by
    apply (hlit.2.2.1 j).congr
    apply Filter.Eventually.of_forall
    intro x
    exact congrArg (fun t : ℝ ↦ D j x*t)
      (sphere_difference_square_test_derivative d p z eta theta ht i j h hlocal x)
  have heq : (∑ j, ∫ x, D j x*P j x)=-(∫ x, F x*b x) := by
    rw [← hlit.2.2.2.2]
    apply Finset.sum_congr rfl
    intro j _
    apply integral_congr_ae
    apply Filter.Eventually.of_forall
    intro x
    exact (congrArg (fun t : ℝ ↦ D j x*t)
      (sphere_difference_square_test_derivative d p z eta theta ht i j h hlocal x)).symm
  have henergy := Yau.real_difference_energy_absorption volume m K hm T V R D P F b
    (fun j ↦ (htest.1 j).1) hV.1 (fun j ↦ (htest.1 j).2.1) hDP
    (sphereChartForcingZero_memLp d p f) htest.2.1
    (hcoer z eta theta ht hts i h hh hlocal) htest.2.2 heq
  have hnorm : ‖z‖^2 ≤ ‖f‖^2+‖z‖^2 := by nlinarith [sq_nonneg ‖f‖]
  have hglobal : (∑ j, ∫ x, (T j x)^2) ≤ C0*(‖f‖^2+‖z‖^2) := by
    apply henergy.trans
    have h1 := mul_le_mul_of_nonneg_left (hFb f) (show 0 ≤ 8/m by positivity)
    have h2 := mul_le_mul_of_nonneg_left (hV.2.trans (mul_le_mul_of_nonneg_left hnorm hCV.le)) hK.le
    have h3 := mul_le_mul_of_nonneg_left (hRbound.trans
      (mul_le_mul_of_nonneg_left hnorm (mul_nonneg hCR.le hCQ.le))) (add_nonneg hK.le hm.le)
    have ht' := mul_le_mul_of_nonneg_left (add_le_add (add_le_add h1 h2) h3)
      (show 0 ≤ 4/m by positivity)
    convert ht' using 1
    all_goals try with_reducible_and_instances rfl
    dsimp [C0,z]
    ring
  refine ⟨fun j ↦ sphere_chart_interior_difference_memLp d p z i j h hh,?_⟩
  apply le_trans (Finset.sum_le_sum (fun j _ ↦ ?_)) hglobal
  have hEq : (∫ x in Yau.realCenteredCube 4 (1/2),
      (Yau.realDifferenceQuotient i h (sphereChartDerivativeMap d p j z) x)^2) =
      ∫ x in Yau.realCenteredCube 4 (1/2), (T j x)^2 := by
    apply setIntegral_congr_fun (Yau.realCenteredCube_isCompact 4 (1/2)).measurableSet
    intro x hx
    dsimp [T]
    rw [(ht1 x hx).eq_of_nhds,one_mul]
  rw [hEq]
  have hmono := setIntegral_mono_set (s := Yau.realCenteredCube 4 (1/2)) (t := Set.univ) ((htest.1 j).1.integrable_sq.integrableOn (s := Set.univ))
    (Filter.Eventually.of_forall (fun _ ↦ sq_nonneg _))
    (Filter.Eventually.of_forall (fun x _ ↦ Set.mem_univ x))
  simpa only [Measure.restrict_univ] using hmono

end
end Yau.Target

end OAI
end

theorem solution : type_of% @OAI.Yau.Target.sphere_resolvent_interior_gradient_difference_bound_oai := @OAI.Yau.Target.sphere_resolvent_interior_gradient_difference_bound_oai
