-- Prove2me | solution 1 for OAI.Yau.Target.sphere_interior_localized_energy
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T00:34:18.877951+00:00
-- url     : https://prove2.me/submissions/9a4c79b1-5235-4c9f-b852-49dba597e4a0

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
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.Completion
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.Normed.Lp.SmoothApprox
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

local instance sphereChartDivergenceDataMeasurable_ra9ec27_1 : MeasurableSpace Base := borel Base
local instance sphereChartDivergenceDataBorel_ra9ec27_1 : BorelSpace Base := ⟨rfl⟩
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

open MeasureTheory Set
open scoped ContDiff

theorem real_divergence_forcing_difference_equation {n : ℕ}
    (A G : Fin n → Coord n → ℝ) (F : Coord n → ℝ)
    (hA : ∀ j, MemLp (A j) 2 volume) (hG : ∀ j, MemLp (G j) 2 volume)
    (hF : MemLp F 2 volume) (R r : ℝ) (hr : r ≤ R)
    (heq : ∀ psi : Coord n → ℝ, ContDiff ℝ ∞ psi → HasCompactSupport psi →
      tsupport psi ⊆ realCenteredCube n R →
      (∑ j, ∫ x, A j x*coordPartial psi x j) =
        (∫ x, F x*psi x)-(∑ j, ∫ x, G j x*coordPartial psi x j))
    (i : Fin n) (h : ℝ) (hh : |h| ≤ R-r)
    (phi : Coord n → ℝ) (hp : ContDiff ℝ ∞ phi) (hc : HasCompactSupport phi)
    (hs : tsupport phi ⊆ realCenteredCube n r) :
    (∀ j, Integrable (fun x ↦ realDifferenceQuotient i h (A j) x*coordPartial phi x j) ∧
      Integrable (fun x ↦ realDifferenceQuotient i h (G j) x*coordPartial phi x j)) ∧
    Integrable (fun x ↦ F x*realDifferenceQuotient i (-h) phi x) ∧
    (∑ j, ∫ x, realDifferenceQuotient i h (A j) x*coordPartial phi x j) =
      -(∫ x, F x*realDifferenceQuotient i (-h) phi x)-
        (∑ j, ∫ x, realDifferenceQuotient i h (G j) x*coordPartial phi x j) := by
  have ht := heq (realDifferenceQuotient i (-h) phi)
    (realDifferenceQuotient_smooth i (-h) phi hp)
    (realDifferenceQuotient_compact i (-h) phi hc)
    (realDifferenceQuotient_tsupport i (-h) phi (realCenteredCube_isCompact n R).isClosed
      (hs.trans (realCenteredCube_mono hr))
      (fun x hx ↦ realCenteredCube_shift i (by simpa only [abs_neg] using hh) (hs hx)))
  have hd (j : Fin n) := real_compact_continuous_memLp _ (real_coordPartial_smooth phi hp j).continuous
    (hc.fderiv_apply ℝ (Pi.single j 1))
  have hda (j : Fin n) := real_differenceQuotient_pairing i h (A j) _ (hA j) (hd j)
  have hdg (j : Fin n) := real_differenceQuotient_pairing i h (G j) _ (hG j) (hd j)
  have hi : Integrable (fun x ↦ F x*realDifferenceQuotient i (-h) phi x) :=
    hF.integrable_mul (realDifferenceQuotient_memLp i (-h) phi
      (real_compact_continuous_memLp phi hp.continuous hc))
  refine ⟨fun j ↦ ⟨(hda j).1,(hdg j).1⟩,hi,?_⟩
  simp only [realDifferenceQuotient_partial i _ (-h) phi hp] at ht
  simp only [(hda _).2.2,(hdg _).2.2,Finset.sum_neg_distrib]
  linarith only [ht]

theorem real_ae_translation_endpoints {n : ℕ} {S : Set (Coord n)}
    (hS : MeasurableSet S) (P : Coord n → Prop)
    (hP : ∀ᵐ x ∂volume.restrict S, P x) (v : Coord n) :
    ∀ᵐ x ∂volume, (x ∈ S → P x) ∧ (x+v ∈ S → P (x+v)) := by
  have hbase : ∀ᵐ x ∂volume, x ∈ S → P x := (ae_restrict_iff' hS).mp hP
  have hshift := (measurePreserving_add_right (G := Coord n) volume v).quasiMeasurePreserving.ae hbase
  filter_upwards [hbase,hshift] with x hx hy
  exact ⟨hx,hy⟩

theorem real_local_difference_weak_derivative {n : ℕ} (u g : Coord n → ℝ)
    (hu : MemLp u 2 volume) (hg : MemLp g 2 volume) (R r : ℝ) (hr : r ≤ R)
    (j : Fin n)
    (hw : ∀ psi : Coord n → ℝ, ContDiff ℝ ∞ psi → HasCompactSupport psi →
      tsupport psi ⊆ realCenteredCube n R →
      (∫ x, u x*coordPartial psi x j)=-(∫ x, g x*psi x))
    (i : Fin n) (h : ℝ) (hh : |h| ≤ R-r)
    (psi : Coord n → ℝ) (hp : ContDiff ℝ ∞ psi) (hc : HasCompactSupport psi)
    (hs : tsupport psi ⊆ realCenteredCube n r) :
    (∫ x, realDifferenceQuotient i h u x*coordPartial psi x j) =
      -(∫ x, realDifferenceQuotient i h g x*psi x) := by
  have hd := real_compact_continuous_memLp _ (real_coordPartial_smooth psi hp j).continuous
    (hc.fderiv_apply ℝ (Pi.single j 1))
  have hv := real_compact_continuous_memLp psi hp.continuous hc
  have ht := hw (realDifferenceQuotient i (-h) psi)
    (realDifferenceQuotient_smooth i (-h) psi hp)
    (realDifferenceQuotient_compact i (-h) psi hc)
    (realDifferenceQuotient_tsupport i (-h) psi (realCenteredCube_isCompact n R).isClosed
      (hs.trans (realCenteredCube_mono hr))
      (fun x hx ↦ realCenteredCube_shift i (by simpa only [abs_neg] using hh) (hs hx)))
  simp only [realDifferenceQuotient_partial i j (-h) psi hp] at ht
  rw [(real_differenceQuotient_pairing i h u _ hu hd).2.2,
    (real_differenceQuotient_pairing i h g psi hg hv).2.2]
  linarith only [ht]

end Yau

end

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

local instance sphereDifferenceCoercivityMeasurable_ra9ec27_1 : MeasurableSpace Base := borel Base
local instance sphereDifferenceCoercivityBorel_ra9ec27_1 : BorelSpace Base := ⟨rfl⟩
theorem sphereChartPrincipalDensity_entries_bound (d : SphereEnergyData) (p : Base) :
    ∃ B > 0, ∀ x ∈ realFinCube 4, ∀ a j : Fin 4,
      |sphereChartPrincipalDensity d p x a j| ≤ B := by
  have hc : Continuous (sphereChartPrincipalDensity d p) := continuous_pi (fun a ↦
    continuous_pi (fun j ↦ (sphereChartPrincipalDensity_smooth d p a j).continuous))
  obtain ⟨B,hB,hb⟩ := ((realFinCube_isCompact 4).image hc).isBounded.exists_pos_norm_le
  refine ⟨B,hB,fun x hx a j ↦ ?_⟩
  exact (norm_le_pi_norm (sphereChartPrincipalDensity d p x a) j).trans
    ((norm_le_pi_norm (sphereChartPrincipalDensity d p x) a).trans (hb _ ⟨x,hx,rfl⟩))

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_RealInteriorFluxDifference
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau
open MeasureTheory Set
noncomputable section

theorem real_interior_flux_difference_ae {n : ℕ} (Q : Set (Coord n))
    (C : Coord n → Fin n → Fin n → ℝ) (P V : Fin n → Coord n → ℝ)
    (hsame : ∀ a, P a =ᵐ[volume.restrict (interior Q)] V a)
    (i : Fin n) (h : ℝ) :
    ∀ᵐ x ∂volume, x ∈ interior Q → x+Pi.single i h ∈ interior Q → ∀ j,
      realDifferenceQuotient i h (Q.indicator (fun y ↦ ∑ a, C y a j*P a y)) x =
        ∑ a, (C (x+Pi.single i h) a j*realDifferenceQuotient i h (Q.indicator (V a)) x+
          realDifferenceQuotient i h (fun y ↦ C y a j) x*(Q.indicator (V a)) x) := by
  have hall : ∀ᵐ x ∂volume.restrict (interior Q), ∀ a, P a x=V a x := ae_all_iff.mpr hsame
  have ht := real_ae_translation_endpoints isOpen_interior.measurableSet
    (fun x ↦ ∀ a, P a x=V a x) hall (Pi.single i h)
  filter_upwards [ht] with x hx
  intro hxi hti j
  have hxe := hx.1 hxi
  have hte := hx.2 hti
  have hxQ : x ∈ Q := interior_subset hxi
  have htQ : x+Pi.single i h ∈ Q := interior_subset hti
  have hid : realDifferenceQuotient i h (Q.indicator (fun y ↦ ∑ a, C y a j*P a y)) x =
      realDifferenceQuotient i h (fun y ↦ ∑ a, C y a j*(Q.indicator (V a)) y) x := by
    simp only [realDifferenceQuotient,indicator_of_mem hxQ,indicator_of_mem htQ,hxe,hte]
  rw [hid,realDifferenceQuotient_sum]
  apply Finset.sum_congr rfl
  intro a _
  exact realDifferenceQuotient_mul i h _ _ x

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
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_RealSquareCutoffWeakGradient
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau
open MeasureTheory Set
open scoped ContDiff
noncomputable section

theorem real_integral_pairing_restrict {n : ℕ} {D : Set (Coord n)}
    (a b : Coord n → ℝ) (hs : tsupport b ⊆ D) :
    (∫ x, a x*b x) = ∫ x in D, a x*b x := by
  symm
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro x hx
  rw [image_eq_zero_of_notMem_tsupport (fun ht ↦ hx (hs ht)),mul_zero]

theorem real_square_cutoff_weak_gradient {n : ℕ} {D : Set (Coord n)} (hD : IsCompact D)
    (eta u : Coord n → ℝ) (g : Fin n → Coord n → ℝ)
    (hu : MemLp u 2 (volume.restrict D)) (hg : ∀ j, MemLp (g j) 2 (volume.restrict D))
    (he : ContDiff ℝ ∞ eta) (hs : tsupport eta ⊆ D)
    (hw : ∀ j, ∀ psi : Coord n → ℝ, ContDiff ℝ ∞ psi → HasCompactSupport psi → tsupport psi ⊆ D →
      (∫ x in D, u x*coordPartial psi x j)=-(∫ x in D, g j x*psi x)) :
    MemLp (realSquareCutoff eta u) 2 volume ∧
    (∀ j, MemLp (realSquareCutoffGradient eta u g j) 2 volume) ∧
    (∀ x, x ∉ tsupport eta → realSquareCutoff eta u x=0) ∧
    (∀ j x, x ∉ tsupport eta → realSquareCutoffGradient eta u g j x=0) ∧
    ∀ j, ∀ psi : Coord n → ℝ, ContDiff ℝ ∞ psi → HasCompactSupport psi →
      (∫ x, realSquareCutoff eta u x*coordPartial psi x j)=
        -(∫ x, realSquareCutoffGradient eta u g j x*psi x) := by
  have he2 : ContDiff ℝ ∞ (fun x ↦ eta x^2) := he.pow 2
  have hs2 : tsupport (fun x ↦ eta x^2) ⊆ D := by
    simpa only [pow_two] using (tsupport_mul_subset_left (f := eta) (g := eta)).trans hs
  have hd (x : Coord n) (j : Fin n) : coordPartial (fun y ↦ eta y^2) x j =
      2*eta x*coordPartial eta x j := by
    simp only [pow_two,real_coordPartial_mul eta eta he he]
    ring
  have hbase := real_compact_localL2_product hD (fun x ↦ eta x^2) u he2.continuous hs2 hu
  have hh (j : Fin n) := real_local_weak_cutoff hD u (g j) (fun x ↦ eta x^2)
    hu (hg j) he2 hs2 j (hw j)
  simp only [hd] at hh
  refine ⟨hbase,fun j ↦ (hh j).2.1,?_,?_,fun j psi hp hc ↦ ((hh j).2.2 psi hp hc).2.2⟩
  · intro x hx
    simp only [realSquareCutoff,image_eq_zero_of_notMem_tsupport hx,zero_pow (by decide : 2≠0),zero_mul]
  · intro j x hx
    simp only [realSquareCutoffGradient,image_eq_zero_of_notMem_tsupport hx,
      zero_pow (by decide : 2≠0),zero_mul,mul_zero,add_zero]

theorem real_square_cutoff_difference_weak_gradient {n : ℕ}
    (eta u : Coord n → ℝ) (g : Fin n → Coord n → ℝ)
    (hu : MemLp u 2 volume) (hg : ∀ j, MemLp (g j) 2 volume)
    (R r : ℝ) (hr : r ≤ R) (he : ContDiff ℝ ∞ eta)
    (hs : tsupport eta ⊆ realCenteredCube n r)
    (hw : ∀ j, ∀ psi : Coord n → ℝ, ContDiff ℝ ∞ psi → HasCompactSupport psi →
      tsupport psi ⊆ realCenteredCube n R →
      (∫ x, u x*coordPartial psi x j)=-(∫ x, g j x*psi x))
    (i : Fin n) (h : ℝ) (hh : |h| ≤ R-r) :
    MemLp (realSquareCutoff eta (realDifferenceQuotient i h u)) 2 volume ∧
    (∀ j, MemLp (realSquareCutoffGradient eta (realDifferenceQuotient i h u)
      (fun l ↦ realDifferenceQuotient i h (g l)) j) 2 volume) ∧
    (∀ x, x ∉ tsupport eta → realSquareCutoff eta (realDifferenceQuotient i h u) x=0) ∧
    (∀ j x, x ∉ tsupport eta → realSquareCutoffGradient eta (realDifferenceQuotient i h u)
      (fun l ↦ realDifferenceQuotient i h (g l)) j x=0) ∧
    ∀ j, ∀ psi : Coord n → ℝ, ContDiff ℝ ∞ psi → HasCompactSupport psi →
      (∫ x, realSquareCutoff eta (realDifferenceQuotient i h u) x*coordPartial psi x j)=
        -(∫ x, realSquareCutoffGradient eta (realDifferenceQuotient i h u)
          (fun l ↦ realDifferenceQuotient i h (g l)) j x*psi x) := by
  apply real_square_cutoff_weak_gradient (realCenteredCube_isCompact n r) eta
    (realDifferenceQuotient i h u) (fun j ↦ realDifferenceQuotient i h (g j))
    ((realDifferenceQuotient_memLp i h u hu).restrict _)
    (fun j ↦ (realDifferenceQuotient_memLp i h (g j) (hg j)).restrict _) he hs
  intro j psi hp hc hpsi
  have ht := real_local_difference_weak_derivative u (g j) hu (hg j) R r hr j (hw j)
    i h hh psi hp hc hpsi
  rw [real_integral_pairing_restrict (realDifferenceQuotient i h u) (fun x ↦ coordPartial psi x j)
    ((tsupport_fderiv_apply_subset ℝ (Pi.single j 1)).trans hpsi),
    real_integral_pairing_restrict (realDifferenceQuotient i h (g j)) psi hpsi] at ht
  exact ht

end
end Yau

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Charts_SphereInteriorFluxCoercivity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open MeasureTheory Yau.Geometry Set
open scoped ContDiff
noncomputable section

theorem sphere_interior_flux_difference_coercivity (d : SphereEnergyData) (p : Base) :
    ∃ m > 0, ∃ K > 0,
      ∀ (Q : Set Yau.Jets.Coord) (_ : Q ⊆ realFinCube 4)
        (P0 V0 : Fin 4 → Yau.Jets.Coord → ℝ),
        (∀ a, P0 a =ᵐ[volume.restrict (interior Q)] V0 a) →
        ∀ (i : Fin 4) (h : ℝ) (eta q : Yau.Jets.Coord → ℝ),
          (∀ x ∈ tsupport eta, x ∈ interior Q ∧ x+Pi.single i h ∈ interior Q) →
        let V := fun a ↦ Q.indicator (V0 a)
        let A := fun j ↦ Q.indicator (fun x ↦ ∑ a, sphereChartPrincipalDensity d p x a j*P0 a x)
        let T := fun a x ↦ eta x*Yau.realDifferenceQuotient i h (V a) x
        let W := fun a x ↦ eta x*V a x
        let R := fun a x ↦ Yau.coordPartial eta x a*q x
        let P := Yau.realSquareCutoffGradient eta q (fun a ↦ Yau.realDifferenceQuotient i h (V a))
        ∀ᵐ x ∂volume, (m/2)*(∑ a, (T a x)^2) ≤
          (∑ j, Yau.realDifferenceQuotient i h (A j) x*P j x)+
            K*((∑ a, (W a x)^2)+(∑ a, (R a x)^2)) := by
  obtain ⟨m,hm,C,hC,hell⟩ := sphereChartPrincipalDensity_elliptic d p (realFinCube_isCompact 4)
  obtain ⟨B,hB,hb⟩ := sphereChartPrincipalDensity_entries_bound d p
  obtain ⟨D,hD,hd⟩ := sphereChartPrincipalDensity_difference_bound d p
  let E := B+D
  have hE : 0 < E := by dsimp [E] <;> positivity
  refine ⟨m,hm,256*E^2/m+4*E,by positivity,?_⟩
  intro Q hQ P0 V0 hsame i h eta q hend
  dsimp only
  have hflux := Yau.real_interior_flux_difference_ae Q (sphereChartPrincipalDensity d p) P0 V0 hsame i h
  filter_upwards [hflux] with x hflux
  let V := fun a ↦ Q.indicator (V0 a)
  let A := fun j ↦ Q.indicator (fun y ↦ ∑ a, sphereChartPrincipalDensity d p y a j*P0 a y)
  let T : Fin 4 → ℝ := fun a ↦ eta x*Yau.realDifferenceQuotient i h (V a) x
  let W : Fin 4 → ℝ := fun a ↦ eta x*V a x
  let R : Fin 4 → ℝ := fun a ↦ Yau.coordPartial eta x a*q x
  by_cases hx : x ∈ tsupport eta
  · have hxint := (hend x hx).1
    have htint := (hend x hx).2
    have hx0 : x ∈ realFinCube 4 := hQ (interior_subset hxint)
    have hxt : x+Pi.single i h ∈ realFinCube 4 := hQ (interior_subset htint)
    have hmB (a j : Fin 4) : |sphereChartPrincipalDensity d p (x+Pi.single i h) a j| ≤ E :=
      (hb _ hxt a j).trans (by dsimp [E] <;> linarith)
    have hnB (a j : Fin 4) :
        |Yau.realDifferenceQuotient i h (fun y ↦ sphereChartPrincipalDensity d p y a j) x| ≤ E :=
      (hd a j i h x hx0 hxt).trans (by dsimp [E] <;> linarith)
    have hellT := (hell (x+Pi.single i h) hxt T).1
    have hc := Yau.real_difference_coercivity m E hm hE.le
    specialize hc (sphereChartPrincipalDensity d p (x+Pi.single i h))
      (fun a j ↦ Yau.realDifferenceQuotient i h (fun y ↦ sphereChartPrincipalDensity d p y a j) x)
      T W R
    specialize hc hmB hnB hellT
    have heq (j : Fin 4) : Yau.realDifferenceQuotient i h (A j) x*
        Yau.realSquareCutoffGradient eta q (fun a ↦ Yau.realDifferenceQuotient i h (V a)) j x =
        (∑ a, (sphereChartPrincipalDensity d p (x+Pi.single i h) a j*T a+
          Yau.realDifferenceQuotient i h (fun y ↦ sphereChartPrincipalDensity d p y a j) x*W a))*(T j+2*R j) := by
      have hgrad : Yau.realSquareCutoffGradient eta q
          (fun a ↦ Yau.realDifferenceQuotient i h (V a)) j x=eta x*(T j+2*R j) := by
        dsimp [Yau.realSquareCutoffGradient,T,R]
        ring
      rw [hgrad,hflux hxint htint j,← mul_assoc]
      congr 1
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro a _
      dsimp [T,W]
      ring
    simp_rw [← heq] at hc
    exact hc
  · have hz := image_eq_zero_of_notMem_tsupport hx
    have hdz (j : Fin 4) : Yau.coordPartial eta x j=0 :=
      image_eq_zero_of_notMem_tsupport (f := fun y ↦ Yau.coordPartial eta y j)
        (fun hj ↦ hx (tsupport_fderiv_apply_subset ℝ (Pi.single j 1) hj))
    simp only [Yau.realSquareCutoffGradient,hz,hdz,zero_mul,mul_zero,
      zero_pow (by decide : (2:ℕ)≠0),Finset.sum_const_zero,add_zero,le_refl]

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

end
end Yau

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_RealDivergenceEnergyAE
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau
open MeasureTheory
noncomputable section

theorem real_divergence_difference_energy_absorption_ae {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (m K : ℝ) (hm : 0 < m)
    (T V R D P G : Fin 4 → α → ℝ) (F b : α → ℝ)
    (hT : ∀ j, MemLp (T j) 2 μ) (hV : ∀ j, MemLp (V j) 2 μ)
    (hR : ∀ j, MemLp (R j) 2 μ) (hP : ∀ j, MemLp (P j) 2 μ)
    (hG : ∀ j, MemLp (G j) 2 μ)
    (hDP : ∀ j, Integrable (fun x ↦ D j x*P j x) μ)
    (hF : MemLp F 2 μ) (hb : MemLp b 2 μ)
    (hlow : ∀ᵐ x ∂μ, (m/2)*(∑ j, (T j x)^2) ≤
      (∑ j, D j x*P j x)+K*((∑ j, (V j x)^2)+(∑ j, (R j x)^2)))
    (htest : (∫ x, (b x)^2 ∂μ) ≤
      2*(∑ j, ∫ x, (T j x)^2 ∂μ)+8*(∑ j, ∫ x, (R j x)^2 ∂μ))
    (hPtest : (∑ j, ∫ x, (P j x)^2 ∂μ) ≤
      2*(∑ j, ∫ x, (T j x)^2 ∂μ)+8*(∑ j, ∫ x, (R j x)^2 ∂μ))
    (heq : (∑ j, ∫ x, D j x*P j x ∂μ)=-(∫ x, F x*b x ∂μ)-
      ∑ j, ∫ x, G j x*P j x ∂μ) :
    (∑ j, ∫ x, (T j x)^2 ∂μ) ≤ (4/m)*
      ((16/m)*((∫ x, (F x)^2 ∂μ)+(∑ j, ∫ x, (G j x)^2 ∂μ))+
        K*(∑ j, ∫ x, (V j x)^2 ∂μ)+(K+m)*(∑ j, ∫ x, (R j x)^2 ∂μ)) := by
  have hiT := integrable_finsetSum Finset.univ (fun j _ ↦ (hT j).integrable_sq)
  have hiV := integrable_finsetSum Finset.univ (fun j _ ↦ (hV j).integrable_sq)
  have hiR := integrable_finsetSum Finset.univ (fun j _ ↦ (hR j).integrable_sq)
  have hiD := integrable_finsetSum Finset.univ (fun j _ ↦ hDP j)
  have hiVR : Integrable (fun x ↦ (∑ j, (V j x)^2)+(∑ j, (R j x)^2)) μ := hiV.add hiR
  have hiK : Integrable (fun x ↦ K*((∑ j, (V j x)^2)+(∑ j, (R j x)^2))) μ := hiVR.const_mul K
  have hl := integral_mono_ae (hiT.const_mul (m/2)) (hiD.add hiK) hlow
  dsimp only [Pi.add_apply] at hl
  rw [integral_const_mul,integral_add hiD hiK,integral_const_mul,integral_add hiV hiR,
    integral_finsetSum _ (fun j _ ↦ (hT j).integrable_sq),
    integral_finsetSum _ (fun j _ ↦ (hV j).integrable_sq),
    integral_finsetSum _ (fun j _ ↦ (hR j).integrable_sq),
    integral_finsetSum _ (fun j _ ↦ hDP j),heq] at hl
  have hy := real_integral_young μ F b hF hb (m/16) (by positivity)
  have hys := Finset.sum_le_sum (s := Finset.univ) (fun j _ ↦
    real_integral_young μ (G j) (P j) (hG j) (hP j) (m/16) (by positivity))
  simp only [Finset.sum_neg_distrib,Finset.sum_add_distrib,← Finset.mul_sum] at hys
  have hb' := mul_le_mul_of_nonneg_left htest (show 0 ≤ m/16 by positivity)
  have hP' := mul_le_mul_of_nonneg_left hPtest (show 0 ≤ m/16 by positivity)
  have hc : 1/(m/16)=16/m := by ring
  rw [hc] at hy hys
  have hpre : (m/4)*(∑ j, ∫ x, (T j x)^2 ∂μ) ≤
      (16/m)*((∫ x, (F x)^2 ∂μ)+(∑ j, ∫ x, (G j x)^2 ∂μ))+
        K*(∑ j, ∫ x, (V j x)^2 ∂μ)+(K+m)*(∑ j, ∫ x, (R j x)^2 ∂μ) := by
    nlinarith only [hl,hy,hys,hb',hP']
  have hscale := mul_le_mul_of_nonneg_left hpre (show 0 ≤ 4/m by positivity)
  have hcancel : (4/m)*(m/4)=1 := by field_simp
  simpa only [← mul_assoc,hcancel,one_mul] using hscale

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

theorem realSmoothCompactL2_ae {n : ℕ} (v : Coord n → ℝ)
    (hv : ContDiff ℝ ∞ v) (hc : HasCompactSupport v) :
    (realSmoothCompactL2 v hv hc : Coord n → ℝ) =ᵐ[volume] v :=
  (real_compact_continuous_memLp v hv.continuous hc).coeFn_toLp

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

theorem real_compact_weak_H1_smooth_approximation {n : ℕ} {K L : Set (Coord n)}
    (hK : IsCompact K) (hL : IsCompact L) (hKL : K ⊆ interior L)
    (u : Coord n → ℝ) (g : Fin n → Coord n → ℝ)
    (hu : MemLp u 2 volume) (hg : ∀ i, MemLp (g i) 2 volume)
    (hsu : ∀ x, x ∉ K → u x=0) (hsg : ∀ i x, x ∉ K → g i x=0)
    (hw : ∀ i, ∀ psi : Coord n → ℝ, ContDiff ℝ ∞ psi → HasCompactSupport psi →
      (∫ x, u x*coordPartial psi x i)=-(∫ x, g i x*psi x)) :
    ∃ v : ℕ → Coord n → ℝ, ∃ hv : ∀ m, ContDiff ℝ ∞ (v m),
      ∃ hc : ∀ m, HasCompactSupport (v m),
      (∀ m, tsupport (v m) ⊆ L) ∧
      Tendsto (fun m ↦ realSmoothCompactL2 (v m) (hv m) (hc m)) atTop (𝓝 (hu.toLp u)) ∧
      ∀ i, Tendsto (fun m ↦ realSmoothCompactL2 (fun x ↦ coordPartial (v m) x i)
        (real_coordPartial_smooth (v m) (hv m) i) ((hc m).fderiv_apply ℝ (Pi.single i 1)))
        atTop (𝓝 ((hg i).toLp (g i))) := by
  have hs : tsupport u ⊆ K := closure_minimal (fun x hx ↦ by
    by_contra hn; exact hx (hsu x hn)) hK.isClosed
  have hgs (i : Fin n) : tsupport (g i) ⊆ K := closure_minimal (fun x hx ↦ by
    by_contra hn; exact hx (hsg i x hn)) hK.isClosed
  have huc : HasCompactSupport u := hK.of_isClosed_subset (isClosed_tsupport u) hs
  have hgc (i : Fin n) : HasCompactSupport (g i) :=
    hK.of_isClosed_subset (isClosed_tsupport (g i)) (hgs i)
  obtain ⟨r,hr,hsupport⟩ := real_compact_mollifier_support hK hKL
  let b : ℕ → ContDiffBump (0 : Coord n) := realMollifierBump r hr
  have hb : Tendsto (fun m ↦ (b m).rOut) atTop (𝓝 0) := realMollifierBump_radius_tendsto r hr
  let v : ℕ → Coord n → ℝ := fun m ↦ u ⋆ (b m).normed volume
  have hv (m : ℕ) : ContDiff ℝ ∞ (v m) :=
    (b m).hasCompactSupport_normed.contDiff_convolution_right
      (ContinuousLinearMap.lsmul ℝ ℝ) (hu.locallyIntegrable (by norm_num)) (b m).contDiff_normed
  have hc (m : ℕ) : HasCompactSupport (v m) :=
    hL.of_isClosed_subset (isClosed_tsupport (v m)) (hsupport u hs m)
  refine ⟨v,hv,hc,hsupport u hs,real_compact_convolution_L2_tendsto u hu huc b hb,?_⟩
  intro i
  have ht := real_compact_convolution_L2_tendsto (g i) (hg i) (hgc i) b hb
  convert ht using 1
  all_goals try with_reducible_and_instances rfl
  funext m
  apply Lp.ext
  refine (realSmoothCompactL2_ae _ _ _).trans ?_
  rw [real_weak_convolution_derivative u (g i) ((b m).normed volume)
    (hu.locallyIntegrable (by norm_num)) (b m).contDiff_normed (b m).hasCompactSupport_normed i (hw i)]
  exact (realSmoothCompactL2_ae _ _ _).symm

end
end Yau

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_RealH1TestExtension
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau
open MeasureTheory Set Filter
open scoped ContDiff Topology
noncomputable section

theorem real_L2_strong_pairing_tendsto {n : ℕ} (a u : Coord n → ℝ)
    (ha : MemLp a 2 volume) (hu : MemLp u 2 volume)
    (v : ℕ → Coord n → ℝ) (hv : ∀ m, MemLp (v m) 2 volume)
    (ht : Tendsto (fun m ↦ (hv m).toLp (v m)) atTop (𝓝 (hu.toLp u))) :
    Tendsto (fun m ↦ ∫ x, a x*v m x) atTop (𝓝 (∫ x, a x*u x)) := by
  have h := (tendsto_const_nhds (x := ha.toLp a)).inner (𝕜 := ℝ) ht
  simpa only [real_toLp_inner] using h

end
end Yau

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_RealH1DifferenceEquation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau
open MeasureTheory Set Filter
open scoped ContDiff Topology
noncomputable section

theorem real_divergence_H1_difference_equation {n : ℕ}
    (A G : Fin n → Coord n → ℝ) (F : Coord n → ℝ)
    (hA : ∀ j, MemLp (A j) 2 volume) (hG : ∀ j, MemLp (G j) 2 volume)
    (hF : MemLp F 2 volume) (R r : ℝ) (hr : r ≤ R)
    (heq : ∀ psi : Coord n → ℝ, ContDiff ℝ ∞ psi → HasCompactSupport psi →
      tsupport psi ⊆ realCenteredCube n R →
      (∑ j, ∫ x, A j x*coordPartial psi x j) =
        (∫ x, F x*psi x)-(∑ j, ∫ x, G j x*coordPartial psi x j))
    (i : Fin n) (h : ℝ) (hh : |h| ≤ R-r) {K : Set (Coord n)}
    (hK : IsCompact K) (hKr : K ⊆ interior (realCenteredCube n r))
    (v : Coord n → ℝ) (P : Fin n → Coord n → ℝ)
    (hv : MemLp v 2 volume) (hP : ∀ j, MemLp (P j) 2 volume)
    (hsv : ∀ x, x ∉ K → v x=0) (hsP : ∀ j x, x ∉ K → P j x=0)
    (hw : ∀ j, ∀ psi : Coord n → ℝ, ContDiff ℝ ∞ psi → HasCompactSupport psi →
      (∫ x, v x*coordPartial psi x j)=-(∫ x, P j x*psi x)) :
    (∀ j, Integrable (fun x ↦ realDifferenceQuotient i h (A j) x*P j x) ∧
      Integrable (fun x ↦ realDifferenceQuotient i h (G j) x*P j x)) ∧
    Integrable (fun x ↦ F x*realDifferenceQuotient i (-h) v x) ∧
    (∑ j, ∫ x, realDifferenceQuotient i h (A j) x*P j x) =
      -(∫ x, F x*realDifferenceQuotient i (-h) v x)-
        (∑ j, ∫ x, realDifferenceQuotient i h (G j) x*P j x) := by
  obtain ⟨w,hwS,hwC,hwK,ht,hdt⟩ := real_compact_weak_H1_smooth_approximation
    hK (realCenteredCube_isCompact n r) hKr v P hv hP hsv hsP hw
  have hDA (j : Fin n) := realDifferenceQuotient_memLp i h (A j) (hA j)
  have hDG (j : Fin n) := realDifferenceQuotient_memLp i h (G j) (hG j)
  have hDF := realDifferenceQuotient_memLp i h F hF
  have hwLp (m : ℕ) := real_compact_continuous_memLp (w m) (hwS m).continuous (hwC m)
  have hdLp (j : Fin n) (m : ℕ) := real_compact_continuous_memLp _
    (real_coordPartial_smooth (w m) (hwS m) j).continuous ((hwC m).fderiv_apply ℝ (Pi.single j 1))
  have hleft := tendsto_finsetSum Finset.univ (fun j _ ↦ real_L2_strong_pairing_tendsto
    _ (P j) (hDA j) (hP j) (fun m x ↦ coordPartial (w m) x j) (hdLp j) (hdt j))
  have hdiv := tendsto_finsetSum Finset.univ (fun j _ ↦ real_L2_strong_pairing_tendsto
    _ (P j) (hDG j) (hP j) (fun m x ↦ coordPartial (w m) x j) (hdLp j) (hdt j))
  have hscalar := real_L2_strong_pairing_tendsto _ v hDF hv w hwLp ht
  have he (m : ℕ) := (real_divergence_forcing_difference_equation A G F hA hG hF R r hr heq
    i h hh (w m) (hwS m) (hwC m) (hwK m)).2.2
  have hsame (m : ℕ) : (∑ j, ∫ x, realDifferenceQuotient i h (A j) x*coordPartial (w m) x j) =
      (∫ x, realDifferenceQuotient i h F x*w m x)-
        ∑ j, ∫ x, realDifferenceQuotient i h (G j) x*coordPartial (w m) x j := by
    rw [(real_differenceQuotient_pairing i h F (w m) hF (hwLp m)).2.2]
    exact he m
  have hlim := tendsto_nhds_unique hleft ((hscalar.sub hdiv).congr (fun m ↦ (hsame m).symm))
  refine ⟨fun j ↦ ⟨(hDA j).integrable_mul (hP j),(hDG j).integrable_mul (hP j)⟩,
    hF.integrable_mul (realDifferenceQuotient_memLp i (-h) v hv),?_⟩
  rw [(real_differenceQuotient_pairing i h F v hF hv).2.2] at hlim
  exact hlim

end
end Yau

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_RealSquareDifferenceTest
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau
open MeasureTheory Set
open scoped ContDiff
noncomputable section

theorem real_square_cutoff_difference_test {n : ℕ}
    (A G : Fin n → Coord n → ℝ) (F : Coord n → ℝ)
    (hA : ∀ j, MemLp (A j) 2 volume) (hG : ∀ j, MemLp (G j) 2 volume)
    (hF : MemLp F 2 volume) (R r : ℝ) (hr : r ≤ R)
    (heq : ∀ psi : Coord n → ℝ, ContDiff ℝ ∞ psi → HasCompactSupport psi →
      tsupport psi ⊆ realCenteredCube n R →
      (∑ j, ∫ x, A j x*coordPartial psi x j) =
        (∫ x, F x*psi x)-(∑ j, ∫ x, G j x*coordPartial psi x j))
    (u : Coord n → ℝ) (g : Fin n → Coord n → ℝ)
    (hu : MemLp u 2 volume) (hg : ∀ j, MemLp (g j) 2 volume)
    (hw : ∀ j, ∀ psi : Coord n → ℝ, ContDiff ℝ ∞ psi → HasCompactSupport psi →
      tsupport psi ⊆ realCenteredCube n R →
      (∫ x, u x*coordPartial psi x j)=-(∫ x, g j x*psi x))
    (eta : Coord n → ℝ) (he : ContDiff ℝ ∞ eta) (hc : HasCompactSupport eta)
    (hs : tsupport eta ⊆ interior (realCenteredCube n r))
    (i : Fin n) (h : ℝ) (hh : |h| ≤ R-r) :
    let v := realSquareCutoff eta (realDifferenceQuotient i h u)
    let P := realSquareCutoffGradient eta (realDifferenceQuotient i h u)
      (fun j ↦ realDifferenceQuotient i h (g j))
    MemLp v 2 volume ∧ (∀ j, MemLp (P j) 2 volume) ∧
    (∀ j, Integrable (fun x ↦ realDifferenceQuotient i h (A j) x*P j x) ∧
      Integrable (fun x ↦ realDifferenceQuotient i h (G j) x*P j x)) ∧
    Integrable (fun x ↦ F x*realDifferenceQuotient i (-h) v x) ∧
    (∑ j, ∫ x, realDifferenceQuotient i h (A j) x*P j x) =
      -(∫ x, F x*realDifferenceQuotient i (-h) v x)-
        (∑ j, ∫ x, realDifferenceQuotient i h (G j) x*P j x) := by
  dsimp only
  have htest := real_square_cutoff_difference_weak_gradient eta u g hu hg R r hr he
    (hs.trans interior_subset) hw i h hh
  refine ⟨htest.1,htest.2.1,?_⟩
  exact real_divergence_H1_difference_equation A G F hA hG hF R r hr heq i h hh
    hc hs _ _ htest.1 htest.2.1 htest.2.2.1 htest.2.2.2.1 htest.2.2.2.2

end
end Yau

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_RealInteriorSquareDifferenceTest
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau
open MeasureTheory Set
open scoped ContDiff
noncomputable section

theorem real_interior_square_difference_test {n : ℕ} (R r : ℝ) (hr : r ≤ R)
    (C : Coord n → Fin n → Fin n → ℝ) (hC : ∀ a j, Continuous (fun x ↦ C x a j))
    (u : Coord n → ℝ) (V0 P0 G0 : Fin n → Coord n → ℝ) (F0 : Coord n → ℝ)
    (hu : MemLp u 2 (volume.restrict (realCenteredCube n R)))
    (hV : ∀ a, MemLp (V0 a) 2 (volume.restrict (realCenteredCube n R)))
    (hP : ∀ a, MemLp (P0 a) 2 (volume.restrict (realCenteredCube n R)))
    (hG : ∀ a, MemLp (G0 a) 2 (volume.restrict (realCenteredCube n R)))
    (hF : MemLp F0 2 (volume.restrict (realCenteredCube n R)))
    (hweak : ∀ j psi, ContDiff ℝ ∞ psi → HasCompactSupport psi → tsupport psi ⊆ realCenteredCube n R →
      (∫ x in realCenteredCube n R, u x*coordPartial psi x j) =
        -(∫ x in realCenteredCube n R, V0 j x*psi x))
    (heq : ∀ psi, ContDiff ℝ ∞ psi → HasCompactSupport psi → tsupport psi ⊆ realCenteredCube n R →
      (∑ a, ∑ j, ∫ x in realCenteredCube n R, C x a j*P0 a x*coordPartial psi x j) =
        (∫ x in realCenteredCube n R, F0 x*psi x)-
          ∑ j, ∫ x in realCenteredCube n R, G0 j x*coordPartial psi x j)
    (eta : Coord n → ℝ) (he : ContDiff ℝ ∞ eta) (hc : HasCompactSupport eta)
    (hs : tsupport eta ⊆ interior (realCenteredCube n r))
    (i : Fin n) (h : ℝ) (hh : |h| ≤ R-r) :
    let Q := realCenteredCube n R
    let U := Q.indicator u
    let V := fun a ↦ Q.indicator (V0 a)
    let A := fun j ↦ Q.indicator (fun x ↦ ∑ a, C x a j*P0 a x)
    let G := fun j ↦ Q.indicator (G0 j)
    let F := Q.indicator F0
    let v := realSquareCutoff eta (realDifferenceQuotient i h U)
    let P := realSquareCutoffGradient eta (realDifferenceQuotient i h U)
      (fun j ↦ realDifferenceQuotient i h (V j))
    MemLp v 2 volume ∧ (∀ j, MemLp (P j) 2 volume) ∧
    (∀ j, Integrable (fun x ↦ realDifferenceQuotient i h (A j) x*P j x) ∧
      Integrable (fun x ↦ realDifferenceQuotient i h (G j) x*P j x)) ∧
    Integrable (fun x ↦ F x*realDifferenceQuotient i (-h) v x) ∧
    (∑ j, ∫ x, realDifferenceQuotient i h (A j) x*P j x) =
      -(∫ x, F x*realDifferenceQuotient i (-h) v x)-
        (∑ j, ∫ x, realDifferenceQuotient i h (G j) x*P j x) := by
  dsimp only
  let Q := realCenteredCube n R
  have hQ : IsCompact Q := realCenteredCube_isCompact n R
  let U := Q.indicator u
  let V := fun a ↦ Q.indicator (V0 a)
  let A := fun j ↦ Q.indicator (fun x ↦ ∑ a, C x a j*P0 a x)
  let G := fun j ↦ Q.indicator (G0 j)
  let F := Q.indicator F0
  have hU : MemLp U 2 volume := (memLp_indicator_iff_restrict hQ.measurableSet).mpr hu
  have hVG (a : Fin n) : MemLp (V a) 2 volume := (memLp_indicator_iff_restrict hQ.measurableSet).mpr (hV a)
  have hGG (j : Fin n) : MemLp (G j) 2 volume := (memLp_indicator_iff_restrict hQ.measurableSet).mpr (hG j)
  have hFG : MemLp F 2 volume := (memLp_indicator_iff_restrict hQ.measurableSet).mpr hF
  have hcoef (a j : Fin n) : MemLp (fun x ↦ C x a j*P0 a x) 2 (volume.restrict Q) := by
    obtain ⟨_,_,hb⟩ := real_compact_multiplier_bound hQ _ (hC a j)
    exact (hb _ (hP a)).1
  have hAG (j : Fin n) : MemLp (A j) 2 volume :=
    (memLp_indicator_iff_restrict hQ.measurableSet).mpr
      (memLp_finsetSum Finset.univ (fun a _ ↦ hcoef a j))
  have hzpair (a b : Coord n → ℝ) : (∫ x, Q.indicator a x*b x)=∫ x in Q, a x*b x := by
    simp only [← indicator_mul_left,integral_indicator hQ.measurableSet]
  have hW (j : Fin n) (psi : Coord n → ℝ) (hp : ContDiff ℝ ∞ psi)
      (hpc : HasCompactSupport psi) (hps : tsupport psi ⊆ Q) :
      (∫ x, U x*coordPartial psi x j)=-(∫ x, V j x*psi x) := by
    change (∫ x, Q.indicator u x*coordPartial psi x j)=-(∫ x, Q.indicator (V0 j) x*psi x)
    rw [hzpair,hzpair]
    exact hweak j psi hp hpc hps
  have hE (psi : Coord n → ℝ) (hp : ContDiff ℝ ∞ psi)
      (hpc : HasCompactSupport psi) (hps : tsupport psi ⊆ Q) :
      (∑ j, ∫ x, A j x*coordPartial psi x j) =
        (∫ x, F x*psi x)-(∑ j, ∫ x, G j x*coordPartial psi x j) := by
    have hi (a j : Fin n) : IntegrableOn (fun x ↦ C x a j*P0 a x*coordPartial psi x j) Q :=
      (hcoef a j).integrable_mul (real_continuous_memLp_compact hQ _ (real_coordPartial_smooth psi hp j).continuous)
    have hsum (j : Fin n) : (∫ x, A j x*coordPartial psi x j) =
        ∑ a, ∫ x in Q, C x a j*P0 a x*coordPartial psi x j := by
      change (∫ x, Q.indicator (fun y ↦ ∑ a, C y a j*P0 a y) x*coordPartial psi x j)=_
      rw [hzpair]
      simp only [Finset.sum_mul]
      exact integral_finsetSum Finset.univ (fun a _ ↦ hi a j)
    simp only [hsum]
    rw [Finset.sum_comm]
    change (∑ a, ∑ j, ∫ x in Q, C x a j*P0 a x*coordPartial psi x j) =
      (∫ x, Q.indicator F0 x*psi x)-(∑ j, ∫ x, Q.indicator (G0 j) x*coordPartial psi x j)
    simp only [hzpair]
    exact heq psi hp hpc hps
  exact real_square_cutoff_difference_test A G F hAG hGG hFG R r hr hE U V hU hVG hW eta he hc hs i h hh

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

theorem real_square_gradient_difference_pairing_localize {n : ℕ} (Q : Set (Coord n))
    (u chi eta q : Coord n → ℝ) (V : Fin n → Coord n → ℝ)
    (i j : Fin n) (h : ℝ)
    (hend : ∀ x ∈ tsupport eta, x ∈ Q ∧ x+Pi.single i h ∈ Q ∧
      chi x=1 ∧ chi (x+Pi.single i h)=1) :
    (fun x ↦ realDifferenceQuotient i h (Q.indicator u) x*realSquareCutoffGradient eta q V j x) =
      (fun x ↦ realDifferenceQuotient i h (fun y ↦ chi y*u y) x*realSquareCutoffGradient eta q V j x) := by
  funext x
  by_cases hx : x ∈ tsupport eta
  · obtain ⟨hxQ,htQ,hc,hct⟩ := hend x hx
    rw [real_indicator_difference_localize Q u chi i h x hxQ htQ hc hct]
  · simp only [realSquareCutoffGradient,image_eq_zero_of_notMem_tsupport hx,
      zero_pow (by decide : (2:ℕ)≠0),zero_mul,mul_zero,add_zero]

end
end Yau

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_RealSquareCutoffEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau
open MeasureTheory Set
open scoped ContDiff
noncomputable section

theorem real_square_cutoff_pointwise_bound (a t r : ℝ) (ha : |a| ≤ 1) :
    (a*(t+2*r))^2 ≤ 2*t^2+8*r^2 := by
  have hsq : a^2 ≤ 1 := (sq_le_one_iff_abs_le_one a).mpr ha
  have hmul := mul_le_mul_of_nonneg_right hsq (sq_nonneg (t+2*r))
  nlinarith [sq_nonneg (t-2*r)]

theorem real_square_cutoff_gradient_energy {n : ℕ} (eta q : Coord n → ℝ)
    (V : Fin n → Coord n → ℝ) (he : ContDiff ℝ ∞ eta) (hc : HasCompactSupport eta)
    (hb : ∀ x, |eta x| ≤ 1) (hq : MemLp q 2 volume) (hV : ∀ j, MemLp (V j) 2 volume) :
    let T := fun j x ↦ eta x*V j x
    let R := fun j x ↦ coordPartial eta x j*q x
    let P := realSquareCutoffGradient eta q V
    (∀ j, MemLp (T j) 2 volume ∧ MemLp (R j) 2 volume ∧ MemLp (P j) 2 volume) ∧
    (∑ j, ∫ x, (P j x)^2) ≤
      2*(∑ j, ∫ x, (T j x)^2)+8*(∑ j, ∫ x, (R j x)^2) := by
  dsimp only
  have hT (j : Fin n) : MemLp (fun x ↦ eta x*V j x) 2 volume :=
    real_compact_localL2_product hc eta (V j) he.continuous Subset.rfl ((hV j).restrict _)
  have hR (j : Fin n) : MemLp (fun x ↦ coordPartial eta x j*q x) 2 volume :=
    real_compact_localL2_product hc _ q (real_coordPartial_smooth eta he j).continuous
      (tsupport_fderiv_apply_subset ℝ (Pi.single j 1)) (hq.restrict _)
  have hid (j : Fin n) : realSquareCutoffGradient eta q V j =
      fun x ↦ eta x*((eta x*V j x)+2*(coordPartial eta x j*q x)) := by
    funext x; unfold realSquareCutoffGradient; ring
  have hP (j : Fin n) : MemLp (realSquareCutoffGradient eta q V j) 2 volume := by
    rw [hid]
    exact real_compact_localL2_product hc eta _ he.continuous Subset.rfl
      (((hT j).add ((hR j).const_mul 2)).restrict _)
  refine ⟨fun j ↦ ⟨hT j,hR j,hP j⟩,?_⟩
  have hle (j : Fin n) : (∫ x, (realSquareCutoffGradient eta q V j x)^2) ≤
      2*(∫ x, (eta x*V j x)^2)+8*(∫ x, (coordPartial eta x j*q x)^2) := by
    rw [← integral_const_mul,← integral_const_mul,
      ← integral_add ((hT j).integrable_sq.const_mul 2) ((hR j).integrable_sq.const_mul 8)]
    apply integral_mono (hP j).integrable_sq
      (((hT j).integrable_sq.const_mul 2).add ((hR j).integrable_sq.const_mul 8))
    intro x
    rw [hid]
    exact real_square_cutoff_pointwise_bound _ _ _ (hb x)
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun j _ ↦ hle j)
  simpa only [Finset.sum_add_distrib,← Finset.mul_sum] using hsum

theorem real_compact_weak_test_difference_energy {n : ℕ} (v : Coord n → ℝ)
    (P T R : Fin n → Coord n → ℝ) (hv : MemLp v 2 volume) (hc : HasCompactSupport v)
    (hP : ∀ j, MemLp (P j) 2 volume)
    (hw : ∀ j, ∀ psi : Coord n → ℝ, ContDiff ℝ ∞ psi → HasCompactSupport psi →
      (∫ x, v x*coordPartial psi x j)=-(∫ x, P j x*psi x))
    (hbound : (∑ j, ∫ x, (P j x)^2) ≤
      2*(∑ j, ∫ x, (T j x)^2)+8*(∑ j, ∫ x, (R j x)^2)) (i : Fin n) (h : ℝ) :
    MemLp (realDifferenceQuotient i h v) 2 volume ∧
      (∫ x, (realDifferenceQuotient i h v x)^2) ≤
        2*(∑ j, ∫ x, (T j x)^2)+8*(∑ j, ∫ x, (R j x)^2) := by
  have hd := real_weak_derivative_difference_bound v (P i)
    (real_compact_memLp_integrable v hv hc) hv (hP i) i (hw i) h
  refine ⟨hd.1,hd.2.trans (le_trans ?_ hbound)⟩
  exact Finset.single_le_sum (f := fun j ↦ ∫ x, (P j x)^2)
    (fun j _ ↦ integral_nonneg (fun x ↦ sq_nonneg (P j x))) (Finset.mem_univ i)

end
end Yau

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_RealSquareDifferenceEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau
open MeasureTheory Set
open scoped ContDiff
noncomputable section

theorem real_square_difference_test_energy {n : ℕ}
    (eta u : Coord n → ℝ) (g : Fin n → Coord n → ℝ)
    (hu : MemLp u 2 volume) (hg : ∀ j, MemLp (g j) 2 volume)
    (R0 r : ℝ) (hr : r ≤ R0) (he : ContDiff ℝ ∞ eta) (hc : HasCompactSupport eta)
    (hb : ∀ x, |eta x| ≤ 1) (hs : tsupport eta ⊆ realCenteredCube n r)
    (hw : ∀ j, ∀ psi : Coord n → ℝ, ContDiff ℝ ∞ psi → HasCompactSupport psi →
      tsupport psi ⊆ realCenteredCube n R0 →
      (∫ x, u x*coordPartial psi x j)=-(∫ x, g j x*psi x))
    (i : Fin n) (h : ℝ) (hh : |h| ≤ R0-r) :
    let q := realDifferenceQuotient i h u
    let T := fun j x ↦ eta x*realDifferenceQuotient i h (g j) x
    let R := fun j x ↦ coordPartial eta x j*q x
    let P := realSquareCutoffGradient eta q (fun j ↦ realDifferenceQuotient i h (g j))
    let v := realSquareCutoff eta q
    let b := realDifferenceQuotient i (-h) v
    (∀ j, MemLp (T j) 2 volume ∧ MemLp (R j) 2 volume ∧ MemLp (P j) 2 volume) ∧
    MemLp b 2 volume ∧
    (∑ j, ∫ x, (P j x)^2) ≤ 2*(∑ j, ∫ x, (T j x)^2)+8*(∑ j, ∫ x, (R j x)^2) ∧
    (∫ x, (b x)^2) ≤ 2*(∑ j, ∫ x, (T j x)^2)+8*(∑ j, ∫ x, (R j x)^2) := by
  dsimp only
  have hq := realDifferenceQuotient_memLp i h u hu
  have hV (j : Fin n) := realDifferenceQuotient_memLp i h (g j) (hg j)
  have henergy := real_square_cutoff_gradient_energy eta _ _ he hc hb hq hV
  have htest := real_square_cutoff_difference_weak_gradient eta u g hu hg R0 r hr he hs hw i h hh
  have hvc : HasCompactSupport (realSquareCutoff eta (realDifferenceQuotient i h u)) := by
    convert (hc.mul_right (f' := eta)).mul_right (f' := realDifferenceQuotient i h u) using 1
    all_goals try with_reducible_and_instances rfl
    first | rfl | (funext x; simp only [realSquareCutoff,pow_two,Pi.mul_apply])
  have houter := real_compact_weak_test_difference_energy _ _ _ _ htest.1 hvc htest.2.1
    htest.2.2.2.2 henergy.2 i (-h)
  exact ⟨henergy.1,houter.1,henergy.2,houter.2⟩

end
end Yau

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Charts_SphereInteriorLocalizedEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open MeasureTheory Yau.Geometry Set
open scoped ContDiff
noncomputable section

theorem sphere_interior_localized_energy_oai (d : SphereEnergyData) (p : Base) :
    ∃ m > 0, ∃ K > 0,
      ∀ (R0 r : ℝ), r ≤ R0 → R0 ≤ 1 →
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
      ∀ (eta chi : Yau.Jets.Coord → ℝ),
        ContDiff ℝ ∞ eta → HasCompactSupport eta → (∀ x, |eta x| ≤ 1) →
        tsupport eta ⊆ interior (Yau.realCenteredCube 4 r) →
        ContDiff ℝ ∞ chi → tsupport chi ⊆ Q →
        ∀ (i : Fin 4) (h : ℝ), |h| ≤ R0-r →
        (∀ x ∈ tsupport eta, x ∈ interior Q ∧ x+Pi.single i h ∈ interior Q ∧
          chi x=1 ∧ chi (x+Pi.single i h)=1) →
        let U := Q.indicator u
        let V := fun a ↦ Q.indicator (V0 a)
        let F := Q.indicator F0
        let q := Yau.realDifferenceQuotient i h U
        let T := fun a x ↦ eta x*Yau.realDifferenceQuotient i h (V a) x
        let W := fun a x ↦ eta x*V a x
        let R := fun a x ↦ Yau.coordPartial eta x a*q x
        (∀ a, MemLp (T a) 2 volume ∧ MemLp (W a) 2 volume ∧ MemLp (R a) 2 volume) ∧
        (∑ a, ∫ x, (T a x)^2) ≤ (4/m)*
          ((16/m)*((∫ x, (F x)^2)+
              (∑ j, ∫ x, (chi x*DG j i x+Yau.coordPartial chi x i*G j x)^2))+
            K*(∑ a, ∫ x, (W a x)^2)+(K+m)*(∑ a, ∫ x, (R a x)^2)) := by
  obtain ⟨m,hm,K,hK,hcoer⟩ := sphere_interior_flux_difference_coercivity d p
  refine ⟨m,hm,K,hK,?_⟩
  intro R0 r hr hR u V0 P0 G DG F0
  dsimp only
  intro hu hv hp hg hd hf hsame hweak hcomm hequation eta chi he hc heb hs hchi hchis i h hh hend
  let Q := Yau.realCenteredCube 4 R0
  have hQ : IsCompact Q := Yau.realCenteredCube_isCompact 4 R0
  have hsub : Q ⊆ realFinCube 4 := Yau.realCenteredCube_mono hR
  let U := Q.indicator u
  let V := fun a ↦ Q.indicator (V0 a)
  let A := fun j ↦ Q.indicator (fun x ↦ ∑ a, sphereChartPrincipalDensity d p x a j*P0 a x)
  let F := Q.indicator F0
  let q := Yau.realDifferenceQuotient i h U
  let T := fun a x ↦ eta x*Yau.realDifferenceQuotient i h (V a) x
  let W := fun a x ↦ eta x*V a x
  let R := fun a x ↦ Yau.coordPartial eta x a*q x
  let P := Yau.realSquareCutoffGradient eta q (fun a ↦ Yau.realDifferenceQuotient i h (V a))
  let v := Yau.realSquareCutoff eta q
  let b := Yau.realDifferenceQuotient i (-h) v
  let L := fun j ↦ Yau.realDifferenceQuotient i h (fun x ↦ chi x*G j x)
  have hU : MemLp U 2 volume := (memLp_indicator_iff_restrict hQ.measurableSet).mpr hu
  have hV (j : Fin 4) : MemLp (V j) 2 volume :=
    (memLp_indicator_iff_restrict hQ.measurableSet).mpr (hv j)
  have hW (j : Fin 4) : MemLp (W j) 2 volume :=
    Yau.real_compact_localL2_product hc eta (V j) he.continuous Subset.rfl ((hV j).restrict _)
  have hzpair (a b : Yau.Jets.Coord → ℝ) :
      (∫ x, Q.indicator a x*b x) = ∫ x in Q, a x*b x := by
    simp only [← indicator_mul_left,integral_indicator hQ.measurableSet]
  have hUW (j : Fin 4) (psi : Yau.Jets.Coord → ℝ) (hp : ContDiff ℝ ∞ psi)
      (hpc : HasCompactSupport psi) (hps : tsupport psi ⊆ Q) :
      (∫ x, U x*Yau.coordPartial psi x j)=-(∫ x, V j x*psi x) := by
    change (∫ x, Q.indicator u x*Yau.coordPartial psi x j)=-(∫ x, Q.indicator (V0 j) x*psi x)
    rw [hzpair,hzpair]
    exact hweak j psi hp hpc hps
  have htest := Yau.real_interior_square_difference_test R0 r hr
    (sphereChartPrincipalDensity d p) (fun a j ↦ (sphereChartPrincipalDensity_smooth d p a j).continuous)
    u V0 P0 G F0 hu hv hp hg hf hweak hequation eta he hc hs i h hh
  have henergy := Yau.real_square_difference_test_energy eta U V hU hV R0 r hr
    he hc heb (hs.trans interior_subset) hUW i h hh
  have hlocal (j : Fin 4) := Yau.real_local_weak_cutoff_difference_bound hQ (G j) (DG j i) chi
    (hg j) (hd j i) hchi hchis i (hcomm j i) h
  have hF : MemLp F 2 volume := (memLp_indicator_iff_restrict hQ.measurableSet).mpr hf
  have hlow := hcoer Q hsub P0 V0 hsame i h eta q (fun x hx ↦ ⟨(hend x hx).1,(hend x hx).2.1⟩)
  have hend0 : ∀ x ∈ tsupport eta, x ∈ Q ∧ x+Pi.single i h ∈ Q ∧ chi x=1 ∧ chi (x+Pi.single i h)=1 :=
    fun x hx ↦ ⟨interior_subset (hend x hx).1,interior_subset (hend x hx).2.1,(hend x hx).2.2⟩
  have heq : (∑ j, ∫ x, Yau.realDifferenceQuotient i h (A j) x*P j x) =
      -(∫ x, F x*b x)-(∑ j, ∫ x, L j x*P j x) := by
    have hl (j : Fin 4) := Yau.real_square_gradient_difference_pairing_localize Q (G j) chi eta q
      (fun a ↦ Yau.realDifferenceQuotient i h (V a)) i j h hend0
    have hlsum : (∑ j, ∫ x, Yau.realDifferenceQuotient i h (Q.indicator (G j)) x*P j x) =
        (∑ j, ∫ x, L j x*P j x) := by
      apply Finset.sum_congr rfl
      intro j _
      exact congrArg (fun v : Yau.Jets.Coord → ℝ ↦ ∫ x, v x) (hl j)
    rw [← hlsum]
    exact htest.2.2.2.2
  have habs := Yau.real_divergence_difference_energy_absorption_ae volume m K hm
    T W R (fun j ↦ Yau.realDifferenceQuotient i h (A j)) P L F b
    (fun j ↦ (henergy.1 j).1) hW (fun j ↦ (henergy.1 j).2.1)
    (fun j ↦ (henergy.1 j).2.2) (fun j ↦ (hlocal j).1)
    (fun j ↦ (htest.2.2.1 j).1) hF henergy.2.1 hlow henergy.2.2.2 henergy.2.2.1 heq
  refine ⟨fun j ↦ ⟨(henergy.1 j).1,hW j,(henergy.1 j).2.1⟩,habs.trans ?_⟩
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun j _ ↦ (hlocal j).2)
  gcongr

end
end Yau.Target

end OAI
end

theorem solution : type_of% @OAI.Yau.Target.sphere_interior_localized_energy_oai := @OAI.Yau.Target.sphere_interior_localized_energy_oai
