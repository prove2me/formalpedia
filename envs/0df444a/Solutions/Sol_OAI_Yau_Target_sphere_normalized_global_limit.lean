-- Prove2me | solution 1 for OAI.Yau.Target.sphere_normalized_global_limit
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T00:34:20.350053+00:00
-- url     : https://prove2.me/submissions/a78ee1ed-36ba-465b-9e76-8fca4717deb7

import Mathlib
import Mathlib.Algebra.MvPolynomial.PDeriv
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
import Mathlib.Analysis.Calculus.UniformLimitsDeriv
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Operator.ContinuousLinearMap
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Data.Finset.Insert
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
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.ContDiff
import Mathlib.MeasureTheory.Integral.IntervalIntegral.DistLEIntegral
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.Order.Filter.AtTopBot.CountablyGenerated
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
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.Algebra.Ring.Basic
import Mathlib.Topology.Algebra.Support
import Mathlib.Topology.Compactness.LocallyCompact
import Mathlib.Topology.ContinuousMap.Bounded.ArzelaAscoli
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Sequences
import Mathlib.Topology.UniformSpace.UniformApproximation
import Mathlib.Topology.UniformSpace.UniformConvergence
import Mathlib.Topology.UniformSpace.UniformConvergenceTopology
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
-- module Solutions.OAIQ237_NY.NodalSets_Charts_SphereChartL2Comparison
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Yau.Geometry Set Metric MeasureTheory
noncomputable section
variable {T : Type*} [TopologicalSpace T] [CompactSpace T]

theorem sphere_chart_l2_comparison (rho : T → Base → ℝ)
    (hr : Continuous (fun z : T × Base ↦ rho z.1 z.2)) (hp : ∀ t p, 0 < rho t p)
    (p : Base) (Q : Set Yau.Jets.Coord) (hQ : IsCompact Q) :
    ∃ K > 0, ∀ t (v : Base → ℝ), Continuous v →
      IntegrableOn (fun x ↦ v (sphereChartCoordMap p x)^2) Q ∧
      (∫ x in Q, v (sphereChartCoordMap p x)^2) ≤ K*sphereWeightedPairing (rho t) v v := by
  let d (t : T) (x : Yau.Jets.Coord) := roundCoordDensity x*rho t (sphereChartCoordMap p x)
  have hdpos (t : T) (x : Yau.Jets.Coord) : 0 < d t x :=
    mul_pos (roundCoordDensity_pos x) (hp t _)
  have hdc : Continuous (fun z : T × Q ↦ d z.1 z.2) :=
    (roundCoordDensity_smooth.continuous.comp (continuous_subtype_val.comp continuous_snd)).mul
      (hr.comp (continuous_fst.prodMk ((sphereChartCoordMap_smooth p).continuous.comp
        (continuous_subtype_val.comp continuous_snd))))
  obtain ⟨K,hK,hbound⟩ := compact_parameter_scalar_bound (fun t x ↦ (d t x)⁻¹) hQ
    (hdc.inv₀ (fun z ↦ (hdpos z.1 z.2).ne'))
  have hlow (t : T) (x : Yau.Jets.Coord) (hx : x ∈ Q) : 1 ≤ K*d t x := by
    have hh := (le_abs_self (d t x)⁻¹).trans (hbound t x hx)
    simpa only [inv_mul_cancel₀ (hdpos t x).ne'] using
      mul_le_mul_of_nonneg_right hh (hdpos t x).le
  refine ⟨K,hK,?_⟩
  intro t v hv
  have hrt : Continuous (rho t) := hr.comp (continuous_const.prodMk continuous_id)
  let J (x : Yau.Jets.Coord) := roundCoordDensity x*(rho t (sphereChartCoordMap p x)*
    v (sphereChartCoordMap p x)*v (sphereChartCoordMap p x))
  have hJ : Integrable J := by
    have hi := (sphereReferenceMeasure_integrable_chart p _).mp
      (sphereWeightedPairing_integrable (rho t) v v hrt hv hv)
    simpa only [roundChartDensity_coord_eq] using hi
  have hJn (x : Yau.Jets.Coord) : 0 ≤ J x := by
    dsimp [J]
    nlinarith [roundCoordDensity_pos x,hp t (sphereChartCoordMap p x),sq_nonneg (v (sphereChartCoordMap p x)),
      mul_nonneg (mul_pos (roundCoordDensity_pos x) (hp t (sphereChartCoordMap p x))).le
        (sq_nonneg (v (sphereChartCoordMap p x)))]
  have hi : IntegrableOn (fun x ↦ v (sphereChartCoordMap p x)^2) Q :=
    ((hv.comp (sphereChartCoordMap_smooth p).continuous).pow 2).continuousOn.integrableOn_compact hQ
  refine ⟨hi,?_⟩
  have hmon := setIntegral_mono_on hi (hJ.integrableOn.const_mul K) hQ.isClosed.measurableSet
    (fun x hx ↦ show v (sphereChartCoordMap p x)^2 ≤ K*J x from by
      have hh := mul_le_mul_of_nonneg_right (hlow t x hx) (sq_nonneg (v (sphereChartCoordMap p x)))
      dsimp [d,J] at hh ⊢
      nlinarith [hh])
  rw [integral_const_mul] at hmon
  have heq : (∫ x, J x) = sphereWeightedPairing (rho t) v v := by
    rw [sphereWeightedPairing,sphereReferenceMeasure_integral_chart p]
    simp only [roundChartDensity_coord_eq]
    rfl
  exact hmon.trans ((mul_le_mul_of_nonneg_left
    (setIntegral_le_integral hJ (Filter.Eventually.of_forall hJn)) hK.le).trans_eq (by rw [heq]))

theorem sphere_normalized_chart_l2_bound (rho : T → Base → ℝ)
    (hr : Continuous (fun z : T × Base ↦ rho z.1 z.2)) (hp : ∀ t p, 0 < rho t p)
    (p : Base) (Q : Set Yau.Jets.Coord) (hQ : IsCompact Q) :
    ∃ K > 0, ∀ t (v : Base → ℝ), Continuous v → sphereWeightedPairing (rho t) v v=1 →
      (∫ x in Q, v (sphereChartCoordMap p x)^2) ≤ K := by
  obtain ⟨K,hK,hest⟩ := sphere_chart_l2_comparison rho hr hp p Q hQ
  refine ⟨K,hK,?_⟩
  intro t v hv hn
  simpa only [hn,mul_one] using (hest t v hv).2

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

lemma intrinsicRealPotential_smooth (rho : Base → ℝ)
    (hr : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ rho) (lam : ℝ) (p : Base) :
    ContDiff ℝ ∞ (intrinsicRealPotential rho lam p) :=
  contDiff_const.mul (spherePullback_smooth rho hr p)

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

end
end Yau.Target

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
-- module Solutions.OAIQ237_NY.NodalSets_Coefficients_IntrinsicDivergenceCoefficients
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Manifold Yau.Geometry
open scoped ContDiff
noncomputable section

lemma intrinsicDivergencePrincipal_smooth (A : IntrinsicTensor) (hA : IntrinsicTensorSmooth A)
    (hs : ∀ p v w, A p v w = A p w v) (hp : ∀ p v, v ≠ 0 → 0 < A p v v)
    (p : Base) (i j : Fin 4) : ContDiff ℝ ∞ (fun x ↦ intrinsicDivergencePrincipal A p x i j) :=
  roundCoordDensity_smooth.mul (intrinsicRealPrincipal_smooth A hA hs hp p i j)

lemma intrinsicDivergencePrincipal_symmetric (A : IntrinsicTensor)
    (hs : ∀ p v w, A p v w = A p w v) (p : Base) (x : Yau.Jets.Coord) (i j : Fin 4) :
    intrinsicDivergencePrincipal A p x i j = intrinsicDivergencePrincipal A p x j i := by
  change roundCoordDensity x * _ = roundCoordDensity x * _
  rw [intrinsicRealPrincipal_symmetric A hs]

lemma intrinsicDivergencePrincipal_posDef (A : IntrinsicTensor)
    (hs : ∀ p v w, A p v w = A p w v) (hp : ∀ p v, v ≠ 0 → 0 < A p v v)
    (p : Base) (x : Yau.Jets.Coord) : (intrinsicDivergencePrincipal A p x).PosDef :=
  (intrinsicRealPrincipal_posDef A hs hp p x).smul (roundCoordDensity_pos x)

lemma intrinsicDivergencePotential_smooth (rho : Base → ℝ)
    (hr : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ rho) (lam : ℝ) (p : Base) :
    ContDiff ℝ ∞ (intrinsicDivergencePotential rho lam p) :=
  roundCoordDensity_smooth.mul (intrinsicRealPotential_smooth rho hr lam p)

theorem intrinsic_unweighted_divergence_equation (A : IntrinsicTensor) (rho : Base → ℝ)
    (hrp : ∀ p, 0 < rho p) (w : Base → ℝ) (lam : ℝ)
    (he : ∀ p z, -intrinsicWeightedChartOperator A rho w p z =
      lam*w ((extChartAt (𝓡 4) p).symm z)) (p : Base) (x : Yau.Jets.Coord) :
    Yau.coordDiv (realMatrixFlux (intrinsicDivergencePrincipal A p) (w ∘ sphereChartCoordMap p)) x +
      intrinsicDivergencePotential rho lam p x * (w ∘ sphereChartCoordMap p) x = 0 := by
  have h := intrinsic_real_divergence_equation A rho hrp w lam he p x
  rw [Yau.weightedDiv] at h
  have hh := congrArg (fun s : ℝ ↦ roundCoordDensity x*s) h
  rw [mul_add,← mul_assoc,mul_inv_cancel₀ (roundCoordDensity_pos x).ne',one_mul,mul_zero] at hh
  have hf : realMatrixFlux (intrinsicDivergencePrincipal A p) (w ∘ sphereChartCoordMap p) =
      fun y i ↦ roundCoordDensity y * ∑ j, intrinsicRealPrincipal A p y i j*
        Yau.coordPartial (w ∘ sphereChartCoordMap p) y j := by
    funext y i
    simp [realMatrixFlux,intrinsicDivergencePrincipal,Finset.mul_sum,mul_assoc]
  rw [hf]
  simpa only [intrinsicDivergencePotential,Function.comp_apply,mul_assoc] using hh

end
end Yau.Target

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
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_AnchoredCubeBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Analysis
open MeasureTheory Set Function
open scoped ENNReal ContDiff
noncomputable section
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] in
lemma inUnitCube_update {x : ι → ℝ} (hx : InUnitCube x)
    (i : ι) {t : ℝ} (ht : |t| ≤ 1) : InUnitCube (update x i t) := by
  intro j
  by_cases h : j = i
  · subst j; simpa using ht
  · simpa [update_of_ne h] using hx j

end
end Yau.Analysis

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

theorem real_inhomogeneous_differentiation
    (C : Yau.Jets.Coord → Matrix (Fin 4) (Fin 4) ℝ)
    (V W f : Yau.Jets.Coord → ℝ) (F : Yau.Jets.Coord → Yau.Jets.Coord)
    (hC : ∀ i j, ContDiff ℝ ∞ (fun x ↦ C x i j))
    (hV : ContDiff ℝ ∞ V) (hW : ContDiff ℝ ∞ W) (hf : ContDiff ℝ ∞ f)
    (hF : ∀ i, ContDiff ℝ ∞ (fun x ↦ F x i))
    (he : ∀ x, Yau.coordDiv (realMatrixFlux C W) x+V x*W x=Yau.coordDiv F x+f x)
    (k : Fin 4) :
    ∀ x, Yau.coordDiv (realMatrixFlux C (fun y ↦ Yau.coordPartial W y k)) x+
      V x*Yau.coordPartial W x k =
      Yau.coordDiv (fun y i ↦ Yau.coordPartial (fun z ↦ F z i) y k-realDerivativeErrorFlux C W k y i) x+
        (Yau.coordPartial f x k-Yau.coordPartial V x k*W x) := by
  have hflux := realMatrixFlux_smooth C W hC hW
  have hdiv : ContDiff ℝ ∞ (Yau.coordDiv (realMatrixFlux C W)) :=
    ContDiff.sum (fun i _ ↦ Yau.real_coordPartial_smooth _ (hflux i) i)
  have hdivF : ContDiff ℝ ∞ (Yau.coordDiv F) :=
    ContDiff.sum (fun i _ ↦ Yau.real_coordPartial_smooth _ (hF i) i)
  intro x
  have hd := congrArg (fun H : Yau.Jets.Coord → ℝ ↦ Yau.coordPartial H x k) (funext he)
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

theorem real_jet_error_equation (C : Yau.Jets.Coord → Matrix (Fin 4) (Fin 4) ℝ)
    (V W : Yau.Jets.Coord → ℝ) (hC : ∀ i j, ContDiff ℝ ∞ (fun x ↦ C x i j))
    (hV : ContDiff ℝ ∞ V) (hW : ContDiff ℝ ∞ W)
    (he : ∀ x, Yau.coordDiv (realMatrixFlux C W) x+V x*W x=0)
    (ds : List (Fin 4)) :
    ∀ x, Yau.coordDiv (realMatrixFlux C (partialJet W ds)) x+V x*partialJet W ds x =
      Yau.coordDiv (realJetErrorFlux C W ds) x+realJetErrorSource V W ds x := by
  induction ds with
  | nil =>
    intro x
    simpa [partialJet,realJetErrorFlux,realJetErrorSource,Yau.coordDiv,Yau.coordPartial] using he x
  | cons l ds ih =>
    exact real_inhomogeneous_differentiation C V (partialJet W ds) (realJetErrorSource V W ds)
      (realJetErrorFlux C W ds) hC hV (partialJet_smooth W hW ds)
      (realJetErrorSource_smooth V W hV hW ds) (realJetErrorFlux_smooth C W hC hW ds) ih l

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
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_RealJetCutoffEstimate
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

theorem real_jet_cutoff_estimate (k L M : ℝ) (hk : 0 < k) (hL : 0 < L) (hM : 0 ≤ M) :
    ∃ K > 0, ∀ (C : Yau.Jets.Coord → Matrix (Fin 4) (Fin 4) ℝ)
      (V W eta : Yau.Jets.Coord → ℝ),
      (∀ i j, ContDiff ℝ ∞ (fun x ↦ C x i j)) → ContDiff ℝ ∞ V →
      ContDiff ℝ ∞ W → ContDiff ℝ ∞ eta → HasCompactSupport eta →
      (∀ x i j, C x i j=C x j i) →
      (∀ x ∈ tsupport eta, ∀ z : Yau.Jets.Coord,
        k*(∑ i, z i^2) ≤ ∑ i, ∑ j, z i*C x i j*z j) →
      (∀ x ∈ tsupport eta, ∀ z : Yau.Jets.Coord,
        (∑ i, ∑ j, z i*C x i j*z j) ≤ L*(∑ i, z i^2)) →
      (∀ x ∈ tsupport eta, |V x| ≤ M) →
      (∀ x, Yau.coordDiv (realMatrixFlux C W) x+V x*W x=0) →
      ∀ ds : List (Fin 4),
      Integrable (fun x ↦ eta x^2*realGradientSquare (partialJet W ds) x) ∧
      Integrable (fun x ↦ (eta x^2+realGradientSquare eta x)*(partialJet W ds x)^2) ∧
      Integrable (fun x ↦ eta x^2*(realJetErrorSource V W ds x)^2) ∧
      Integrable (fun x ↦ eta x^2*(∑ i, (realJetErrorFlux C W ds x i)^2)) ∧
      (∫ x, eta x^2*realGradientSquare (partialJet W ds) x) ≤ K *
        ((∫ x, (eta x^2+realGradientSquare eta x)*(partialJet W ds x)^2)+
          (∫ x, eta x^2*(realJetErrorSource V W ds x)^2)+
          (∫ x, eta x^2*(∑ i, (realJetErrorFlux C W ds x i)^2))) := by
  obtain ⟨K,hK,h⟩ := real_inhomogeneous_caccioppoli k L M hk hL hM
  refine ⟨K,hK,?_⟩
  intro C V W eta hC hV hW heta hc hs hlo hhi hpot he ds
  exact h C V (partialJet W ds) (realJetErrorSource V W ds) eta (realJetErrorFlux C W ds)
    hC hV (partialJet_smooth W hW ds) (realJetErrorSource_smooth V W hV hW ds) heta
    (realJetErrorFlux_smooth C W hC hW ds) hc hs hlo hhi hpot
    (real_jet_error_equation C V W hC hV hW he ds)

end
end Yau.Geometry

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
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_RealJetClosedCutoff
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

theorem real_jet_closed_cutoff (n : ℕ) (k L M B : ℝ)
    (hk : 0 < k) (hL : 0 < L) (hM : 0 ≤ M) (hB : 0 ≤ B) :
    ∃ K > 0, ∀ (C : Yau.Jets.Coord → Matrix (Fin 4) (Fin 4) ℝ)
      (V W eta : Yau.Jets.Coord → ℝ),
      (∀ i j, ContDiff ℝ ∞ (fun x ↦ C x i j)) → ContDiff ℝ ∞ V →
      ContDiff ℝ ∞ W → ContDiff ℝ ∞ eta → HasCompactSupport eta →
      (∀ x i j, C x i j=C x j i) →
      (∀ x ∈ tsupport eta, ∀ z : Yau.Jets.Coord,
        k*(∑ i, z i^2) ≤ ∑ i, ∑ j, z i*C x i j*z j) →
      (∀ x ∈ tsupport eta, ∀ z : Yau.Jets.Coord,
        (∑ i, ∑ j, z i*C x i j*z j) ≤ L*(∑ i, z i^2)) →
      (∀ x ∈ tsupport eta, |V x| ≤ M) →
      (∀ x ∈ tsupport eta, ∀ es : List (Fin 4), es.length ≤ n →
        (∀ i j, |partialJet (fun y ↦ C y i j) es x| ≤ B) ∧ |partialJet V es x| ≤ B) →
      (∀ x, Yau.coordDiv (realMatrixFlux C W) x+V x*W x=0) →
      ∀ ds : List (Fin 4), ds.length ≤ n →
      Integrable (fun x ↦ eta x^2*realGradientSquare (partialJet W ds) x) ∧
      Integrable (fun x ↦ realCutoffWeight eta x*realFiniteJetSquare W n x) ∧
      (∫ x, eta x^2*realGradientSquare (partialJet W ds) x) ≤
        K*(∫ x, realCutoffWeight eta x*realFiniteJetSquare W n x) := by
  obtain ⟨K,hK,hcut⟩ := real_jet_cutoff_estimate k L M hk hL hM
  obtain ⟨E,hE,herror⟩ := real_jet_error_bound n B hB
  refine ⟨K*(1+E),by positivity,?_⟩
  intro C V W eta hC hV hW heta hc hs hlo hhi hpot hb he ds hd
  obtain ⟨hG,hI,hS,hF,hest⟩ := hcut C V W eta hC hV hW heta hc hs hlo hhi hpot he ds
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
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_RealJetSuccessorCutoff
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

theorem real_jet_successor_cutoff (n : ℕ) (k L M B : ℝ)
    (hk : 0 < k) (hL : 0 < L) (hM : 0 ≤ M) (hB : 0 ≤ B) :
    ∃ K > 0, ∀ (C : Yau.Jets.Coord → Matrix (Fin 4) (Fin 4) ℝ)
      (V W eta : Yau.Jets.Coord → ℝ),
      (∀ i j, ContDiff ℝ ∞ (fun x ↦ C x i j)) → ContDiff ℝ ∞ V →
      ContDiff ℝ ∞ W → ContDiff ℝ ∞ eta → HasCompactSupport eta →
      (∀ x i j, C x i j=C x j i) →
      (∀ x ∈ tsupport eta, ∀ z : Yau.Jets.Coord,
        k*(∑ i, z i^2) ≤ ∑ i, ∑ j, z i*C x i j*z j) →
      (∀ x ∈ tsupport eta, ∀ z : Yau.Jets.Coord,
        (∑ i, ∑ j, z i*C x i j*z j) ≤ L*(∑ i, z i^2)) →
      (∀ x ∈ tsupport eta, |V x| ≤ M) →
      (∀ x ∈ tsupport eta, ∀ es : List (Fin 4), es.length ≤ n →
        (∀ i j, |partialJet (fun y ↦ C y i j) es x| ≤ B) ∧ |partialJet V es x| ≤ B) →
      (∀ x, Yau.coordDiv (realMatrixFlux C W) x+V x*W x=0) →
      Integrable (fun x ↦ eta x^2*realFiniteJetSquare W (n+1) x) ∧
      Integrable (fun x ↦ realCutoffWeight eta x*realFiniteJetSquare W n x) ∧
      (∫ x, eta x^2*realFiniteJetSquare W (n+1) x) ≤
        K*(∫ x, realCutoffWeight eta x*realFiniteJetSquare W n x) := by
  obtain ⟨K,hK,hcut⟩ := real_jet_closed_cutoff n k L M B hk hL hM hB
  let N : ℝ := ∑ r ∈ Finset.range (n+2), (4:ℝ)^r
  have hN : 0 ≤ N := Finset.sum_nonneg (fun _ _ ↦ by positivity)
  refine ⟨N*(K+1)+1,by positivity,?_⟩
  intro C V W eta hC hV hW heta hc hs hlo hhi hpot hb he
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
      obtain ⟨hG,_,hest⟩ := hcut C V W eta hC hV hW heta hc hs hlo hhi hpot hb he ds (by simpa using hd)
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
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_RealNestedJetCutoff
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

theorem real_nested_jet_cutoff (n : ℕ) (k L M B : ℝ)
    (hk : 0 < k) (hL : 0 < L) (hM : 0 ≤ M) (hB : 0 ≤ B)
    (eta chi : Yau.Jets.Coord → ℝ) (heta : ContDiff ℝ ∞ eta) (hchi : ContDiff ℝ ∞ chi)
    (hce : HasCompactSupport eta) (hcc : HasCompactSupport chi)
    (hnest : ∀ x ∈ tsupport eta, chi x=1) :
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
      (∀ x, Yau.coordDiv (realMatrixFlux C W) x+V x*W x=0) →
      Integrable (fun x ↦ eta x^2*realFiniteJetSquare W (n+1) x) ∧
      Integrable (fun x ↦ chi x^2*realFiniteJetSquare W n x) ∧
      (∫ x, eta x^2*realFiniteJetSquare W (n+1) x) ≤
        K*(∫ x, chi x^2*realFiniteJetSquare W n x) := by
  obtain ⟨K,hK,hcut⟩ := real_jet_successor_cutoff n k L M B hk hL hM hB
  obtain ⟨D,hD,hweight⟩ := real_nested_cutoff_weight eta chi heta hce hnest
  refine ⟨K*D,by positivity,?_⟩
  intro C V W hC hV hW hs hlo hhi hpot hb he
  obtain ⟨hI,hJ,hest⟩ := hcut C V W eta hC hV hW heta hce hs hlo hhi hpot hb he
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

theorem real_interior_jet_estimate (n : ℕ) (k L M B : ℝ)
    (hk : 0 < k) (hL : 0 < L) (hM : 0 ≤ M) (hB : 0 ≤ B)
    (eta : ℕ → Yau.Jets.Coord → ℝ) (heta : ∀ j, ContDiff ℝ ∞ (eta j))
    (hc : ∀ j, HasCompactSupport (eta j))
    (hnest : ∀ j x, x ∈ tsupport (eta (j+1)) → eta j x=1) :
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
      (∀ x, Yau.coordDiv (realMatrixFlux C W) x+V x*W x=0) →
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
    obtain ⟨K1,hK1,hstep⟩ := real_nested_jet_cutoff n k L M B hk hL hM hB
      (eta (n+1)) (eta n) (heta (n+1)) (heta n) (hc (n+1)) (hc n) (hnest n)
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
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_RealBallJetEstimate
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Yau.Analysis MeasureTheory Metric
open scoped ContDiff
noncomputable section

theorem real_ball_jet_estimate (n : ℕ) (k L M B : ℝ)
    (hk : 0 < k) (hL : 0 < L) (hM : 0 ≤ M) (hB : 0 ≤ B)
    (y : Yau.Jets.Coord) (r R : ℝ) (hr : 0 < r) (hR : r < R) :
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
      (∀ x, Yau.coordDiv (realMatrixFlux C W) x+V x*W x=0) →
      IntegrableOn (realFiniteJetSquare W n) (closedBall y r) ∧
      IntegrableOn (fun x ↦ W x^2) (closedBall y R) ∧
      (∫ x in closedBall y r, realFiniteJetSquare W n x) ≤
        K*(∫ x in closedBall y R, W x^2) := by
  obtain ⟨eta,heta,hc,hval,hsupport,hone,hnest⟩ := real_ball_cutoff_chain y r R hr hR
  obtain ⟨K,hK,hest⟩ := real_interior_jet_estimate n k L M B hk hL hM hB eta heta hc hnest
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
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_CompactFamilyBallJetEstimate
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Yau.Analysis MeasureTheory Metric
open scoped ContDiff
noncomputable section
variable {T : Type*} [TopologicalSpace T] [CompactSpace T]

theorem compact_family_ball_jet_estimate (n : ℕ)
    (C : T → Yau.Jets.Coord → Matrix (Fin 4) (Fin 4) ℝ) (V : T → Yau.Jets.Coord → ℝ)
    (y : Yau.Jets.Coord) (r R : ℝ) (hr : 0 < r) (hR : r < R)
    (hC : ∀ t i j, ContDiff ℝ ∞ (fun x ↦ C t x i j)) (hV : ∀ t, ContDiff ℝ ∞ (V t))
    (hs : ∀ t x i j, C t x i j=C t x j i)
    (hp : ∀ t x, x ∈ closedBall y R → (C t x).PosDef)
    (hCjoint : ∀ i j ds, ds.length ≤ n → Continuous (fun z : T × closedBall y R ↦
      partialJet (fun x ↦ C z.1 x i j) ds z.2))
    (hVjoint : ∀ ds, ds.length ≤ n → Continuous (fun z : T × closedBall y R ↦
      partialJet (V z.1) ds z.2)) :
    ∃ K > 0, ∀ t (W : Yau.Jets.Coord → ℝ), ContDiff ℝ ∞ W →
      (∀ x, Yau.coordDiv (realMatrixFlux (C t) W) x+V t x*W x=0) →
      IntegrableOn (realFiniteJetSquare W n) (closedBall y r) ∧
      IntegrableOn (fun x ↦ W x^2) (closedBall y R) ∧
      (∫ x in closedBall y r, realFiniteJetSquare W n x) ≤
        K*(∫ x in closedBall y R, W x^2) := by
  obtain ⟨k,hk,L,hL,hell⟩ := compact_parameter_matrix_ellipticity C (isCompact_closedBall y R)
    (fun i j ↦ hCjoint i j [] (by simp)) hp
  obtain ⟨M,hM,hpot⟩ := compact_parameter_scalar_bound V (isCompact_closedBall y R) (hVjoint [] (by simp))
  obtain ⟨BC,hBC,hCd⟩ := compact_parameter_finite_jet_bound n
    (fun ij : Fin 4 × Fin 4 ↦ fun t x ↦ C t x ij.1 ij.2) (isCompact_closedBall y R)
    (fun ij ↦ hCjoint ij.1 ij.2)
  obtain ⟨BV,hBV,hVd⟩ := compact_parameter_finite_jet_bound n
    (fun _ : Unit ↦ V) (isCompact_closedBall y R) (fun _ ↦ hVjoint)
  obtain ⟨K,hK,hest⟩ := real_ball_jet_estimate n k L M (BC+BV) hk hL hM.le
    (by positivity) y r R hr hR
  refine ⟨K,hK,?_⟩
  intro t W hW he
  apply hest (C t) (V t) W (hC t) (hV t) hW (hs t)
    (fun x hx z ↦ (hell t x hx z).1) (fun x hx z ↦ (hell t x hx z).2) (hpot t) _ he
  intro x hx ds hd
  exact ⟨fun i j ↦ (hCd (i,j) t x hx ds hd).trans (by linarith),
    (hVd () t x hx ds hd).trans (by linarith)⟩

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_RealIntervalL2Embedding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open MeasureTheory Set
open scoped ContDiff
noncomputable section

lemma real_interval_square_variation (f : ℝ → ℝ) (hf : ContDiff ℝ ∞ f)
    (a b : ℝ) (ha : a ∈ Icc (-1:ℝ) 1) (hb : b ∈ Icc (-1:ℝ) 1) :
    |f b^2-f a^2| ≤ ∫ t in Icc (-1:ℝ) 1, (f t^2+(deriv f t)^2) := by
  have hcont : Continuous (fun t ↦ f t^2+(deriv f t)^2) :=
    (hf.continuous.pow 2).add ((hf.continuous_deriv (by simp)).pow 2)
  have hpos (t : ℝ) : 0 ≤ f t^2+(deriv f t)^2 := add_nonneg (sq_nonneg _) (sq_nonneg _)
  have hder (t : ℝ) : ‖deriv (fun s ↦ f s^2) t‖ ≤ f t^2+(deriv f t)^2 := by
    have he : deriv (fun s ↦ f s^2) t = 2*f t*deriv f t := by
      simpa only [Pi.pow_apply,Nat.cast_ofNat,show 2-1=1 from rfl,pow_one] using
        ((hf.differentiable (by simp) t).hasDerivAt.fun_pow 2).deriv
    rw [he,Real.norm_eq_abs]
    exact abs_le.mpr ⟨by nlinarith [sq_nonneg (f t+deriv f t)],
      by nlinarith [sq_nonneg (f t-deriv f t)]⟩
  have hordered (c d : ℝ) (hc : c ∈ Icc (-1:ℝ) 1) (hd : d ∈ Icc (-1:ℝ) 1)
      (hcd : c ≤ d) : |f d^2-f c^2| ≤ ∫ t in Icc (-1:ℝ) 1, (f t^2+(deriv f t)^2) := by
    have h := norm_sub_le_integral_of_norm_deriv_le_of_le hcd
      (hf.pow 2).continuous.continuousOn ((hf.pow 2).differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).differentiableOn
      (Filter.Eventually.of_forall (fun t _ ↦ hder t)) (hcont.intervalIntegrable c d)
    rw [intervalIntegral.integral_of_le hcd] at h
    have hm : (∫ t in Ioc c d, (f t^2+(deriv f t)^2)) ≤
        ∫ t in Icc (-1:ℝ) 1, (f t^2+(deriv f t)^2) := by
      apply setIntegral_mono_set (hcont.continuousOn.integrableOn_compact isCompact_Icc)
        (Filter.Eventually.of_forall hpos)
      exact Filter.Eventually.of_forall (fun t ht ↦ ⟨hc.1.trans ht.1.le,ht.2.trans hd.2⟩)
    have hh : |f d^2-f c^2| ≤ ∫ t in Ioc c d, (f t^2+(deriv f t)^2) := by
      simpa only [Real.norm_eq_abs] using h
    exact hh.trans hm
  rcases le_total a b with hab | hba
  · exact hordered a b ha hb hab
  · simpa only [abs_sub_comm] using hordered b a hb ha hba

theorem real_interval_l2_embedding (f : ℝ → ℝ) (hf : ContDiff ℝ ∞ f)
    (x : ℝ) (hx : x ∈ Icc (-1:ℝ) 1) :
    f x^2 ≤ 2*(∫ t in Icc (-1:ℝ) 1, (f t^2+(deriv f t)^2)) := by
  have hfi : IntegrableOn (fun t ↦ f t^2) (Icc (-1:ℝ) 1) :=
    (hf.continuous.pow 2).continuousOn.integrableOn_compact isCompact_Icc
  have hdi : IntegrableOn (fun t ↦ (deriv f t)^2) (Icc (-1:ℝ) 1) :=
    ((hf.continuous_deriv (by simp)).pow 2).continuousOn.integrableOn_compact isCompact_Icc
  obtain ⟨y,hy,hmin⟩ := isCompact_Icc.exists_isMinOn (show (Icc (-1:ℝ) 1).Nonempty from ⟨0,by norm_num⟩)
    (hf.continuous.pow 2).continuousOn
  have hm := setIntegral_mono_on
    (integrableOn_const (isCompact_Icc.measure_ne_top (μ := volume))) hfi measurableSet_Icc
    (fun t ht ↦ hmin ht)
  have hm' : 2*f y^2 ≤ ∫ t in Icc (-1:ℝ) 1, f t^2 := by
    norm_num at hm
    exact hm
  have hd : 0 ≤ ∫ t in Icc (-1:ℝ) 1, (deriv f t)^2 := integral_nonneg (fun t ↦ sq_nonneg _)
  have hv := (le_abs_self (f x^2-f y^2)).trans (real_interval_square_variation f hf y x hy hx)
  rw [integral_add hfi hdi] at hv ⊢
  nlinarith [sq_nonneg (f y)]

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_RealCubeL2Control
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Yau.Analysis MeasureTheory Set Function
open scoped ContDiff
noncomputable section

lemma real_coordinate_update_continuous (i : Fin 4) :
    Continuous (fun z : Yau.Jets.Coord × ℝ ↦ update z.1 i z.2) := by
  apply continuous_pi
  intro j
  by_cases hj : j=i
  · subst j; simpa using (continuous_snd : Continuous (fun z : Yau.Jets.Coord × ℝ ↦ z.2))
  · simpa only [update_of_ne hj,Function.comp_def] using (continuous_apply j).comp
      (continuous_fst : Continuous (fun z : Yau.Jets.Coord × ℝ ↦ z.1))

lemma realCubeL2Control_continuous (W : Yau.Jets.Coord → ℝ) (hW : ContDiff ℝ ∞ W)
    (is ds : List (Fin 4)) : Continuous (realCubeL2Control W is ds) := by
  induction is generalizing ds with
  | nil => exact ((partialJet_smooth W hW ds).pow 2).continuous
  | cons i is ih =>
    apply continuous_const.mul
    apply continuous_parametric_integral_of_continuous _ isCompact_Icc
    exact ((ih ds).comp (real_coordinate_update_continuous i)).add
      ((ih (i::ds)).comp (real_coordinate_update_continuous i))

theorem partialJet_sq_le_realCubeL2Control (W : Yau.Jets.Coord → ℝ) (hW : ContDiff ℝ ∞ W)
    (is ds : List (Fin 4)) (x : Yau.Jets.Coord) (hx : InUnitCube x) :
    (partialJet W ds x)^2 ≤ realCubeL2Control W is ds x := by
  induction is generalizing ds x with
  | nil => exact le_rfl
  | cons i is ih =>
    have hd (t : ℝ) : deriv (fun s ↦ partialJet W ds (update x i s)) t =
        partialJet W (i::ds) (update x i t) := by
      change deriv (partialJet W ds ∘ update x i) t = _
      rw [((partialJet_smooth W hW ds).differentiable (by simp) (update x i t)).hasFDerivAt.comp_hasDerivAt t
        (hasDerivAt_update x i t) |>.deriv]
      rfl
    have h := real_interval_l2_embedding (fun t ↦ partialJet W ds (update x i t))
      ((partialJet_smooth W hW ds).comp (contDiff_update ∞ x i)) (x i) (abs_le.mp (hx i))
    simp only [update_eq_self] at h
    simp_rw [hd] at h
    have hc (es : List (Fin 4)) : Continuous (fun t ↦ partialJet W es (update x i t)) :=
      (partialJet_smooth W hW es).continuous.comp (contDiff_update (𝕜 := ℝ) ∞ x i).continuous
    have hc' (es : List (Fin 4)) : Continuous (fun t ↦ realCubeL2Control W is es (update x i t)) :=
      (realCubeL2Control_continuous W hW is es).comp (contDiff_update (𝕜 := ℝ) ∞ x i).continuous
    have hm := setIntegral_mono_on (μ := volume)
      (((hc ds).pow 2).add ((hc (i::ds)).pow 2)).continuousOn.integrableOn_Icc
      ((hc' ds).add (hc' (i::ds))).continuousOn.integrableOn_Icc measurableSet_Icc
      (fun t ht ↦ add_le_add
        (ih ds _ (inUnitCube_update hx i (abs_le.mpr ht)))
        (ih (i::ds) _ (inUnitCube_update hx i (abs_le.mpr ht))))
    exact h.trans (mul_le_mul_of_nonneg_left hm (by norm_num))

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_RealCubeAverage
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Yau.Analysis MeasureTheory Set Function
open scoped ContDiff
noncomputable section

lemma realCubeAverage_continuous (F : Yau.Jets.Coord → ℝ) (hF : Continuous F)
    (is : List (Fin 4)) : Continuous (realCubeAverage F is) := by
  induction is with
  | nil => exact hF
  | cons i is ih =>
    apply continuous_parametric_integral_of_continuous _ isCompact_Icc
    exact ih.comp (real_coordinate_update_continuous i)

theorem realCubeL2Control_le_average (W : Yau.Jets.Coord → ℝ) (hW : ContDiff ℝ ∞ W)
    (n : ℕ) (is ds : List (Fin 4)) (hd : ds.length+is.length ≤ n) (x : Yau.Jets.Coord) :
    realCubeL2Control W is ds x ≤
      4^is.length * realCubeAverage (realFiniteJetSquare W n) is x := by
  induction is generalizing ds x with
  | nil => simpa [realCubeL2Control,realCubeAverage] using
      partialJet_sq_le_realFiniteJetSquare W n ds (by simpa using hd) x
  | cons i is ih =>
    have hi (es : List (Fin 4)) : IntegrableOn
        (fun t ↦ realCubeL2Control W is es (update x i t)) (Icc (-1:ℝ) 1) :=
      ((realCubeL2Control_continuous W hW is es).comp
        (contDiff_update (𝕜 := ℝ) ∞ x i).continuous).continuousOn.integrableOn_Icc
    have ha : IntegrableOn
        (fun t ↦ realCubeAverage (realFiniteJetSquare W n) is (update x i t))
        (Icc (-1:ℝ) 1) :=
      ((realCubeAverage_continuous _ (realFiniteJetSquare_smooth W hW n).continuous is).comp
        (contDiff_update (𝕜 := ℝ) ∞ x i).continuous).continuousOn.integrableOn_Icc
    have hm := setIntegral_mono_on (μ := volume) ((hi ds).add (hi (i::ds)))
      ((ha.const_mul (4^is.length)).add (ha.const_mul (4^is.length))) measurableSet_Icc
      (fun t _ ↦ add_le_add (ih ds (by simpa using (show ds.length+is.length ≤ n by
          simp only [List.length_cons] at hd; omega)) _)
        (ih (i::ds) (by simp only [List.length_cons] at hd ⊢; omega) _))
    simp only [Pi.add_apply,integral_add (ha.const_mul _) (ha.const_mul _),
      integral_const_mul] at hm
    change 2 * _ ≤ _
    calc
      _ ≤ 2*(4^is.length * (∫ t in Icc (-1:ℝ) 1,
          realCubeAverage (realFiniteJetSquare W n) is (update x i t)) +
        4^is.length * (∫ t in Icc (-1:ℝ) 1,
          realCubeAverage (realFiniteJetSquare W n) is (update x i t))) :=
        mul_le_mul_of_nonneg_left hm (by norm_num)
      _ = _ := by simp only [List.length_cons,realCubeAverage,pow_succ] <;> ring

end
end Yau.Geometry

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

theorem realFinCube_integral_four (F : Yau.Jets.Coord → ℝ) (hF : Continuous F) :
    (∫ z in realFinCube 4, F z) =
      ∫ a in Icc (-1:ℝ) 1, ∫ b in Icc (-1:ℝ) 1,
        ∫ c in Icc (-1:ℝ) 1, ∫ d in Icc (-1:ℝ) 1, F ![a,b,c,d] := by
  rw [realFinCube_integral_succ 3 F hF]
  apply integral_congr_ae
  filter_upwards [] with a
  have ha : Continuous (fun z : Fin 3 → ℝ ↦ F (Fin.cons a z)) :=
    hF.comp (continuous_const.finCons continuous_id)
  rw [realFinCube_integral_succ 2 _ ha]
  apply integral_congr_ae
  filter_upwards [] with b
  have hb : Continuous (fun z : Fin 2 → ℝ ↦ F (Fin.cons a (Fin.cons b z))) :=
    ha.comp (continuous_const.finCons continuous_id)
  rw [realFinCube_integral_succ 1 _ hb]
  apply integral_congr_ae
  filter_upwards [] with c
  have hc : Continuous (fun z : Fin 1 → ℝ ↦ F (Fin.cons a (Fin.cons b (Fin.cons c z)))) :=
    hb.comp (continuous_const.finCons continuous_id)
  rw [realFinCube_integral_succ 0 _ hc]
  apply integral_congr_ae
  filter_upwards [] with d
  rw [realFinCube_integral_zero]
  rfl

theorem realCubeAverage_all (F : Yau.Jets.Coord → ℝ) (hF : Continuous F)
    (x : Yau.Jets.Coord) :
    realCubeAverage F [0,1,2,3] x = ∫ z in closedBall (0 : Yau.Jets.Coord) 1, F z := by
  rw [← realFinCube_four_eq_closedBall,realFinCube_integral_four F hF]
  simp only [realCubeAverage]
  apply integral_congr_ae
  filter_upwards [] with a
  apply integral_congr_ae
  filter_upwards [] with b
  apply integral_congr_ae
  filter_upwards [] with c
  apply integral_congr_ae
  filter_upwards [] with d
  congr 1
  ext i
  fin_cases i <;> simp

theorem real_cube_l2_embedding (W : Yau.Jets.Coord → ℝ) (hW : ContDiff ℝ ∞ W)
    (ds : List (Fin 4)) (x : Yau.Jets.Coord) (hx : InUnitCube x) :
    (partialJet W ds x)^2 ≤ 256 * (∫ z in closedBall (0 : Yau.Jets.Coord) 1,
      realFiniteJetSquare W (ds.length+4) z) := by
  have h := (partialJet_sq_le_realCubeL2Control W hW [0,1,2,3] ds x hx).trans
    (realCubeL2Control_le_average W hW (ds.length+4) [0,1,2,3] ds (by simp) x)
  rw [realCubeAverage_all _ (realFiniteJetSquare_smooth W hW _).continuous] at h
  norm_num at h ⊢
  exact h

open MeasureTheory Set Function

end Yau.Geometry

end

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_RealTranslatedJetEmbedding
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Yau.Analysis MeasureTheory Set Function Metric
open scoped ContDiff
noncomputable section

lemma partialJet_translate (W : Yau.Jets.Coord → ℝ) (a : Yau.Jets.Coord)
    (ds : List (Fin 4)) (x : Yau.Jets.Coord) :
    partialJet (fun z ↦ W (a+z)) ds x = partialJet W ds (a+x) := by
  induction ds generalizing x with
  | nil => rfl
  | cons i ds ih =>
    have he : partialJet (fun z ↦ W (a+z)) ds = fun z ↦ partialJet W ds (a+z) := funext ih
    change fderiv ℝ (partialJet (fun z ↦ W (a+z)) ds) x _ = _
    rw [he,fderiv_comp_add_left]
    rfl

lemma realFiniteJetSquare_translate (W : Yau.Jets.Coord → ℝ) (a : Yau.Jets.Coord)
    (n : ℕ) (x : Yau.Jets.Coord) :
    realFiniteJetSquare (fun z ↦ W (a+z)) n x = realFiniteJetSquare W n (a+x) := by
  simp only [realFiniteJetSquare,partialJet_translate]

lemma real_integral_ball_translate (F : Yau.Jets.Coord → ℝ) (a : Yau.Jets.Coord) (r : ℝ) :
    (∫ z in closedBall (0 : Yau.Jets.Coord) r, F (a+z)) = ∫ z in closedBall a r, F z := by
  have hs : (fun z : Yau.Jets.Coord ↦ a+z) ⁻¹' closedBall a r = closedBall 0 r := by
    ext z
    simp only [mem_preimage,mem_closedBall,dist_self_add_left,dist_zero_right]
  rw [← hs]
  exact (measurePreserving_add_left volume a).setIntegral_preimage_emb
    (MeasurableEquiv.addLeft a).measurableEmbedding F _

theorem real_point_jet_l2_embedding (W : Yau.Jets.Coord → ℝ) (hW : ContDiff ℝ ∞ W)
    (ds : List (Fin 4)) (x : Yau.Jets.Coord) :
    (partialJet W ds x)^2 ≤ 256 * (∫ z in closedBall x 1,
      realFiniteJetSquare W (ds.length+4) z) := by
  have h := real_cube_l2_embedding (fun z ↦ W (x+z))
    (hW.comp (contDiff_const.add contDiff_id)) ds 0 (by intro i; simp)
  simp only [partialJet_translate,add_zero,realFiniteJetSquare_translate,
    real_integral_ball_translate] at h
  exact h

theorem real_uniform_jet_l2_embedding (W : Yau.Jets.Coord → ℝ) (hW : ContDiff ℝ ∞ W)
    (n : ℕ) (y : Yau.Jets.Coord) (r : ℝ) (ds : List (Fin 4)) (hd : ds.length ≤ n)
    (x : Yau.Jets.Coord) (hx : x ∈ closedBall y r) :
    (partialJet W ds x)^2 ≤ 256 * (∫ z in closedBall y (r+1), realFiniteJetSquare W (n+4) z) := by
  have hsub : closedBall x 1 ⊆ closedBall y (r+1) := by
    intro z hz
    exact (dist_triangle z x y).trans (by linarith [mem_closedBall.mp hz,mem_closedBall.mp hx])
  have hs (z : Yau.Jets.Coord) : realFiniteJetSquare W (ds.length+4) z ≤ realFiniteJetSquare W (n+4) z := by
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega))
    intro a _ _
    exact Finset.sum_nonneg (fun _ _ ↦ sq_nonneg _)
  have hi (m : ℕ) (a : Yau.Jets.Coord) (s : ℝ) :
      IntegrableOn (realFiniteJetSquare W m) (closedBall a s) :=
    (realFiniteJetSquare_smooth W hW m).continuous.continuousOn.integrableOn_compact (isCompact_closedBall a s)
  have hmono := (setIntegral_mono_on (hi (ds.length+4) x 1) (hi (n+4) x 1)
    isClosed_closedBall.measurableSet (fun z _ ↦ hs z)).trans
    (setIntegral_mono_set (hi (n+4) y (r+1))
      (Filter.Eventually.of_forall (realFiniteJetSquare_nonneg W (n+4)))
      (Filter.Eventually.of_forall hsub))
  exact (real_point_jet_l2_embedding W hW ds x).trans
    (mul_le_mul_of_nonneg_left hmono (by norm_num))

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_CompactFamilyPointwiseEstimate
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Yau.Analysis MeasureTheory Metric
open scoped ContDiff
noncomputable section
variable {T : Type*} [TopologicalSpace T] [CompactSpace T]

theorem compact_family_pointwise_estimate (n : ℕ)
    (C : T → Yau.Jets.Coord → Matrix (Fin 4) (Fin 4) ℝ) (V : T → Yau.Jets.Coord → ℝ)
    (y : Yau.Jets.Coord) (r : ℝ) (hr : 0 ≤ r)
    (hC : ∀ t i j, ContDiff ℝ ∞ (fun x ↦ C t x i j)) (hV : ∀ t, ContDiff ℝ ∞ (V t))
    (hs : ∀ t x i j, C t x i j=C t x j i)
    (hp : ∀ t x, x ∈ closedBall y (r+2) → (C t x).PosDef)
    (hCjoint : ∀ i j ds, ds.length ≤ n+4 → Continuous (fun z : T × closedBall y (r+2) ↦
      partialJet (fun x ↦ C z.1 x i j) ds z.2))
    (hVjoint : ∀ ds, ds.length ≤ n+4 → Continuous (fun z : T × closedBall y (r+2) ↦
      partialJet (V z.1) ds z.2)) :
    ∃ K > 0, ∀ t (W : Yau.Jets.Coord → ℝ), ContDiff ℝ ∞ W →
      (∀ x, Yau.coordDiv (realMatrixFlux (C t) W) x+V t x*W x=0) →
      ∀ ds : List (Fin 4), ds.length ≤ n → ∀ x ∈ closedBall y r,
        (partialJet W ds x)^2 ≤ K*(∫ z in closedBall y (r+2), W z^2) := by
  obtain ⟨K,hK,hest⟩ := compact_family_ball_jet_estimate (n+4) C V y (r+1) (r+2)
    (by linarith) (by linarith) hC hV hs hp hCjoint hVjoint
  refine ⟨256*K,by positivity,?_⟩
  intro t W hW he ds hd x hx
  exact (real_uniform_jet_l2_embedding W hW n y r ds hd x hx).trans
    ((mul_le_mul_of_nonneg_left (hest t W hW he).2.2 (by norm_num : (0:ℝ) ≤ 256)).trans_eq (by ring))

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
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_RealJetLimitDerivative
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

theorem real_jet_limit_hasFDerivAt (W : ℕ → Yau.Jets.Coord → ℝ)
    (hW : ∀ j, ContDiff ℝ ∞ (W j)) (g : List (Fin 4) → Yau.Jets.Coord → ℝ)
    (ht : ∀ ds (Q : Set Yau.Jets.Coord), IsCompact Q →
      TendstoUniformlyOn (fun j ↦ partialJet (W j) ds) (g ds) atTop Q)
    (ds : List (Fin 4)) (x : Yau.Jets.Coord) :
    HasFDerivAt (g ds) (realCoordinateDual (fun i ↦ g (i::ds) x)) x := by
  have hu := real_uniform_coordinate_dual (fun i ↦ ht (i::ds) (closedBall x 1) (isCompact_closedBall x 1))
  apply hasFDerivAt_of_tendstoUniformlyOn isOpen_ball (hu.mono ball_subset_closedBall)
    (f := fun j ↦ partialJet (W j) ds)
  · intro j y _
    change HasFDerivAt (partialJet (W j) ds)
      (realCoordinateDual (fun i ↦ fderiv ℝ (partialJet (W j) ds) y (Pi.single i 1))) y
    rw [← real_fderiv_coordinateDual]
    exact ((partialJet_smooth _ (hW j) ds).differentiable (by simp) y).hasFDerivAt
  · intro y _
    exact (ht ds {y} isCompact_singleton).tendsto_at (mem_singleton y)
  · exact mem_ball_self (by norm_num)

theorem real_jet_limit_smooth (g : List (Fin 4) → Yau.Jets.Coord → ℝ)
    (hc : ∀ ds, Continuous (g ds))
    (hd : ∀ ds x, HasFDerivAt (g ds) (realCoordinateDual (fun i ↦ g (i::ds) x)) x) :
    ∀ ds, ContDiff ℝ ∞ (g ds) := by
  have hn (n : ℕ) : ∀ ds, ContDiff ℝ n (g ds) := by
    induction n with
    | zero => intro ds; exact contDiff_zero.mpr (hc ds)
    | succ n ih =>
      intro ds
      rw [show ((n+1:ℕ) : ℕ∞ω) = (n:ℕ∞ω)+1 by simp,contDiff_succ_iff_fderiv]
      refine ⟨fun x ↦ (hd ds x).differentiableAt,by simp,?_⟩
      have he : fderiv ℝ (g ds) = fun x ↦ realCoordinateDual (fun i ↦ g (i::ds) x) :=
        funext (fun x ↦ (hd ds x).fderiv)
      rw [he]
      exact realCoordinateDual.contDiff.comp (contDiff_pi.mpr (fun i ↦ ih (i::ds)))
  intro ds
  exact contDiff_infty.mpr (fun n ↦ hn n ds)

theorem real_jet_limit_identification (g : List (Fin 4) → Yau.Jets.Coord → ℝ)
    (hd : ∀ ds x, HasFDerivAt (g ds) (realCoordinateDual (fun i ↦ g (i::ds) x)) x)
    (ds : List (Fin 4)) : partialJet (g []) ds = g ds := by
  induction ds with
  | nil => rfl
  | cons i ds ih =>
    funext x
    change fderiv ℝ (partialJet (g []) ds) x (Pi.single i 1) = _
    rw [ih,(hd ds x).fderiv,realCoordinateDual_single]

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_RealJetUniformDerivative
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

lemma iteratedFDeriv_coordinate_apply (W : Yau.Jets.Coord → ℝ) (hW : ContDiff ℝ ∞ W)
    (n : ℕ) (w : Fin n → Fin 4) (x : Yau.Jets.Coord) :
    iteratedFDeriv ℝ n W x (fun j ↦ Pi.single (w j) 1) = partialJet W (List.ofFn w) x := by
  have he := partialJet_eq_iterated W hW (List.ofFn w) x
  simp only [partialDirs_eq_get,List.get_eq_getElem,List.getElem_ofFn] at he
  have aux (m : ℕ) (hm : m=n) :
      iteratedFDeriv ℝ m W x (fun j ↦ Pi.single (w (Fin.cast hm j)) 1) =
        iteratedFDeriv ℝ n W x (fun j ↦ Pi.single (w j) 1) := by
    subst m
    rfl
  exact (he.trans (aux _ List.length_ofFn)).symm

theorem real_uniform_iteratedFDeriv (W : ℕ → Yau.Jets.Coord → ℝ) (v : Yau.Jets.Coord → ℝ)
    (hW : ∀ j, ContDiff ℝ ∞ (W j)) (hv : ContDiff ℝ ∞ v) (n : ℕ) (Q : Set Yau.Jets.Coord)
    (ht : ∀ ds : List (Fin 4), ds.length=n →
      TendstoUniformlyOn (fun j ↦ partialJet (W j) ds) (partialJet v ds) atTop Q) :
    TendstoUniformlyOn (fun j ↦ iteratedFDeriv ℝ n (W j)) (iteratedFDeriv ℝ n v) atTop Q := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  let δ := ε/(4^n+1)
  have hp : (0:ℝ) < 4^n+1 := by positivity
  have hδ : 0 < δ := div_pos hε hp
  have hh (w : Fin n → Fin 4) := Metric.tendstoUniformlyOn_iff.mp
    (ht (List.ofFn w) List.length_ofFn) δ hδ
  filter_upwards [Filter.eventually_all.mpr hh] with j hj x hx
  rw [dist_eq_norm]
  have hb : ‖iteratedFDeriv ℝ n v x - iteratedFDeriv ℝ n (W j) x‖ ≤ 4^n*δ := by
    apply real_coordinate_multilinear_norm n _ δ hδ.le
    intro w
    simpa only [sub_apply,iteratedFDeriv_coordinate_apply v hv,
      iteratedFDeriv_coordinate_apply (W j) (hW j),← dist_eq_norm] using (hj w x hx).le
  apply hb.trans_lt
  calc
    4^n*δ < (4^n+1)*δ := mul_lt_mul_of_pos_right (lt_add_one _) hδ
    _ = ε := by dsimp [δ]; field_simp

end
end Yau.Geometry

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

theorem real_jet_ball_subsequence (W : ℕ → Yau.Jets.Coord → ℝ)
    (hW : ∀ j, ContDiff ℝ ∞ (W j))
    (hb : ∀ R n : ℕ, ∃ B ≥ 0, ∀ j (ds : List (Fin 4)), ds.length ≤ n →
      ∀ x ∈ closedBall (0 : Yau.Jets.Coord) (R:ℝ), |partialJet (W j) ds x| ≤ B) :
    ∃ f : ∀ R : ℕ, List (Fin 4) → closedBall (0 : Yau.Jets.Coord) (R:ℝ) → ℝ,
      (∀ R ds, Continuous (f R ds)) ∧ ∃ nu : ℕ → ℕ, StrictMono nu ∧ ∀ (R : ℕ) (ds : List (Fin 4)),
        TendstoUniformly (fun j (x : closedBall (0 : Yau.Jets.Coord) (R:ℝ)) ↦
          partialJet (W (nu j)) ds x) (f R ds) atTop := by
  choose B hB hbound using hb
  let X (i : ℕ × List (Fin 4)) := closedBall (0 : Yau.Jets.Coord) (i.1:ℝ)
  let F (i : ℕ × List (Fin 4)) (j : ℕ) (x : X i) := partialJet (W j) i.2 x
  let C (i : ℕ × List (Fin 4)) : ℝ≥0 := ⟨B i.1 (i.2.length+1),hB _ _⟩
  have hval (i : ℕ × List (Fin 4)) (j : ℕ) (x : X i) : |F i j x| ≤ (C i:ℝ) :=
    hbound _ _ j _ (by omega) x x.property
  have hLip (i : ℕ × List (Fin 4)) (j : ℕ) : LipschitzWith (4*C i) (F i j) := by
    apply LipschitzOnWith.to_restrict
    apply real_partialJet_lipschitz (W j) (hW j) i.2 0 (i.1:ℝ) (C i)
    intro k x hx
    exact hbound _ _ j _ (by simp) x hx
  obtain ⟨f,hf,nu,hnu,ht⟩ := real_countable_uniform_subsequence F (fun i ↦ (C i:ℝ))
    (fun i ↦ 4*C i) hval hLip
  exact ⟨fun R ds ↦ f (R,ds),fun R ds ↦ hf (R,ds),nu,hnu,fun R ds ↦ ht (R,ds)⟩

end Yau.Geometry

end

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_RealCompatibleBallLimits
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Set Metric Filter
open scoped Topology
noncomputable section

theorem real_compatible_ball_limits (W : ℕ → Yau.Jets.Coord → ℝ)
    (hW : ∀ j, Continuous (W j))
    (f : ∀ R : ℕ, closedBall (0 : Yau.Jets.Coord) (R:ℝ) → ℝ)
    (ht : ∀ R : ℕ, TendstoUniformly (fun j (x : closedBall (0 : Yau.Jets.Coord) (R:ℝ)) ↦ W j x)
      (f R) atTop) :
    ∃ g : Yau.Jets.Coord → ℝ, Continuous g ∧
      ∀ Q : Set Yau.Jets.Coord, IsCompact Q → TendstoUniformlyOn W g atTop Q := by
  choose R hR using (fun x : Yau.Jets.Coord ↦ exists_nat_gt ‖x‖)
  have hx (x : Yau.Jets.Coord) : x ∈ closedBall (0 : Yau.Jets.Coord) (R x:ℝ) := by
    simpa only [mem_closedBall,dist_zero_right] using (hR x).le
  let g (x : Yau.Jets.Coord) : ℝ := f (R x) ⟨x,hx x⟩
  have he (n : ℕ) (x : closedBall (0 : Yau.Jets.Coord) (n:ℝ)) : f n x = g x :=
    tendsto_nhds_unique ((ht n).tendsto_at x) ((ht (R x)).tendsto_at ⟨x,hx x⟩)
  have hu (n : ℕ) : TendstoUniformlyOn W g atTop (closedBall (0 : Yau.Jets.Coord) (n:ℝ)) := by
    rw [tendstoUniformlyOn_iff_restrict]
    have heq : f n = fun x : closedBall (0 : Yau.Jets.Coord) (n:ℝ) ↦ g x := funext (he n)
    change TendstoUniformly (fun j (x : closedBall (0 : Yau.Jets.Coord) (n:ℝ)) ↦ W j x)
      (fun x ↦ g x) atTop
    rw [← heq]
    exact ht n
  have hc : Continuous g := by
    rw [continuous_iff_continuousAt]
    intro x
    have hcont := (hu (R x)).continuousOn (Filter.Eventually.frequently (Filter.Eventually.of_forall (fun j ↦ (hW j).continuousOn)))
    exact hcont.continuousAt (closedBall_mem_nhds_of_mem (by
      simpa only [mem_ball,dist_zero_right] using hR x))
  refine ⟨g,hc,?_⟩
  intro Q hQ
  obtain ⟨r,hr⟩ := hQ.isBounded.subset_closedBall (0 : Yau.Jets.Coord)
  obtain ⟨n,hn⟩ := exists_nat_gt r
  exact (hu n).mono (hr.trans (closedBall_subset_closedBall hn.le))

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_RealLocalJetLimits
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

theorem real_local_jet_limits (W : ℕ → Yau.Jets.Coord → ℝ)
    (hW : ∀ j, ContDiff ℝ ∞ (W j))
    (hb : ∀ R n : ℕ, ∃ B ≥ 0, ∀ j (ds : List (Fin 4)), ds.length ≤ n →
      ∀ x ∈ closedBall (0 : Yau.Jets.Coord) (R:ℝ), |partialJet (W j) ds x| ≤ B) :
    ∃ g : List (Fin 4) → Yau.Jets.Coord → ℝ, (∀ ds, Continuous (g ds)) ∧
      ∃ nu : ℕ → ℕ, StrictMono nu ∧ ∀ ds (Q : Set Yau.Jets.Coord), IsCompact Q →
        TendstoUniformlyOn (fun j ↦ partialJet (W (nu j)) ds) (g ds) atTop Q := by
  obtain ⟨f,_,nu,hnu,ht⟩ := real_jet_ball_subsequence W hW hb
  have hh (ds : List (Fin 4)) := real_compatible_ball_limits
    (fun j ↦ partialJet (W (nu j)) ds) (fun j ↦ (partialJet_smooth _ (hW _) ds).continuous)
    (fun R ↦ f R ds) (fun R ↦ ht R ds)
  choose g hg hconv using hh
  exact ⟨g,hg,nu,hnu,hconv⟩

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_RealSmoothLocalCompactness
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

theorem real_smooth_local_subsequence (W : ℕ → Yau.Jets.Coord → ℝ)
    (hW : ∀ j, ContDiff ℝ ∞ (W j))
    (hb : ∀ R n : ℕ, ∃ B ≥ 0, ∀ j (ds : List (Fin 4)), ds.length ≤ n →
      ∀ x ∈ closedBall (0 : Yau.Jets.Coord) (R:ℝ), |partialJet (W j) ds x| ≤ B) :
    ∃ v : Yau.Jets.Coord → ℝ, ContDiff ℝ ∞ v ∧ ∃ nu : ℕ → ℕ, StrictMono nu ∧
      (∀ ds (Q : Set Yau.Jets.Coord), IsCompact Q →
        TendstoUniformlyOn (fun j ↦ partialJet (W (nu j)) ds) (partialJet v ds) atTop Q) ∧
      (∀ n (Q : Set Yau.Jets.Coord), IsCompact Q →
        TendstoUniformlyOn (fun j ↦ iteratedFDeriv ℝ n (W (nu j)))
          (iteratedFDeriv ℝ n v) atTop Q) := by
  obtain ⟨g,hg,nu,hnu,ht⟩ := real_local_jet_limits W hW hb
  have hd := real_jet_limit_hasFDerivAt (fun j ↦ W (nu j)) (fun j ↦ hW (nu j)) g ht
  have hs := real_jet_limit_smooth g hg hd
  have hi := real_jet_limit_identification g hd
  have hu (ds : List (Fin 4)) (Q : Set Yau.Jets.Coord) (hQ : IsCompact Q) :
      TendstoUniformlyOn (fun j ↦ partialJet (W (nu j)) ds) (partialJet (g []) ds) atTop Q := by
    rw [hi ds]
    exact ht ds Q hQ
  refine ⟨g [],hs [],nu,hnu,hu,?_⟩
  intro n Q hQ
  exact real_uniform_iteratedFDeriv (fun j ↦ W (nu j)) (g []) (fun j ↦ hW (nu j)) (hs []) n Q
    (fun ds _ ↦ hu ds Q hQ)

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_RealEllipticLocalCompactness
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Yau.Analysis Set Metric Filter MeasureTheory
open scoped Topology ContDiff
noncomputable section
variable {T : Type*} [TopologicalSpace T] [CompactSpace T]

theorem real_elliptic_local_subsequence
    (C : T → Yau.Jets.Coord → Matrix (Fin 4) (Fin 4) ℝ) (V : T → Yau.Jets.Coord → ℝ)
    (hC : ∀ t i j, ContDiff ℝ ∞ (fun x ↦ C t x i j)) (hV : ∀ t, ContDiff ℝ ∞ (V t))
    (hs : ∀ t x i j, C t x i j=C t x j i) (hp : ∀ t x, (C t x).PosDef)
    (hCjoint : ∀ i j ds, Continuous (fun z : T × Yau.Jets.Coord ↦
      partialJet (fun x ↦ C z.1 x i j) ds z.2))
    (hVjoint : ∀ ds, Continuous (fun z : T × Yau.Jets.Coord ↦ partialJet (V z.1) ds z.2))
    (t : ℕ → T) (W : ℕ → Yau.Jets.Coord → ℝ) (hW : ∀ j, ContDiff ℝ ∞ (W j))
    (he : ∀ j x, Yau.coordDiv (realMatrixFlux (C (t j)) (W j)) x+V (t j) x*W j x=0)
    (hL2 : ∀ R : ℕ, ∃ D ≥ 0, ∀ j, (∫ z in closedBall (0 : Yau.Jets.Coord) ((R:ℝ)+2), W j z^2) ≤ D) :
    ∃ v : Yau.Jets.Coord → ℝ, ContDiff ℝ ∞ v ∧ ∃ nu : ℕ → ℕ, StrictMono nu ∧
      (∀ ds (Q : Set Yau.Jets.Coord), IsCompact Q →
        TendstoUniformlyOn (fun j ↦ partialJet (W (nu j)) ds) (partialJet v ds) atTop Q) ∧
      (∀ n (Q : Set Yau.Jets.Coord), IsCompact Q →
        TendstoUniformlyOn (fun j ↦ iteratedFDeriv ℝ n (W (nu j)))
          (iteratedFDeriv ℝ n v) atTop Q) := by
  apply real_smooth_local_subsequence W hW
  intro R n
  obtain ⟨K,hK,hest⟩ := compact_family_pointwise_estimate n C V 0 (R:ℝ) (by positivity)
    hC hV hs (fun t x _ ↦ hp t x)
    (fun i j ds _ ↦ (hCjoint i j ds).comp
      (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)))
    (fun ds _ ↦ (hVjoint ds).comp
      (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)))
  obtain ⟨D,hD,hsize⟩ := hL2 R
  refine ⟨Real.sqrt (K*D),Real.sqrt_nonneg _,?_⟩
  intro j ds hd x hx
  have hh := (hest (t j) (W j) (hW j) (he j) ds hd x hx).trans
    (mul_le_mul_of_nonneg_left (hsize j) hK.le)
  simpa only [Real.sqrt_sq_eq_abs] using Real.sqrt_le_sqrt hh

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Charts_SphereChartEllipticCompactness
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Manifold Yau.Analysis Yau.Geometry Set Metric Filter MeasureTheory
open scoped Topology ContDiff
noncomputable section
variable {T : Type*} [TopologicalSpace T] [CompactSpace T]

theorem sphere_normalized_chart_subsequence (A : T → IntrinsicTensor) (rho : T → Base → ℝ)
    (hA : ∀ t, IntrinsicTensorSmooth (A t))
    (hs : ∀ t p v w, A t p v w = A t p w v) (hp : ∀ t p v, v ≠ 0 → 0 < A t p v v)
    (hr : ∀ t, ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ (rho t)) (hrp : ∀ t p, 0 < rho t p)
    (hrjoint : Continuous (fun z : T × Base ↦ rho z.1 z.2)) (lam : ℝ) (p : Base)
    (hCjoint : ∀ i j ds, Continuous (fun z : T × Yau.Jets.Coord ↦
      partialJet (fun x ↦ intrinsicDivergencePrincipal (A z.1) p x i j) ds z.2))
    (hVjoint : ∀ ds, Continuous (fun z : T × Yau.Jets.Coord ↦
      partialJet (intrinsicDivergencePotential (rho z.1) lam p) ds z.2))
    (t : ℕ → T) (w : ℕ → Base → ℝ) (hw : ∀ j, ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ (w j))
    (he : ∀ j q z, -intrinsicWeightedChartOperator (A (t j)) (rho (t j)) (w j) q z =
      lam*w j ((extChartAt (𝓡 4) q).symm z))
    (hn : ∀ j, sphereWeightedPairing (rho (t j)) (w j) (w j)=1) :
    ∃ v : Yau.Jets.Coord → ℝ, ContDiff ℝ ∞ v ∧ ∃ nu : ℕ → ℕ, StrictMono nu ∧
      (∀ ds (Q : Set Yau.Jets.Coord), IsCompact Q →
        TendstoUniformlyOn (fun j ↦ partialJet (w (nu j) ∘ sphereChartCoordMap p) ds)
          (partialJet v ds) atTop Q) ∧
      (∀ n (Q : Set Yau.Jets.Coord), IsCompact Q →
        TendstoUniformlyOn (fun j ↦ iteratedFDeriv ℝ n (w (nu j) ∘ sphereChartCoordMap p))
          (iteratedFDeriv ℝ n v) atTop Q) := by
  apply real_elliptic_local_subsequence
    (fun t ↦ intrinsicDivergencePrincipal (A t) p)
    (fun t ↦ intrinsicDivergencePotential (rho t) lam p)
    (fun t ↦ intrinsicDivergencePrincipal_smooth (A t) (hA t) (hs t) (hp t) p)
    (fun t ↦ intrinsicDivergencePotential_smooth (rho t) (hr t) lam p)
    (fun t ↦ intrinsicDivergencePrincipal_symmetric (A t) (hs t) p)
    (fun t ↦ intrinsicDivergencePrincipal_posDef (A t) (hs t) (hp t) p)
    hCjoint hVjoint t (fun j ↦ w j ∘ sphereChartCoordMap p)
    (fun j ↦ spherePullback_smooth (w j) (hw j) p)
    (fun j ↦ intrinsic_unweighted_divergence_equation (A (t j)) (rho (t j)) (hrp (t j)) (w j) lam (he j) p)
  intro R
  obtain ⟨K,hK,hbound⟩ := sphere_normalized_chart_l2_bound rho hrjoint hrp p
    (closedBall (0 : Yau.Jets.Coord) ((R:ℝ)+2)) (isCompact_closedBall _ _)
  exact ⟨K,hK.le,fun j ↦ hbound (t j) (w j) (hw j).continuous (hn j)⟩

end
end Yau.Target

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
-- module Solutions.OAIQ237_NY.NodalSets_Charts_SphereFiniteAtlasSubsequence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Manifold Yau.Analysis Yau.Geometry Set Metric Filter
open scoped Topology ContDiff
noncomputable section
variable {T : Type*} [TopologicalSpace T] [CompactSpace T]

theorem sphere_finite_atlas_subsequence (A : T → IntrinsicTensor) (rho : T → Base → ℝ)
    (hA : ∀ t, IntrinsicTensorSmooth (A t))
    (hs : ∀ t p v w, A t p v w = A t p w v) (hp : ∀ t p v, v ≠ 0 → 0 < A t p v v)
    (hr : ∀ t, ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ (rho t)) (hrp : ∀ t p, 0 < rho t p)
    (hrjoint : Continuous (fun z : T × Base ↦ rho z.1 z.2)) (lam : ℝ)
    (hCjoint : ∀ p i j ds, Continuous (fun z : T × Yau.Jets.Coord ↦
      partialJet (fun x ↦ intrinsicDivergencePrincipal (A z.1) p x i j) ds z.2))
    (hVjoint : ∀ p ds, Continuous (fun z : T × Yau.Jets.Coord ↦
      partialJet (intrinsicDivergencePotential (rho z.1) lam p) ds z.2))
    (t : ℕ → T) (w : ℕ → Base → ℝ) (hw : ∀ j, ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ (w j))
    (he : ∀ j q z, -intrinsicWeightedChartOperator (A (t j)) (rho (t j)) (w j) q z =
      lam*w j ((extChartAt (𝓡 4) q).symm z))
    (hn : ∀ j, sphereWeightedPairing (rho (t j)) (w j) (w j)=1) (P : Finset Base) :
    ∃ nu : ℕ → ℕ, StrictMono nu ∧ ∀ p ∈ P,
      ∃ v : Yau.Jets.Coord → ℝ, ContDiff ℝ ∞ v ∧
        (∀ ds (Q : Set Yau.Jets.Coord), IsCompact Q →
          TendstoUniformlyOn (fun j ↦ partialJet (w (nu j) ∘ sphereChartCoordMap p) ds)
            (partialJet v ds) atTop Q) ∧
        (∀ n (Q : Set Yau.Jets.Coord), IsCompact Q →
          TendstoUniformlyOn (fun j ↦ iteratedFDeriv ℝ n (w (nu j) ∘ sphereChartCoordMap p))
            (iteratedFDeriv ℝ n v) atTop Q) := by
  apply finite_subsequence_selection P
  · intro p nu hnu
    obtain ⟨v,hv,mu,hmu,hpartial,hderiv⟩ := sphere_normalized_chart_subsequence
      A rho hA hs hp hr hrp hrjoint lam p (hCjoint p) (hVjoint p)
      (t ∘ nu) (w ∘ nu) (fun j ↦ hw (nu j)) (fun j ↦ he (nu j)) (fun j ↦ hn (nu j))
    exact ⟨mu,hmu,v,hv,hpartial,hderiv⟩
  · intro p nu mu hR hmu
    obtain ⟨v,hv,hpartial,hderiv⟩ := hR
    exact ⟨v,hv,fun ds Q hQ ↦ (hpartial ds Q hQ).seq_tendstoUniformlyOn mu hmu.tendsto_atTop,
      fun n Q hQ ↦ (hderiv n Q hQ).seq_tendstoUniformlyOn mu hmu.tendsto_atTop⟩

end
end Yau.Target

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
-- module Solutions.OAIQ237_NY.NodalSets_Charts_SphereChartLimitGluing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Manifold Yau.Analysis Yau.Geometry Set Metric Filter
open scoped Topology ContDiff
noncomputable section

theorem sphere_chart_limit_gluing (P : Finset Base)
    (hcover : ∀ x : Base, ∃ p ∈ P, ∃ z ∈ ball (0 : Yau.Jets.Coord) 1,
      sphereChartCoordMap p z = x)
    (w : ℕ → Base → ℝ)
    (hlim : ∀ p ∈ P, ∃ f : Yau.Jets.Coord → ℝ, ContDiff ℝ ∞ f ∧
      ∀ Q : Set Yau.Jets.Coord, IsCompact Q →
        TendstoUniformlyOn (fun j ↦ w j ∘ sphereChartCoordMap p) f atTop Q) :
    ∃ v : Base → ℝ, ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ v ∧
      TendstoUniformly w v atTop ∧
      ∀ p ∈ P, ∀ f : Yau.Jets.Coord → ℝ,
        (∀ x, Tendsto (fun j ↦ w j (sphereChartCoordMap p x)) atTop (𝓝 (f x))) →
        v ∘ sphereChartCoordMap p = f := by
  classical
  have hex (p : {p // p ∈ P}) := hlim p.val p.property
  choose f hf hconv using hex
  have hcov (x : Base) : ∃ p : {p // p ∈ P}, ∃ z ∈ ball (0 : Yau.Jets.Coord) 1,
      sphereChartCoordMap p.val z = x := by
    obtain ⟨p,hp,z,hz,he⟩ := hcover x
    exact ⟨⟨p,hp⟩,z,hz,he⟩
  choose c z hz he using hcov
  let v : Base → ℝ := fun x ↦ f (c x) (z x)
  have hvpoint (x : Base) : Tendsto (fun j ↦ w j x) atTop (𝓝 (v x)) := by
    have h := (hconv (c x) {z x} isCompact_singleton).tendsto_at (mem_singleton (z x))
    simpa only [Function.comp_apply,he,v] using h
  have hvchart (p : {p // p ∈ P}) (y : Yau.Jets.Coord) :
      v (sphereChartCoordMap p.val y) = f p y := by
    exact tendsto_nhds_unique (hvpoint _) ((hconv p {y} isCompact_singleton).tendsto_at
      (mem_singleton y))
  have hvsmooth : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ v := by
    intro x
    have hsource : x ∈ (extChartAt (𝓡 4) (c x).val).source := by
      have h := sphereChartCoordMap_source (c x).val (z x)
      rwa [he x] at h
    have hchart := contMDiffAt_extChartAt' (I := 𝓡 4) (n := ∞) (x := (c x).val) (x' := x)
      (by simpa only [extChartAt_source] using hsource)
    have hh := (((hf (c x)).comp seedCoordEquiv.symm.contDiff).contMDiff.contMDiffAt).comp x hchart
    apply hh.congr_of_eventuallyEq
    filter_upwards [(isOpen_extChartAt_source (c x).val).mem_nhds hsource] with y hy
    have h := hvchart (c x) (seedCoordEquiv.symm ((extChartAt (𝓡 4) (c x).val) y))
    simpa only [sphereChartCoordMap,seedCoordEquiv.apply_symm_apply,
      (extChartAt (𝓡 4) (c x).val).left_inv hy,Function.comp_apply] using h
  refine ⟨v,hvsmooth,?_,?_⟩
  · rw [Metric.tendstoUniformly_iff]
    intro eps heps
    have hh (p : {p // p ∈ P}) := Metric.tendstoUniformlyOn_iff.mp
      (hconv p (closedBall (0 : Yau.Jets.Coord) 1) (isCompact_closedBall _ _)) eps heps
    filter_upwards [Filter.eventually_all.mpr hh] with j hj x
    have h := hj (c x) (z x) (ball_subset_closedBall (hz x))
    simpa only [Function.comp_apply,he,v] using h
  · intro p hp g hg
    funext y
    exact tendsto_nhds_unique (hvpoint _) (hg y)

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_UniformSubsequenceLimit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Analysis
open Filter Set
open scoped Topology UniformConvergence

theorem uniformOn_of_subsequence_limits {X E : Type*} [UniformSpace E]
    (F : ℕ → X → E) (f : X → E) (Q : Set X)
    (h : ∀ ns : ℕ → ℕ, Tendsto ns atTop atTop → ∃ ms : ℕ → ℕ,
      TendstoUniformlyOn (fun j ↦ F (ns (ms j))) f atTop Q) :
    TendstoUniformlyOn F f atTop Q := by
  rw [tendstoUniformlyOn_iff_tendstoUniformly_comp_coe]
  apply UniformFun.tendsto_iff_tendstoUniformly.mp
    (show Tendsto (fun j ↦ UniformFun.ofFun (fun x : Q ↦ F j x)) atTop
      (𝓝 (UniformFun.ofFun (fun x : Q ↦ f x))) from ?_)
  apply tendsto_of_subseq_tendsto
  intro ns hns
  obtain ⟨ms,hms⟩ := h ns hns
  exact ⟨ms,UniformFun.tendsto_iff_tendstoUniformly.mpr
    (tendstoUniformlyOn_iff_tendstoUniformly_comp_coe.mp hms)⟩

end Yau.Analysis

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Charts_SphereGlobalSmoothCompactness
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Manifold Yau.Analysis Yau.Geometry Set Metric Filter
open scoped Topology ContDiff
noncomputable section
variable {T : Type*} [TopologicalSpace T] [CompactSpace T]

theorem sphere_global_smooth_subsequence (A : T → IntrinsicTensor) (rho : T → Base → ℝ)
    (hA : ∀ t, IntrinsicTensorSmooth (A t))
    (hs : ∀ t p v w, A t p v w = A t p w v) (hp : ∀ t p v, v ≠ 0 → 0 < A t p v v)
    (hr : ∀ t, ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ (rho t)) (hrp : ∀ t p, 0 < rho t p)
    (hrjoint : Continuous (fun z : T × Base ↦ rho z.1 z.2)) (lam : ℝ)
    (hCjoint : ∀ p i j ds, Continuous (fun z : T × Yau.Jets.Coord ↦
      partialJet (fun x ↦ intrinsicDivergencePrincipal (A z.1) p x i j) ds z.2))
    (hVjoint : ∀ p ds, Continuous (fun z : T × Yau.Jets.Coord ↦
      partialJet (intrinsicDivergencePotential (rho z.1) lam p) ds z.2))
    (t : ℕ → T) (w : ℕ → Base → ℝ) (hw : ∀ j, ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ (w j))
    (he : ∀ j q z, -intrinsicWeightedChartOperator (A (t j)) (rho (t j)) (w j) q z =
      lam*w j ((extChartAt (𝓡 4) q).symm z))
    (hn : ∀ j, sphereWeightedPairing (rho (t j)) (w j) (w j)=1)  :
    ∃ v : Base → ℝ, ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ v ∧ ∃ nu : ℕ → ℕ, StrictMono nu ∧
      TendstoUniformly (fun j ↦ w (nu j)) v atTop ∧
      (∀ p ds (Q : Set Yau.Jets.Coord), IsCompact Q →
        TendstoUniformlyOn (fun j ↦ partialJet (w (nu j) ∘ sphereChartCoordMap p) ds)
          (partialJet (v ∘ sphereChartCoordMap p) ds) atTop Q) ∧
      (∀ p n (Q : Set Yau.Jets.Coord), IsCompact Q →
        TendstoUniformlyOn (fun j ↦ iteratedFDeriv ℝ n (w (nu j) ∘ sphereChartCoordMap p))
          (iteratedFDeriv ℝ n (v ∘ sphereChartCoordMap p)) atTop Q) := by
  obtain ⟨P,hP⟩ := finite_sphere_coordinate_cover
  obtain ⟨nu,hnu,hcharts⟩ := sphere_finite_atlas_subsequence A rho hA hs hp hr hrp
    hrjoint lam hCjoint hVjoint t w hw he hn P
  have hvalues (p : Base) (hp : p ∈ P) : ∃ f : Yau.Jets.Coord → ℝ,
      ContDiff ℝ ∞ f ∧ ∀ Q : Set Yau.Jets.Coord, IsCompact Q →
        TendstoUniformlyOn (fun j ↦ w (nu j) ∘ sphereChartCoordMap p) f atTop Q := by
    obtain ⟨f,hf,hpartial,_⟩ := hcharts p hp
    exact ⟨f,hf,hpartial []⟩
  obtain ⟨v,hv,hval,_⟩ := sphere_chart_limit_gluing P hP (fun j ↦ w (nu j)) hvalues
  have hsub (p : Base) (ns : ℕ → ℕ) (hns : Tendsto ns atTop atTop) :
      ∃ mu : ℕ → ℕ,
        (∀ ds (Q : Set Yau.Jets.Coord), IsCompact Q →
          TendstoUniformlyOn (fun j ↦ partialJet (w (nu (ns (mu j))) ∘ sphereChartCoordMap p) ds)
            (partialJet (v ∘ sphereChartCoordMap p) ds) atTop Q) ∧
        (∀ n (Q : Set Yau.Jets.Coord), IsCompact Q →
          TendstoUniformlyOn (fun j ↦ iteratedFDeriv ℝ n (w (nu (ns (mu j))) ∘ sphereChartCoordMap p))
            (iteratedFDeriv ℝ n (v ∘ sphereChartCoordMap p)) atTop Q) := by
    obtain ⟨f,hf,mu,hmu,hpartial,hderiv⟩ := sphere_normalized_chart_subsequence A rho hA hs hp hr hrp
      hrjoint lam p (hCjoint p) (hVjoint p) (fun j ↦ t (nu (ns j)))
      (fun j ↦ w (nu (ns j))) (fun j ↦ hw _) (fun j ↦ he _) (fun j ↦ hn _)
    have heq : f = v ∘ sphereChartCoordMap p := by
      funext x
      exact tendsto_nhds_unique ((hpartial [] {x} isCompact_singleton).tendsto_at (mem_singleton x))
        ((hval.tendsto_at (sphereChartCoordMap p x)).comp (hns.comp hmu.tendsto_atTop))
    rw [heq] at hpartial hderiv
    exact ⟨mu,hpartial,hderiv⟩
  refine ⟨v,hv,nu,hnu,hval,?_,?_⟩
  · intro p ds Q hQ
    apply uniformOn_of_subsequence_limits
    intro ns hns
    obtain ⟨mu,hm,_⟩ := hsub p ns hns
    exact ⟨mu,hm ds Q hQ⟩
  · intro p n Q hQ
    apply uniformOn_of_subsequence_limits
    intro ns hns
    obtain ⟨mu,_,hm⟩ := hsub p ns hns
    exact ⟨mu,hm n Q hQ⟩

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_RealDivergenceLimit
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Yau.Analysis Filter
open scoped Topology ContDiff
noncomputable section

lemma real_unweighted_divergence_expansion
    (C : Yau.Jets.Coord → Matrix (Fin 4) (Fin 4) ℝ) (W : Yau.Jets.Coord → ℝ)
    (hC : ∀ i j, ContDiff ℝ ∞ (fun x ↦ C x i j)) (hW : ContDiff ℝ ∞ W)
    (x : Yau.Jets.Coord) :
    Yau.coordDiv (realMatrixFlux C W) x = ∑ i, ∑ j,
      (partialJet (fun y ↦ C y i j) [i] x*partialJet W [j] x+
        C x i j*partialJet W [i,j] x) := by
  unfold Yau.coordDiv realMatrixFlux
  simp_rw [Yau.real_coordPartial_sum _ (fun j ↦ (hC _ j).mul (Yau.real_coordPartial_smooth W hW j)),
    Yau.real_coordPartial_mul _ _ (hC _ _) (Yau.real_coordPartial_smooth W hW _)]
  rfl

theorem real_divergence_limit_equation
    (C : ℕ → Yau.Jets.Coord → Matrix (Fin 4) (Fin 4) ℝ)
    (C0 : Yau.Jets.Coord → Matrix (Fin 4) (Fin 4) ℝ)
    (V : ℕ → Yau.Jets.Coord → ℝ) (V0 : Yau.Jets.Coord → ℝ)
    (W : ℕ → Yau.Jets.Coord → ℝ) (v : Yau.Jets.Coord → ℝ)
    (hC : ∀ n i j, ContDiff ℝ ∞ (fun x ↦ C n x i j))
    (hC0 : ∀ i j, ContDiff ℝ ∞ (fun x ↦ C0 x i j))
    (hW : ∀ n, ContDiff ℝ ∞ (W n)) (hv : ContDiff ℝ ∞ v)
    (htC : ∀ i j ds x, Tendsto (fun n ↦ partialJet (fun y ↦ C n y i j) ds x) atTop
      (𝓝 (partialJet (fun y ↦ C0 y i j) ds x)))
    (htV : ∀ x, Tendsto (fun n ↦ V n x) atTop (𝓝 (V0 x)))
    (htW : ∀ ds x, Tendsto (fun n ↦ partialJet (W n) ds x) atTop (𝓝 (partialJet v ds x)))
    (he : ∀ n x, Yau.coordDiv (realMatrixFlux (C n) (W n)) x+V n x*W n x=0) :
    ∀ x, Yau.coordDiv (realMatrixFlux C0 v) x+V0 x*v x=0 := by
  intro x
  rw [real_unweighted_divergence_expansion C0 v hC0 hv]
  have hh : Tendsto (fun n ↦ (∑ i, ∑ j,
      (partialJet (fun y ↦ C n y i j) [i] x*partialJet (W n) [j] x+
        C n x i j*partialJet (W n) [i,j] x))+V n x*W n x) atTop
      (𝓝 ((∑ i, ∑ j, (partialJet (fun y ↦ C0 y i j) [i] x*partialJet v [j] x+
        C0 x i j*partialJet v [i,j] x))+V0 x*v x)) :=
    (tendsto_finsetSum _ (fun i _ ↦ tendsto_finsetSum _ (fun j _ ↦
      ((htC i j [i] x).mul (htW [j] x)).add ((htC i j [] x).mul (htW [i,j] x))))).add
      ((htV x).mul (htW [] x))
  apply tendsto_nhds_unique hh
  have hz (n : ℕ) := he n x
  simp only [real_unweighted_divergence_expansion (C _) (W _) (hC _) (hW _)] at hz
  simpa only [hz] using (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ (0:ℝ)) atTop (𝓝 0))

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Charts_SphereLimitEquation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Manifold Yau.Analysis Yau.Geometry Set Filter
open scoped Topology ContDiff
noncomputable section

lemma intrinsic_operator_unweighted_divergence (A : IntrinsicTensor) (rho w : Base → ℝ)
    (p : Base) (x : Yau.Jets.Coord) :
    intrinsicWeightedChartOperator A rho w p (seedCoordEquiv x) =
      (rho (sphereChartCoordMap p x))⁻¹ * (roundCoordDensity x)⁻¹ *
        Yau.coordDiv (realMatrixFlux (intrinsicDivergencePrincipal A p) (w ∘ sphereChartCoordMap p)) x := by
  rw [intrinsicRealOperator_pullback]
  have hf : realMatrixFlux (intrinsicDivergencePrincipal A p) (w ∘ sphereChartCoordMap p) =
      fun y i ↦ roundCoordDensity y * ∑ j, intrinsicRealPrincipal A p y i j*
        Yau.coordPartial (w ∘ sphereChartCoordMap p) y j := by
    funext y i
    simp [realMatrixFlux,intrinsicDivergencePrincipal,Finset.mul_sum,mul_assoc]
  rw [hf]
  simp only [Yau.weightedDiv,mul_assoc]

theorem intrinsic_equation_of_unweighted_divergence (A : IntrinsicTensor) (rho w : Base → ℝ)
    (hrp : ∀ p, 0 < rho p) (lam : ℝ)
    (he : ∀ p x, Yau.coordDiv
      (realMatrixFlux (intrinsicDivergencePrincipal A p) (w ∘ sphereChartCoordMap p)) x+
      intrinsicDivergencePotential rho lam p x*(w ∘ sphereChartCoordMap p) x=0) :
    ∀ p z, -intrinsicWeightedChartOperator A rho w p z =
      lam*w ((extChartAt (𝓡 4) p).symm z) := by
  intro p z
  obtain ⟨x,rfl⟩ := seedCoordEquiv.surjective z
  rw [intrinsic_operator_unweighted_divergence]
  have hh := he p x
  have hd : Yau.coordDiv
      (realMatrixFlux (intrinsicDivergencePrincipal A p) (w ∘ sphereChartCoordMap p)) x =
      -(roundCoordDensity x*(lam*rho (sphereChartCoordMap p x))*w (sphereChartCoordMap p x)) := by
    simpa only [intrinsicDivergencePotential,intrinsicRealPotential,Function.comp_apply] using
      (eq_neg_of_add_eq_zero_left hh)
  rw [hd]
  change -((rho (sphereChartCoordMap p x))⁻¹ * (roundCoordDensity x)⁻¹ *
    -(roundCoordDensity x*(lam*rho (sphereChartCoordMap p x))*w (sphereChartCoordMap p x))) =
      lam*w (sphereChartCoordMap p x)
  field_simp [(hrp (sphereChartCoordMap p x)).ne',(roundCoordDensity_pos x).ne']

theorem sphere_limit_equation {T : Type*} [TopologicalSpace T]
    (A : T → IntrinsicTensor) (rho : T → Base → ℝ)
    (hA : ∀ t, IntrinsicTensorSmooth (A t))
    (hs : ∀ t p v w, A t p v w = A t p w v) (hp : ∀ t p v, v ≠ 0 → 0 < A t p v v)
    (hrp : ∀ t p, 0 < rho t p) (lam : ℝ)
    (hCjoint : ∀ p i j ds, Continuous (fun z : T × Yau.Jets.Coord ↦
      partialJet (fun x ↦ intrinsicDivergencePrincipal (A z.1) p x i j) ds z.2))
    (hVjoint : ∀ p ds, Continuous (fun z : T × Yau.Jets.Coord ↦
      partialJet (intrinsicDivergencePotential (rho z.1) lam p) ds z.2))
    (t : ℕ → T) (t0 : T) (ht : Tendsto t atTop (𝓝 t0))
    (w : ℕ → Base → ℝ) (v : Base → ℝ)
    (hw : ∀ j, ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ (w j)) (hv : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ v)
    (he : ∀ j p z, -intrinsicWeightedChartOperator (A (t j)) (rho (t j)) (w j) p z =
      lam*w j ((extChartAt (𝓡 4) p).symm z))
    (hconv : ∀ p ds x, Tendsto (fun j ↦ partialJet (w j ∘ sphereChartCoordMap p) ds x) atTop
      (𝓝 (partialJet (v ∘ sphereChartCoordMap p) ds x))) :
    ∀ p z, -intrinsicWeightedChartOperator (A t0) (rho t0) v p z =
      lam*v ((extChartAt (𝓡 4) p).symm z) := by
  apply intrinsic_equation_of_unweighted_divergence (A t0) (rho t0) v (hrp t0) lam
  intro p
  apply real_divergence_limit_equation
    (fun j ↦ intrinsicDivergencePrincipal (A (t j)) p) (intrinsicDivergencePrincipal (A t0) p)
    (fun j ↦ intrinsicDivergencePotential (rho (t j)) lam p) (intrinsicDivergencePotential (rho t0) lam p)
    (fun j ↦ w j ∘ sphereChartCoordMap p) (v ∘ sphereChartCoordMap p)
    (fun j ↦ intrinsicDivergencePrincipal_smooth (A (t j)) (hA (t j)) (hs (t j)) (hp (t j)) p)
    (intrinsicDivergencePrincipal_smooth (A t0) (hA t0) (hs t0) (hp t0) p)
    (fun j ↦ spherePullback_smooth (w j) (hw j) p) (spherePullback_smooth v hv p)
  · intro i j ds x
    have htx : Tendsto (fun n ↦ (t n,x)) atTop (𝓝 (t0,x)) := ht.prodMk_nhds tendsto_const_nhds
    have hh := ((hCjoint p i j ds).tendsto (t0,x)).comp htx
    simpa only [Function.comp_def] using hh
  · intro x
    have htx : Tendsto (fun n ↦ (t n,x)) atTop (𝓝 (t0,x)) := ht.prodMk_nhds tendsto_const_nhds
    have hh := ((hVjoint p []).tendsto (t0,x)).comp htx
    simpa only [Function.comp_def,partialJet] using hh
  · exact hconv p
  · exact fun j ↦ intrinsic_unweighted_divergence_equation (A (t j)) (rho (t j)) (hrp (t j))
      (w j) lam (he j) p

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
local instance sphereWeightedPairingLimitBorel : BorelSpace Base := ⟨rfl⟩

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

theorem sphereWeightedPairing_family_limit {T : Type*} [TopologicalSpace T] [CompactSpace T]
    (rho : T → Base → ℝ) (hr : Continuous (fun z : T × Base ↦ rho z.1 z.2))
    (t : ℕ → T) (t0 : T) (ht : Tendsto t atTop (𝓝 t0))
    (w1 w2 : ℕ → Base → ℝ) (v1 v2 : Base → ℝ)
    (hw1 : ∀ j, Continuous (w1 j)) (hw2 : ∀ j, Continuous (w2 j))
    (hv1 : Continuous v1) (hv2 : Continuous v2)
    (hc1 : TendstoUniformly w1 v1 atTop) (hc2 : TendstoUniformly w2 v2 atTop) :
    Tendsto (fun j ↦ sphereWeightedPairing (rho (t j)) (w1 j) (w2 j)) atTop
      (𝓝 (sphereWeightedPairing (rho t0) v1 v2)) := by
  let := sphereReferenceMeasure_finite
  obtain ⟨R,hR⟩ := (isCompact_univ : IsCompact (univ : Set (T × Base))).exists_bound_of_continuousOn
    hr.continuousOn
  obtain ⟨B1,hB1,hb1⟩ := sphere_uniform_eventual_bound w1 v1 hv1 hc1
  obtain ⟨B2,hB2,hb2⟩ := sphere_uniform_eventual_bound w2 v2 hv2 hc2
  apply tendsto_integral_filter_of_norm_le_const
  · exact Eventually.of_forall (fun j ↦
      (((hr.comp (continuous_const.prodMk continuous_id)).mul (hw1 j)).mul (hw2 j)).aestronglyMeasurable)
  · refine ⟨(max 0 R)*B1*B2,?_⟩
    filter_upwards [hb1,hb2] with j hj1 hj2
    exact Eventually.of_forall (fun x ↦ by
      rw [norm_mul,norm_mul]
      have hb : ‖rho (t j) x‖ ≤ max 0 R := (hR (t j,x) (mem_univ _)).trans (le_max_right _ _)
      exact mul_le_mul (mul_le_mul hb (hj1 x) (norm_nonneg _) (le_max_left _ _))
        (hj2 x) (norm_nonneg _) (mul_nonneg (le_max_left _ _) hB1.le))
  · exact Eventually.of_forall (fun x ↦
      (((hr.tendsto (t0,x)).comp (ht.prodMk_nhds tendsto_const_nhds)).mul (hc1.tendsto_at x)).mul
        (hc2.tendsto_at x))

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Charts_SphereNormalizedGlobalLimit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Manifold Yau.Analysis Yau.Geometry Set Metric Filter
open scoped Topology ContDiff
noncomputable section
variable {T : Type*} [TopologicalSpace T] [CompactSpace T]

theorem sphere_normalized_global_limit_oai (A : T → IntrinsicTensor) (rho : T → Base → ℝ)
    (hA : ∀ t, IntrinsicTensorSmooth (A t))
    (hs : ∀ t p v w, A t p v w = A t p w v) (hp : ∀ t p v, v ≠ 0 → 0 < A t p v v)
    (hr : ∀ t, ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ (rho t)) (hrp : ∀ t p, 0 < rho t p)
    (hrjoint : Continuous (fun z : T × Base ↦ rho z.1 z.2)) (lam : ℝ)
    (hCjoint : ∀ p i j ds, Continuous (fun z : T × Yau.Jets.Coord ↦
      partialJet (fun x ↦ intrinsicDivergencePrincipal (A z.1) p x i j) ds z.2))
    (hVjoint : ∀ p ds, Continuous (fun z : T × Yau.Jets.Coord ↦
      partialJet (intrinsicDivergencePotential (rho z.1) lam p) ds z.2))
    (t : ℕ → T) (t0 : T) (ht : Tendsto t atTop (𝓝 t0)) (w : ℕ → Base → ℝ) (hw : ∀ j, ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ (w j))
    (he : ∀ j q z, -intrinsicWeightedChartOperator (A (t j)) (rho (t j)) (w j) q z =
      lam*w j ((extChartAt (𝓡 4) q).symm z))
    (hn : ∀ j, sphereWeightedPairing (rho (t j)) (w j) (w j)=1)
    (u : Base → ℝ) (hu : Continuous u)
    (ho : ∀ j, sphereWeightedPairing (rho (t j)) (w j) u=0) :
    ∃ v : Base → ℝ, ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ v ∧ v ≠ 0 ∧
      (∀ p z, -intrinsicWeightedChartOperator (A t0) (rho t0) v p z =
        lam*v ((extChartAt (𝓡 4) p).symm z)) ∧
      sphereWeightedPairing (rho t0) v v=1 ∧ sphereWeightedPairing (rho t0) v u=0 ∧
      ∃ nu : ℕ → ℕ, StrictMono nu ∧ TendstoUniformly (fun j ↦ w (nu j)) v atTop ∧
        (∀ p ds (Q : Set Yau.Jets.Coord), IsCompact Q →
          TendstoUniformlyOn (fun j ↦ partialJet (w (nu j) ∘ sphereChartCoordMap p) ds)
            (partialJet (v ∘ sphereChartCoordMap p) ds) atTop Q) ∧
        (∀ p n (Q : Set Yau.Jets.Coord), IsCompact Q →
          TendstoUniformlyOn (fun j ↦ iteratedFDeriv ℝ n (w (nu j) ∘ sphereChartCoordMap p))
            (iteratedFDeriv ℝ n (v ∘ sphereChartCoordMap p)) atTop Q) := by
  obtain ⟨v,hv,nu,hnu,hval,hpartial,hderiv⟩ := sphere_global_smooth_subsequence A rho hA hs hp hr hrp
    hrjoint lam hCjoint hVjoint t w hw he hn
  have ht' := ht.comp hnu.tendsto_atTop
  have hev := sphere_limit_equation A rho hA hs hp hrp lam hCjoint hVjoint (t ∘ nu) t0 ht'
    (fun j ↦ w (nu j)) v (fun j ↦ hw _) hv (fun j ↦ he _)
    (fun p ds x ↦ (hpartial p ds {x} isCompact_singleton).tendsto_at (mem_singleton x))
  have hnorm : sphereWeightedPairing (rho t0) v v=1 := by
    apply tendsto_nhds_unique (sphereWeightedPairing_family_limit rho hrjoint (t ∘ nu) t0 ht'
      (fun j ↦ w (nu j)) (fun j ↦ w (nu j)) v v
      (fun j ↦ (hw _).continuous) (fun j ↦ (hw _).continuous) hv.continuous hv.continuous hval hval)
    simpa only [Function.comp_apply,hn] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ (1:ℝ)) atTop (𝓝 1))
  have hortho : sphereWeightedPairing (rho t0) v u=0 := by
    apply tendsto_nhds_unique (sphereWeightedPairing_family_limit rho hrjoint (t ∘ nu) t0 ht'
      (fun j ↦ w (nu j)) (fun _ ↦ u) v u (fun j ↦ (hw _).continuous)
      (fun _ ↦ hu) hv.continuous hu hval (by
        rw [Metric.tendstoUniformly_iff]
        exact fun eps heps ↦ Eventually.of_forall (fun _ _ ↦ by simpa using heps)))
    simpa only [Function.comp_apply,ho] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ (0:ℝ)) atTop (𝓝 0))
  have hvne : v ≠ 0 := by
    intro hzero
    simp [hzero,sphereWeightedPairing] at hnorm
  exact ⟨v,hv,hvne,hev,hnorm,hortho,nu,hnu,hval,hpartial,hderiv⟩

end
end Yau.Target

end OAI
end

theorem solution.{u_1} : type_of% @OAI.Yau.Target.sphere_normalized_global_limit_oai.{u_1} := @OAI.Yau.Target.sphere_normalized_global_limit_oai.{u_1}
