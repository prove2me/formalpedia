-- Prove2me | solution 1 for OAI.Yau.Target.sphere_affine_kernel_implies_simplicity
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T00:34:12.271443+00:00
-- url     : https://prove2.me/submissions/b201b1d5-b4ea-4ece-86d5-de356fce4a23

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
import Mathlib.Analysis.Calculus.UniformLimitsDeriv
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.Harmonic.Basic
import Mathlib.Analysis.InnerProductSpace.Laplacian
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
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
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
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Group.Integral
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
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Algebra.IsUniformGroup.Basic
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.Algebra.Ring.Basic
import Mathlib.Topology.Algebra.Support
import Mathlib.Topology.Compactness.LocallyCompact
import Mathlib.Topology.ContinuousMap.Algebra
import Mathlib.Topology.ContinuousMap.Bounded.ArzelaAscoli
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Sequences
import Mathlib.Topology.UniformSpace.CompactConvergence
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Topology.UniformSpace.UniformApproximation
import Mathlib.Topology.UniformSpace.UniformConvergence
import Mathlib.Topology.UniformSpace.UniformConvergenceTopology
import Definitions.Def_YauCounterexample
import Definitions.Def_OAIQ237Ny004
import Theorems.Thm_OAI_Yau_Target_sphere_normalized_global_limit

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

lemma finiteChartDerivativeSize_zero (P : Finset I) {Q : Set E} (hQ : IsCompact Q) (J : ℕ) :
    finiteChartDerivativeSize P Q J (fun _ _ ↦ (0:F)) = 0 := by
  apply le_antisymm
  · exact finiteChartDerivativeSize_le P Q J _ le_rfl (by intros; simp)
  · exact finiteChartDerivativeSize_nonneg P hQ J _ (fun _ _ ↦ contDiff_const)

lemma finiteChartDerivativeSize_smul_le (P : Finset I) {Q : Set E} (hQ : IsCompact Q)
    (J : ℕ) (r : ℝ) (f : I → E → F) (hf : ∀ p ∈ P, ContDiff ℝ ∞ (f p)) :
    finiteChartDerivativeSize P Q J (fun p x ↦ r • f p x) ≤ ‖r‖*finiteChartDerivativeSize P Q J f := by
  apply finiteChartDerivativeSize_le _ _ _ _
    (mul_nonneg (norm_nonneg r) (finiteChartDerivativeSize_nonneg P hQ J f hf))
  intro p hp i hi x hx
  rw [iteratedFDeriv_const_smul_apply'
    ((hf p hp).of_le (by exact_mod_cast (show (i:ℕ∞) ≤ ⊤ from le_top))).contDiffAt,norm_smul]
  exact mul_le_mul_of_nonneg_left (norm_le_finiteChartDerivativeSize P hQ J f hf p hp i hi x hx) (norm_nonneg r)

lemma finiteChartDerivativeSize_smul (P : Finset I) {Q : Set E} (hQ : IsCompact Q)
    (J : ℕ) (r : ℝ) (f : I → E → F) (hf : ∀ p ∈ P, ContDiff ℝ ∞ (f p)) :
    finiteChartDerivativeSize P Q J (fun p x ↦ r • f p x) = ‖r‖*finiteChartDerivativeSize P Q J f := by
  by_cases hr : r=0
  · subst r
    simpa using finiteChartDerivativeSize_zero (F := F) P hQ J
  · apply le_antisymm (finiteChartDerivativeSize_smul_le P hQ J r f hf)
    have h := finiteChartDerivativeSize_smul_le P hQ J r⁻¹ (fun p x ↦ r • f p x)
      (fun p hp ↦ (hf p hp).const_smul r)
    simp only [smul_smul,inv_mul_cancel₀ hr,one_smul] at h
    have hh := mul_le_mul_of_nonneg_left h (norm_nonneg r)
    simpa only [norm_inv,← mul_assoc,mul_inv_cancel₀ (norm_ne_zero_iff.mpr hr),one_mul] using hh

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Charts_SphereChartVolume
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Manifold Matrix Yau.Geometry
noncomputable section

lemma sphereRoundChartMatrix_posDef (p : Base) {y : BaseModel}
    (hy : y ∈ (extChartAt (𝓡 4) p).target) : (sphereRoundChartMatrix p y).PosDef := by
  simpa [sphereRoundChartMatrix,conjTranspose_eq_transpose_of_trivial] using
    (PosDef.one : (1 : Matrix (Fin 5) (Fin 5) ℝ).PosDef).conjTranspose_mul_mul_same
      (sphereChartFrame_injective p hy)

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Spectral_SphereRadialProjection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Manifold
open scoped RealInnerProductSpace
noncomputable section

lemma sphere_radial_norm (x : Base) : ‖(x : AmbientBase)‖ = 1 := by
  simpa only [Metric.mem_sphere,dist_zero_right] using x.property

lemma sphereTangentProjection_orthogonal (x : Base) (v : AmbientBase) :
    ⟪(x : AmbientBase),sphereTangentProjection x v⟫ = 0 := by
  simp [sphereTangentProjection, inner_sub_right, real_inner_smul_right]

lemma sphereTangentProjection_restriction (x : Base) (v : AmbientBase) :
    sphereCovectorRestriction x (sphereTangentProjection x v) = sphereCovectorRestriction x v := by
  simp only [sphereTangentProjection,map_sub,map_smul,sphereCovectorRestriction_radial,
    smul_zero,sub_zero]

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_IntrinsicRoundReference
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Matrix
open scoped RealInnerProductSpace
noncomputable section

lemma sphereTangentProjection_inner (x : Base) (v w : AmbientBase) :
    ⟪sphereTangentProjection x v,sphereTangentProjection x w⟫ +
      ⟪(x:AmbientBase),v⟫ * ⟪(x:AmbientBase),w⟫ = ⟪v,w⟫ := by
  simp only [sphereTangentProjection,inner_sub_left,inner_sub_right,
    real_inner_smul_left,real_inner_smul_right,real_inner_self_eq_norm_sq,
    sphere_radial_norm,one_pow,real_inner_comm v (x:AmbientBase)]
  ring

lemma intrinsicAmbientForm_reference (A : IntrinsicTensor) (x : Base)
    (hA : ∀ v w : AmbientBase, ⟪(x:AmbientBase),v⟫ = 0 → ⟪(x:AmbientBase),w⟫ = 0 →
      A x (sphereCovectorRestriction x v) (sphereCovectorRestriction x w) = ⟪v,w⟫)
    (v w : AmbientBase) : intrinsicAmbientForm A x v w = ⟪v,w⟫ := by
  have h := hA (sphereTangentProjection x v) (sphereTangentProjection x w)
    (sphereTangentProjection_orthogonal x v) (sphereTangentProjection_orthogonal x w)
  rw [sphereTangentProjection_restriction,sphereTangentProjection_restriction] at h
  rw [intrinsicAmbientForm_apply,h,sphereTangentProjection_inner]

lemma intrinsicAmbientMatrix_reference (A : IntrinsicTensor) (x : Base)
    (hA : ∀ v w : AmbientBase, ⟪(x:AmbientBase),v⟫ = 0 → ⟪(x:AmbientBase),w⟫ = 0 →
      A x (sphereCovectorRestriction x v) (sphereCovectorRestriction x w) = ⟪v,w⟫) :
    intrinsicAmbientMatrix A x = 1 := by
  ext i j
  change intrinsicAmbientForm A x (EuclideanSpace.basisFun (Fin 5) ℝ i)
    (EuclideanSpace.basisFun (Fin 5) ℝ j) = _
  rw [intrinsicAmbientForm_reference A x hA]
  exact (EuclideanSpace.basisFun (Fin 5) ℝ).inner_eq_ite i j

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Charts_RoundCotangentTensor
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Manifold Yau.Geometry
open scoped RealInnerProductSpace
noncomputable section
attribute [local instance] clmTopology clmAdd clmModule
attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace normedSpaceTangentSpaceVectorSpace

attribute [local instance] OAI.Yau.Target.roundCotangentTensorLocalInst1
attribute [local instance] OAI.Yau.Target.roundCotangentTensorLocalInst2
attribute [local instance] OAI.Yau.Target.roundCotangentTensorLocalInst3
attribute [local instance] OAI.Yau.Target.roundCotangentTensorLocalInst4
lemma sphereCotangentRepresentative_orthogonal (x : Base) (ell : SphereCotangent x) :
    ⟪(x:AmbientBase),sphereCotangentRepresentative x ell⟫ = 0 := by
  have h := sphere_derivative_radial_orthogonal x ((sphereRoundMusical x).symm ell)
  simpa [sphereCotangentRepresentative,PiLp.inner_apply,dotProduct,mul_comm] using h

lemma sphereCotangentRepresentative_unique (x : Base) (ell : SphereCotangent x)
    (v : AmbientBase) (hr : sphereCovectorRestriction x v = ell)
    (ho : ⟪(x:AmbientBase),v⟫ = 0) : sphereCotangentRepresentative x ell = v := by
  apply sub_eq_zero.mp
  apply sphereCovectorRestriction_separates x
  · rw [map_sub,sphereCotangentRepresentative_restriction,hr,sub_self]
  · rw [inner_sub_right,sphereCotangentRepresentative_orthogonal,ho,sub_self]

lemma sphereCotangentRepresentative_project (x : Base) (v : AmbientBase) :
    sphereCotangentRepresentative x (sphereCovectorRestriction x v) = sphereTangentProjection x v :=
  sphereCotangentRepresentative_unique x _ _ (sphereTangentProjection_restriction x v)
    (sphereTangentProjection_orthogonal x v)

lemma roundCotangentTensor_restriction (x : Base) (v w : AmbientBase) :
    roundCotangentTensor x (sphereCovectorRestriction x v) (sphereCovectorRestriction x w) =
      ⟪sphereTangentProjection x v,sphereTangentProjection x w⟫ := by
  rw [roundCotangentTensor_apply,sphereCotangentRepresentative_project,sphereCotangentRepresentative_project]

lemma roundCotangentTensor_tangent (x : Base) (v w : AmbientBase)
    (hv : ⟪(x:AmbientBase),v⟫ = 0) (hw : ⟪(x:AmbientBase),w⟫ = 0) :
    roundCotangentTensor x (sphereCovectorRestriction x v) (sphereCovectorRestriction x w) = ⟪v,w⟫ := by
  simp [roundCotangentTensor_restriction,sphereTangentProjection,hv,hw]

lemma roundCotangentTensor_ambient (x : Base) : intrinsicAmbientMatrix roundCotangentTensor x = 1 :=
  intrinsicAmbientMatrix_reference _ x (roundCotangentTensor_tangent x)

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
-- module Solutions.OAIQ237_NY.NodalSets_Charts_SphereChartConformal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Manifold Matrix
open scoped ContDiff RealInnerProductSpace
noncomputable section

lemma sphereRoundChartMatrix_inverse_conformal (p : Base) (y : BaseModel) :
    (sphereRoundChartMatrix p y)⁻¹ = ((4/(‖y‖^2+4))^2)⁻¹ • (1 : Matrix (Fin 4) (Fin 4) ℝ) := by
  let : Invertible ((4/(‖y‖^2+4))^2) := invertibleOfNonzero (by positivity)
  rw [sphereRoundChartMatrix_conformal,Matrix.inv_smul (A := (1 : Matrix (Fin 4) (Fin 4) ℝ)) ((4/(‖y‖^2+4))^2) (by simp)]
  simp

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_IntrinsicRoundPerturbation
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Bundle Manifold Matrix Yau.Geometry
open scoped ContDiff Topology RealInnerProductSpace
noncomputable section
attribute [local instance] clmTopology clmAdd clmModule
attribute [local instance] ContinuousLinearMap.toNormedAddCommGroup ContinuousLinearMap.toNormedSpace
attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace normedSpaceTangentSpaceVectorSpace

attribute [local instance] OAI.Yau.Target.intrinsicRoundPerturbationLocalInst1
attribute [local instance] OAI.Yau.Target.intrinsicRoundPerturbationLocalInst2
attribute [local instance] OAI.Yau.Target.intrinsicRoundPerturbationLocalInst3
attribute [local instance] OAI.Yau.Target.intrinsicRoundPerturbationLocalInst4
attribute [local instance] OAI.Yau.Target.intrinsicRoundPerturbationLocalInst5
attribute [local instance] OAI.Yau.Target.intrinsicRoundPerturbationLocalInst6
attribute [local instance] OAI.Yau.Target.intrinsicRoundPerturbationLocalInst7
attribute [local instance] OAI.Yau.Target.intrinsicRoundPerturbationLocalInst8
attribute [local instance] OAI.Yau.Target.intrinsicRoundPerturbationLocalInst9
attribute [local instance] OAI.Yau.Target.intrinsicRoundPerturbationLocalInst10
attribute [local instance] OAI.Yau.Target.intrinsicRoundPerturbationLocalInst11
attribute [local instance] OAI.Yau.Target.intrinsicRoundPerturbationLocalInst12
attribute [local instance] OAI.Yau.Target.intrinsicRoundPerturbationLocalInst13
attribute [local instance] OAI.Yau.Target.intrinsicRoundPerturbationLocalInst14
attribute [local instance] OAI.Yau.Target.intrinsicRoundPerturbationLocalInst15
attribute [local instance] OAI.Yau.Target.intrinsicRoundPerturbationLocalInst16
attribute [local instance] OAI.Yau.Target.intrinsicRoundPerturbationLocalInst17
attribute [local instance] OAI.Yau.Target.intrinsicRoundPerturbationLocalInst18
lemma roundTensorPerturbation_smooth (alpha : Base → ℝ)
    (ha : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ alpha) :
    IntrinsicTensorSmooth (roundTensorPerturbation alpha) :=
  ha.smul_section roundCotangentTensor_smooth

lemma roundTensorPerturbation_apply (alpha : Base → ℝ) (x : Base) (v w : SphereCotangent x) :
    roundTensorPerturbation alpha x v w = alpha x * roundCotangentTensor x v w := rfl

lemma intrinsicSphereChartTensor_add (A B : IntrinsicTensor) (p : Base) (z : BaseModel) :
    intrinsicSphereChartTensor (fun x ↦ A x+B x) p z =
      intrinsicSphereChartTensor A p z+intrinsicSphereChartTensor B p z := by
  ext i j
  rfl

lemma roundCotangentTensor_chart (p : Base) (z : BaseModel) :
    intrinsicSphereChartTensor roundCotangentTensor p z = (sphereRoundChartMatrix p z)⁻¹ := by
  rw [intrinsicSphereChartTensor_eq]
  have he : intrinsicAmbientMatrix roundCotangentTensor = fun _ ↦ 1 := funext roundCotangentTensor_ambient
  rw [he]
  have hinv := Matrix.mul_nonsing_inv (sphereRoundChartMatrix p z)
    (isUnit_iff_ne_zero.mpr (sphereRoundChartMatrix_posDef p
      (by rw [centeredSphereChart_target]; trivial)).det_pos.ne')
  simp only [sphereChartTensor,frameContravariant,Matrix.mul_one]
  simp only [Matrix.mul_assoc] at *
  rw [← Matrix.mul_assoc (sphereChartFrame p z).transpose (sphereChartFrame p z)]
  change (sphereRoundChartMatrix p z)⁻¹ * (sphereRoundChartMatrix p z * (sphereRoundChartMatrix p z)⁻¹) = _
  rw [hinv,Matrix.mul_one]

lemma roundTensorPerturbation_chart (alpha : Base → ℝ) (p : Base) (z : BaseModel) :
    intrinsicSphereChartTensor (roundTensorPerturbation alpha) p z =
      alpha ((extChartAt (𝓡 4) p).symm z) • (sphereRoundChartMatrix p z)⁻¹ := by
  rw [← roundCotangentTensor_chart]
  ext i j
  rfl

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_RoundCoordinateGradient
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Yau.Geometry Yau.Jets Manifold
open scoped ContDiff RealInnerProductSpace
noncomputable section

lemma roundCoordFactor_smooth : ContDiff ℝ ∞ roundCoordFactor := by
  unfold roundCoordFactor
  exact ((((contDiff_norm_sq ℝ).comp seedCoordEquiv.contDiff).add contDiff_const).div_const 4).pow 2

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Charts_SphereDifferentialCoordinates
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Manifold Matrix Yau.Geometry Yau.Jets
open scoped ContDiff
noncomputable section
attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace normedSpaceTangentSpaceVectorSpace

lemma roundCotangentTensor_coordinate_pair (p : Base) (x : Yau.Jets.Coord)
    (v w : Fin 4 → ℝ) :
    roundCotangentTensor (sphereChartCoordMap p x)
      (sphereCoordinateCovector p (seedCoordEquiv x) v)
      (sphereCoordinateCovector p (seedCoordEquiv x) w) =
      roundCoordFactor x * ∑ i, v i*w i := by
  change roundCotangentTensor ((extChartAt (𝓡 4) p).symm (seedCoordEquiv x))
    (sphereCoordinateCovector p (seedCoordEquiv x) v)
    (sphereCoordinateCovector p (seedCoordEquiv x) w) = _
  rw [← intrinsicAmbientMatrix_chart_pairing,← intrinsicSphereChartTensor_eq,
    roundCotangentTensor_chart,sphereRoundChartMatrix_inverse_conformal]
  simp only [Matrix.smul_mulVec,Matrix.one_mulVec,dotProduct]
  have he : ((4/(‖seedCoordEquiv x‖^2+4))^2)⁻¹ = roundCoordFactor x := by
    unfold roundCoordFactor
    field_simp
  rw [he]
  simp only [Pi.smul_apply,smul_eq_mul,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

lemma roundCotangentTensor_differential_pair (u v : Base → ℝ)
    (hu : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ u) (hv : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ v)
    (p : Base) (x : Yau.Jets.Coord) :
    roundCotangentTensor (sphereChartCoordMap p x)
      (sphereDifferential u (sphereChartCoordMap p x))
      (sphereDifferential v (sphereChartCoordMap p x)) =
      roundCoordFactor x * ∑ i, Yau.coordPartial (u ∘ sphereChartCoordMap p) x i *
        Yau.coordPartial (v ∘ sphereChartCoordMap p) x i := by
  rw [sphereDifferential_chart u hu,sphereDifferential_chart v hv,
    roundCotangentTensor_coordinate_pair]

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

lemma intrinsicDivergencePotential_smooth (rho : Base → ℝ)
    (hr : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ rho) (lam : ℝ) (p : Base) :
    ContDiff ℝ ∞ (intrinsicDivergencePotential rho lam p) :=
  roundCoordDensity_smooth.mul (intrinsicRealPotential_smooth rho hr lam p)

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

lemma partialJet_smooth (f : (ι → ℝ) → ℝ) (hf : ContDiff ℝ ∞ f)
    (ds : List ι) : ContDiff ℝ ∞ (partialJet f ds) := by
  induction ds with
  | nil => exact hf
  | cons i ds ih =>
    exact (ih.fderiv_right (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).clm_apply contDiff_const

end
end Yau.Analysis

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_RealAffinePartialJets
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Analysis
open scoped ContDiff
noncomputable section
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma partialJet_affine (f g : (ι → ℝ) → ℝ)
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (t : ℝ) (ds : List ι) :
    partialJet (fun x ↦ f x+t*g x) ds =
      fun x ↦ partialJet f ds x+t*partialJet g ds x := by
  induction ds with
  | nil => rfl
  | cons i ds ih =>
    funext x
    change fderiv ℝ (partialJet (fun y ↦ f y+t*g y) ds) x (Pi.single i 1) = _
    rw [ih, fderiv_fun_add ((partialJet_smooth f hf ds).differentiable (by simp) x)
      ((contDiff_const.mul (partialJet_smooth g hg ds)).differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) x),
      fderiv_const_mul ((partialJet_smooth g hg ds).differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) x)]
    rfl

theorem affine_partialJet_joint_continuous {T : Type*} [TopologicalSpace T]
    (s : T → ℝ) (hs : Continuous s) (f g : (ι → ℝ) → ℝ)
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (ds : List ι) :
    Continuous (fun z : T × (ι → ℝ) ↦ partialJet (fun x ↦ f x+s z.1*g x) ds z.2) := by
  simp_rw [partialJet_affine f g hf hg]
  exact ((partialJet_smooth f hf ds).continuous.comp continuous_snd).add
    ((hs.comp continuous_fst).mul ((partialJet_smooth g hg ds).continuous.comp continuous_snd))

end
end Yau.Analysis

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Charts_SpherePositiveMargins
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Manifold Yau.Geometry Yau.Jets Set
open scoped ContDiff Topology RealInnerProductSpace
noncomputable section
attribute [local instance] clmTopology clmAdd clmModule

lemma intrinsic_sphere_positive_margin (A : IntrinsicTensor) (hA : IntrinsicTensorSmooth A)
    (hs : ∀ x v w, A x v w = A x w v)
    (hp : ∀ x v, v ≠ 0 → 0 < A x v v) :
    ∃ c > 0, ∀ x v, c*roundCotangentTensor x v v ≤ A x v v := by
  let B := fun x ↦ ambientMatrixForm (intrinsicAmbientMatrix A x)
  have hB : Continuous B := (ambientMatrixForm_smooth _ (intrinsicAmbientMatrix_smooth A hA)).continuous
  have hpos (x : Base) (v : AmbientBase) (hv : v ≠ 0) : 0 < B x v v :=
    ambientMatrixForm_pos _ (intrinsicAmbientMatrix_posDef A hs hp x) v hv
  have hc : Continuous (fun z : Base × AmbientBase ↦ B z.1 z.2 z.2) :=
    ((hB.comp continuous_fst).clm_apply continuous_snd).clm_apply continuous_snd
  obtain ⟨c,hc0,_,_,hbound⟩ := compact_positive_bounds
    (isCompact_univ.prod (isCompact_sphere (0:AmbientBase) 1)) _ hc.continuousOn
    (fun z hz ↦ hpos z.1 z.2 (by intro he; simpa [he] using hz.2))
  have hb (x : Base) (v : AmbientBase) : c*‖v‖^2 ≤ B x v v := by
    by_cases hv : v = 0
    · simp [hv]
    have hn : 0 < ‖v‖ := norm_pos_iff.mpr hv
    have hu : ‖(‖v‖⁻¹:ℝ) • v‖ = 1 := by
      rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hn),inv_mul_cancel₀ hn.ne']
    have hh := (hbound (x,(‖v‖⁻¹:ℝ) • v)
      ⟨mem_univ _,by simpa only [Metric.mem_sphere,dist_zero_right] using hu⟩).1
    simp only [map_smul,smul_apply,smul_eq_mul] at hh
    have hmul := mul_le_mul_of_nonneg_left hh (sq_nonneg ‖v‖)
    have he : ‖v‖^2*(‖v‖⁻¹*(‖v‖⁻¹*B x v v)) = B x v v := by field_simp
    rw [he] at hmul
    nlinarith
  refine ⟨c,hc0,?_⟩
  intro x v
  have hh := hb x (sphereCotangentRepresentative x v)
  rw [show B x = ambientMatrixForm (intrinsicAmbientMatrix A x) from rfl,
    intrinsicAmbientMatrix_pairing,sphereCotangentRepresentative_restriction,
    sphereCotangentRepresentative_orthogonal,zero_mul,add_zero] at hh
  simpa only [roundCotangentTensor_apply,real_inner_self_eq_norm_sq] using hh

lemma intrinsic_pair_positive_margin (A : IntrinsicTensor) (hA : IntrinsicTensorSmooth A)
    (hs : ∀ x v w, A x v w = A x w v)
    (hp : ∀ x v, v ≠ 0 → 0 < A x v v) (rho : Base → ℝ)
    (hr : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ rho) (hrp : ∀ x, 0 < rho x) :
    ∃ c > 0, (∀ x v, c*roundCotangentTensor x v v ≤ A x v v) ∧ ∀ x, c ≤ rho x := by
  obtain ⟨a,ha,hb⟩ := intrinsic_sphere_positive_margin A hA hs hp
  obtain ⟨r,hr0,_,_,hrb⟩ := compact_positive_bounds isCompact_univ rho hr.continuous.continuousOn
    (fun x _ ↦ hrp x)
  refine ⟨min a r,lt_min ha hr0,?_,fun x ↦ (min_le_right _ _).trans (hrb x (mem_univ _)).1⟩
  intro x v
  have hn : 0 ≤ roundCotangentTensor x v v := by
    rw [roundCotangentTensor_apply]; exact real_inner_self_nonneg
  exact (mul_le_mul_of_nonneg_right (min_le_left _ _) hn).trans (hb x v)

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Coefficients_PositiveSphereCorrection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Manifold Yau.Geometry Set
open scoped ContDiff Topology RealInnerProductSpace
noncomputable section
attribute [local instance] clmTopology clmAdd clmModule

attribute [local instance] OAI.Yau.Target.positiveSphereCorrectionLocalInst3
attribute [local instance] OAI.Yau.Target.positiveSphereCorrectionLocalInst4
attribute [local instance] OAI.Yau.Target.positiveSphereCorrectionLocalInst1
attribute [local instance] OAI.Yau.Target.positiveSphereCorrectionLocalInst2
local instance positiveSphereCorrectionLocalInst5_r439447_1 : NormedAddCommGroup (CotangentModel →L[ℝ] CotangentModel →L[ℝ] ℝ) := ContinuousLinearMap.toNormedAddCommGroup
local instance positiveSphereCorrectionLocalInst6_r439447_1 : NormedSpace ℝ (CotangentModel →L[ℝ] CotangentModel →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace
attribute [local instance] OAI.Yau.Target.positiveSphereCorrectionLocalInst7
attribute [local instance] OAI.Yau.Target.positiveSphereCorrectionLocalInst8
attribute [local instance] OAI.Yau.Target.positiveSphereCorrectionLocalInst9
attribute [local instance] OAI.Yau.Target.positiveSphereCorrectionLocalInst10
attribute [local instance] OAI.Yau.Target.positiveSphereCorrectionLocalInst11
local instance positiveSphereCorrectionLocalInst12_r439447_1 (x : Base) : ContinuousSMul ℝ (SphereCotangent x →L[ℝ] ℝ) := ContinuousLinearMap.continuousSMul
attribute [local instance] OAI.Yau.Target.positiveSphereCorrectionLocalInst13
local instance positiveSphereCorrectionLocalInst14_r439447_1 : TopologicalSpace (Bundle.TotalSpace (CotangentModel →L[ℝ] CotangentModel →L[ℝ] ℝ)
    (fun x : Base ↦ SphereCotangent x →L[ℝ] SphereCotangent x →L[ℝ] ℝ)) :=
  Bundle.ContinuousLinearMap.topologicalSpaceTotalSpace (RingHom.id ℝ) CotangentModel SphereCotangent
    (CotangentModel →L[ℝ] ℝ) (fun x : Base ↦ SphereCotangent x →L[ℝ] ℝ)
attribute [local instance] OAI.Yau.Target.positiveSphereCorrectionLocalInst15
attribute [local instance] OAI.Yau.Target.positiveSphereCorrectionLocalInst16
lemma round_perturbed_pair_positive (A : IntrinsicTensor) (rho alpha beta : Base → ℝ)
    {c : ℝ} (hc : 0 < c)
    (hA : ∀ x v, c*roundCotangentTensor x v v ≤ A x v v)
    (hr : ∀ x, c ≤ rho x) (ha : ∀ x, |alpha x| < c) (hb : ∀ x, |beta x| < c) :
    (∀ x v, v ≠ 0 → 0 < (A x+roundTensorPerturbation alpha x) v v) ∧
    ∀ x, 0 < rho x+beta x := by
  constructor
  · intro x v hv
    have hp := roundCotangentTensor_pos x v hv
    have hlow := hA x v
    have hs := (abs_lt.mp (ha x)).1
    have hmul : 0 < (c+alpha x)*roundCotangentTensor x v v := mul_pos (by linarith) hp
    change 0 < A x v v+alpha x*roundCotangentTensor x v v
    nlinarith
  · intro x
    by_cases hbeta : 0 ≤ beta x
    · exact add_pos_of_pos_of_nonneg (hc.trans_le (hr x)) hbeta
    have hs := (abs_lt.mp (hb x)).1
    have := hr x
    linarith

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
-- module Solutions.OAIQ237_NY.NodalSets_Coefficients_MatrixCoefficientBounds
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Matrix Yau.Geometry
open scoped ContDiff
noncomputable section
attribute [local instance] clmTopology clmAdd clmModule
attribute [local instance] ContinuousLinearMap.toNormedAddCommGroup ContinuousLinearMap.toNormedSpace

lemma matrixContravariant_add (A B : Matrix (Fin 4) (Fin 4) ℝ) :
    matrixContravariant (A+B) = matrixContravariant A+matrixContravariant B := by
  ext α i
  simp [matrixContravariant,add_smul,Finset.sum_add_distrib]

lemma matrixContravariant_entry_sum (A : Matrix (Fin 4) (Fin 4) ℝ) :
    matrixContravariant A = ∑ i, ∑ j, coefficientEntryLinear i j (A i j) := rfl

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Coefficients_IntrinsicCoefficientIncrementBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Manifold Yau.Geometry Yau.Jets
open scoped ContDiff
noncomputable section
attribute [local instance] clmTopology clmAdd clmModule
attribute [local instance] ContinuousLinearMap.toNormedAddCommGroup ContinuousLinearMap.toNormedSpace
attribute [local instance] intrinsicRoundPerturbationLocalInst17 intrinsicRoundPerturbationLocalInst18

lemma intrinsicChartCoefficient_increment (A B : IntrinsicTensor) (rho b : Base → ℝ)
    (p : Base) (z : BaseModel) :
    intrinsicChartCoefficient (fun x ↦ A x+B x) (fun x ↦ rho x+b x) p z -
      intrinsicChartCoefficient A rho p z = intrinsicChartCoefficient B b p z := by
  apply Prod.ext
  · simp only [intrinsicChartCoefficient,Prod.fst_sub,intrinsicSphereChartTensor_add,
      matrixContravariant_add,add_sub_cancel_left]
  · simp [intrinsicChartCoefficient]

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Coefficients_SupportedCoefficientChartBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Manifold Yau.Geometry Yau.Jets Set
open scoped ContDiff
noncomputable section
attribute [local instance] clmTopology clmAdd clmModule
attribute [local instance] ContinuousLinearMap.toNormedAddCommGroup ContinuousLinearMap.toNormedSpace
attribute [local instance] intrinsicRoundPerturbationLocalInst17 intrinsicRoundPerturbationLocalInst18

lemma roundTensorPerturbation_any_entry (a : Base → ℝ) (p : Base) (x : Yau.Jets.Coord) (j k : Fin 4) :
    intrinsicSphereChartTensor (roundTensorPerturbation a) p (seedCoordEquiv x) j k =
      if j=k then roundCoordFactor x*a (sphereChartCoordMap p x) else 0 := by
  rw [roundTensorPerturbation_chart,sphereRoundChartMatrix_inverse_conformal]
  have hfac : (((4:ℝ)/(‖seedCoordEquiv x‖^2+4))^2)⁻¹ = roundCoordFactor x := by
    unfold roundCoordFactor
    field_simp
  rw [hfac]
  simp [Matrix.one_apply,sphereChartCoordMap,mul_comm]

lemma round_increment_any_entry_smooth (a : Base → ℝ)
    (ha : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ a) (p : Base) (j k : Fin 4) :
    ContDiff ℝ ∞ (fun x ↦ intrinsicSphereChartTensor (roundTensorPerturbation a) p (seedCoordEquiv x) j k) := by
  simp_rw [roundTensorPerturbation_any_entry]
  split_ifs
  · exact roundCoordFactor_smooth.mul (ha.comp (sphereChartCoordMap_smooth p)).contDiff
  · exact contDiff_const

lemma intrinsic_any_increment_pullback_smooth (a b : Base → ℝ)
    (ha : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ a) (hb : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ b) (p : Base) :
    ContDiff ℝ ∞ (fun x ↦ intrinsicChartCoefficient (roundTensorPerturbation a) b p (seedCoordEquiv x)) := by
  apply ContDiff.prodMk _ (hb.comp (sphereChartCoordMap_smooth p)).contDiff
  change ContDiff ℝ ∞ (fun x ↦ matrixContravariant
    (intrinsicSphereChartTensor (roundTensorPerturbation a) p (seedCoordEquiv x)))
  simp_rw [matrixContravariant_entry_sum]
  let : IsBoundedSMul ℝ ((BaseModel →L[ℝ] ℝ) →L[ℝ] BaseModel) :=
    IsBoundedSMul.of_norm_smul_le ContinuousLinearMap.opNorm_smul_le
  exact ContDiff.sum (fun j _ ↦ ContDiff.sum (fun k _ ↦
    (round_increment_any_entry_smooth a ha p j k).smul contDiff_const))

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
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_SmallRoundPerturbation
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

lemma intrinsic_round_increment_smooth (a b : Base → ℝ)
    (ha : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ a) (hb : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ b)
    (p : Base) : ContDiff ℝ ∞ (intrinsicChartCoefficient (roundTensorPerturbation a) b p) := by
  have h := (intrinsic_any_increment_pullback_smooth a b ha hb p).comp seedCoordEquiv.symm.contDiff
  simpa only [Function.comp_def,ContinuousLinearEquiv.apply_symm_apply] using h

lemma intrinsic_round_increment_smul (a b : Base → ℝ) (t : ℝ) (p : Base) (z : BaseModel) :
    intrinsicChartCoefficient (roundTensorPerturbation (fun x ↦ t*a x)) (fun x ↦ t*b x) p z =
      t • intrinsicChartCoefficient (roundTensorPerturbation a) b p z := by
  apply Prod.ext
  · change matrixContravariant (intrinsicSphereChartTensor
        (roundTensorPerturbation (fun x ↦ t*a x)) p z) =
      t • matrixContravariant (intrinsicSphereChartTensor (roundTensorPerturbation a) p z)
    simp only [roundTensorPerturbation_chart,matrixContravariant,Matrix.smul_apply,
      smul_eq_mul,Finset.smul_sum,smul_smul,mul_assoc]
  · rfl

lemma sphereCoefficientDistance_round_smul (P : Finset Base) (J : ℕ)
    (A : IntrinsicTensor) (rho a b : Base → ℝ)
    (ha : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ a) (hb : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ b) (t : ℝ) :
    sphereCoefficientDistance P J A rho
      (fun x ↦ A x+roundTensorPerturbation (fun y ↦ t*a y) x) (fun x ↦ rho x+t*b x) =
      |t| * finiteChartDerivativeSize P sphereAtlasCore J
        (intrinsicChartCoefficient (roundTensorPerturbation a) b) := by
  simp only [sphereCoefficientDistance,intrinsicChartCoefficient_increment,intrinsic_round_increment_smul]
  simpa only [Real.norm_eq_abs] using finiteChartDerivativeSize_smul P sphereAtlasCore_compact J t
    (intrinsicChartCoefficient (roundTensorPerturbation a) b)
    (fun p _ ↦ intrinsic_round_increment_smooth a b ha hb p)

theorem small_round_perturbation_in_finite_atlas
    (A : IntrinsicTensor) (hA : IntrinsicTensorSmooth A)
    (hs : ∀ x v w, A x v w = A x w v) (hp : ∀ x v, v ≠ 0 → 0 < A x v v)
    (rho : Base → ℝ) (hr : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ rho) (hrp : ∀ x, 0 < rho x)
    (a b : Base → ℝ) (ha : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ a)
    (hb : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ b) (P : Finset Base) (J : ℕ) {eps : ℝ} (heps : 0 < eps) :
    ∃ delta > 0, ∀ t : ℝ, |t| < delta →
      IntrinsicTensorSmooth (fun x ↦ A x+roundTensorPerturbation (fun y ↦ t*a y) x) ∧
      (∀ x v w, (A x+roundTensorPerturbation (fun y ↦ t*a y) x) v w =
        (A x+roundTensorPerturbation (fun y ↦ t*a y) x) w v) ∧
      (∀ x v, v ≠ 0 → 0 < (A x+roundTensorPerturbation (fun y ↦ t*a y) x) v v) ∧
      ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ (fun x ↦ rho x+t*b x) ∧
      (∀ x, 0 < rho x+t*b x) ∧
      sphereCoefficientDistance P J A rho
        (fun x ↦ A x+roundTensorPerturbation (fun y ↦ t*a y) x) (fun x ↦ rho x+t*b x) < eps := by
  obtain ⟨c,hc,hAm,hrm⟩ := intrinsic_pair_positive_margin A hA hs hp rho hr hrp
  obtain ⟨Ba,hBa⟩ := isCompact_univ.exists_bound_of_continuousOn ha.continuous.continuousOn
  obtain ⟨Bb,hBb⟩ := isCompact_univ.exists_bound_of_continuousOn hb.continuous.continuousOn
  let B : ℝ := max 0 (max Ba Bb)+1
  have hB : 0 < B := by dsimp [B]; have := le_max_left (0:ℝ) (max Ba Bb); linarith
  have hab (x : Base) : |a x| ≤ B := by
    have h := hBa x (mem_univ x)
    rw [Real.norm_eq_abs] at h
    have hh : Ba ≤ max 0 (max Ba Bb) := (le_max_left Ba Bb).trans (le_max_right _ _)
    dsimp [B] <;> linarith
  have hbb (x : Base) : |b x| ≤ B := by
    have h := hBb x (mem_univ x)
    rw [Real.norm_eq_abs] at h
    have hh : Bb ≤ max 0 (max Ba Bb) := (le_max_right Ba Bb).trans (le_max_right _ _)
    dsimp [B] <;> linarith
  let C := finiteChartDerivativeSize P sphereAtlasCore J
    (intrinsicChartCoefficient (roundTensorPerturbation a) b)
  have hC : 0 ≤ C := finiteChartDerivativeSize_nonneg P sphereAtlasCore_compact J _
    (fun p _ ↦ intrinsic_round_increment_smooth a b ha hb p)
  refine ⟨min (c/B) (eps/(C+1)),lt_min (div_pos hc hB) (div_pos heps (by linarith)),?_⟩
  intro t ht
  have htB : |t| * B < c := (lt_div_iff₀ hB).mp (ht.trans_le (min_le_left _ _))
  have htC : |t| * (C+1) < eps := (lt_div_iff₀ (by linarith : 0 < C+1)).mp
    (ht.trans_le (min_le_right _ _))
  obtain ⟨hpos,hden⟩ := round_perturbed_pair_positive A rho (fun x ↦ t*a x) (fun x ↦ t*b x)
    hc hAm hrm
    (fun x ↦ by rw [abs_mul]; exact (mul_le_mul_of_nonneg_left (hab x) (abs_nonneg t)).trans_lt htB)
    (fun x ↦ by rw [abs_mul]; exact (mul_le_mul_of_nonneg_left (hbb x) (abs_nonneg t)).trans_lt htB)
  refine ⟨hA.add_section (roundTensorPerturbation_smooth _ (contMDiff_const.mul ha)),?_,hpos,
    hr.add (contMDiff_const.mul hb),hden,?_⟩
  · intro x v w
    change A x v w+(t*a x)*roundCotangentTensor x v w = A x w v+(t*a x)*roundCotangentTensor x w v
    rw [hs,roundCotangentTensor_symm]
  · rw [sphereCoefficientDistance_round_smul P J A rho a b ha hb t]
    change |t| * C < eps
    nlinarith [abs_nonneg t]

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Charts_SphereAffineDivergenceJets
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Manifold Yau.Geometry Yau.Analysis
open scoped ContDiff
noncomputable section
attribute [local instance] clmTopology clmAdd clmModule
attribute [local instance] intrinsicRoundPerturbationLocalInst17 intrinsicRoundPerturbationLocalInst18

lemma intrinsicDivergencePrincipal_affine (A : IntrinsicTensor) (a : Base → ℝ)
    (t : ℝ) (p : Base) (x : Yau.Jets.Coord) (i j : Fin 4) :
    intrinsicDivergencePrincipal
      (fun y ↦ A y+roundTensorPerturbation (fun z ↦ t*a z) y) p x i j =
      intrinsicDivergencePrincipal A p x i j+
        t*intrinsicDivergencePrincipal (roundTensorPerturbation a) p x i j := by
  simp only [intrinsicDivergencePrincipal,intrinsicRealPrincipal,intrinsicSphereChartTensor_add,
    roundTensorPerturbation_chart,Matrix.add_apply,Matrix.smul_apply,smul_eq_mul]
  ring

lemma intrinsicDivergencePotential_affine (rho b : Base → ℝ) (lam t : ℝ)
    (p : Base) (x : Yau.Jets.Coord) :
    intrinsicDivergencePotential (fun y ↦ rho y+t*b y) lam p x =
      intrinsicDivergencePotential rho lam p x+t*intrinsicDivergencePotential b lam p x := by
  simp only [intrinsicDivergencePotential,intrinsicRealPotential]
  ring

lemma intrinsicDivergencePrincipal_round_smooth (a : Base → ℝ)
    (ha : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ a) (p : Base) (i j : Fin 4) :
    ContDiff ℝ ∞ (fun x ↦ intrinsicDivergencePrincipal (roundTensorPerturbation a) p x i j) :=
  roundCoordDensity_smooth.mul (round_increment_any_entry_smooth a ha p i j)

theorem sphere_affine_principal_joint_jets {T : Type*} [TopologicalSpace T]
    (s : T → ℝ) (hs : Continuous s) (A : IntrinsicTensor) (hA : IntrinsicTensorSmooth A)
    (hAs : ∀ x v w, A x v w = A x w v) (hAp : ∀ x v, v ≠ 0 → 0 < A x v v)
    (a : Base → ℝ) (ha : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ a)
    (p : Base) (i j : Fin 4) (ds : List (Fin 4)) :
    Continuous (fun z : T × Yau.Jets.Coord ↦ partialJet
      (fun x ↦ intrinsicDivergencePrincipal
        (fun y ↦ A y+roundTensorPerturbation (fun q ↦ s z.1*a q) y) p x i j) ds z.2) := by
  simp_rw [intrinsicDivergencePrincipal_affine]
  exact affine_partialJet_joint_continuous s hs _ _
    (intrinsicDivergencePrincipal_smooth A hA hAs hAp p i j)
    (intrinsicDivergencePrincipal_round_smooth a ha p i j) ds

theorem sphere_affine_potential_joint_jets {T : Type*} [TopologicalSpace T]
    (s : T → ℝ) (hs : Continuous s) (rho b : Base → ℝ)
    (hr : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ rho) (hb : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ b)
    (lam : ℝ) (p : Base) (ds : List (Fin 4)) :
    Continuous (fun z : T × Yau.Jets.Coord ↦ partialJet
      (intrinsicDivergencePotential (fun y ↦ rho y+s z.1*b y) lam p) ds z.2) := by
  simp_rw [show ∀ t : ℝ, intrinsicDivergencePotential (fun y ↦ rho y+t*b y) lam p =
    fun x ↦ intrinsicDivergencePotential rho lam p x+t*intrinsicDivergencePotential b lam p x
    from fun t ↦ funext (intrinsicDivergencePotential_affine rho b lam t p)]
  exact affine_partialJet_joint_continuous s hs _ _
    (intrinsicDivergencePotential_smooth rho hr lam p)
    (intrinsicDivergencePotential_smooth b hb lam p) ds

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Charts_SphereEnergyForm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Manifold Matrix Yau.Geometry Yau.Jets Set MeasureTheory
open scoped ContDiff
noncomputable section
attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace normedSpaceTangentSpaceVectorSpace

local instance sphereEnergyFormLocal1_r439447_1 : MeasurableSpace Base := borel Base
local instance sphereEnergyFormLocal2_r439447_1 : BorelSpace Base := ⟨rfl⟩
lemma sphereEnergyDensity_chart (a b : Base → ℝ) (lam : ℝ) (v w : Base → ℝ)
    (hv : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ v) (hw : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ w)
    (p : Base) (x : Yau.Jets.Coord) :
    sphereEnergyDensity a b lam v w (sphereChartCoordMap p x) =
      a (sphereChartCoordMap p x) * roundCoordFactor x *
        (∑ i, Yau.coordPartial (v ∘ sphereChartCoordMap p) x i *
          Yau.coordPartial (w ∘ sphereChartCoordMap p) x i) -
      lam*b (sphereChartCoordMap p x)*v (sphereChartCoordMap p x)*w (sphereChartCoordMap p x) := by
  rw [sphereEnergyDensity,roundTensorPerturbation_apply,roundCotangentTensor_differential_pair v w hv hw]
  ring

lemma sphereEnergyForm_chart (a b : Base → ℝ) (lam : ℝ) (v w : Base → ℝ)
    (hv : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ v) (hw : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ w) (p : Base) :
    sphereEnergyForm a b lam v w = ∫ x, roundCoordDensity x *
      (a (sphereChartCoordMap p x)*roundCoordFactor x*
        (∑ i, Yau.coordPartial (v ∘ sphereChartCoordMap p) x i *
          Yau.coordPartial (w ∘ sphereChartCoordMap p) x i) -
      lam*b (sphereChartCoordMap p x)*v (sphereChartCoordMap p x)*w (sphereChartCoordMap p x)) := by
  rw [sphereEnergyForm,sphereReferenceMeasure_integral_chart p]
  simp only [roundChartDensity_coord_eq,sphereEnergyDensity_chart a b lam v w hv hw]

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
-- module Solutions.OAIQ237_NY.NodalSets_Charts_SphereAffineFormAnnihilation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Manifold Yau.Geometry MeasureTheory
open scoped ContDiff
noncomputable section
attribute [local instance] clmTopology clmAdd clmModule
attribute [local instance] intrinsicRoundPerturbationLocalInst17 intrinsicRoundPerturbationLocalInst18

theorem sphere_affine_form_annihilates (A : IntrinsicTensor) (hA : IntrinsicTensorSmooth A)
    (hs : ∀ x alpha beta, A x alpha beta = A x beta alpha)
    (hp : ∀ x alpha, alpha ≠ 0 → 0 < A x alpha alpha)
    (rho : Base → ℝ) (hr : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ rho) (hrp : ∀ x, 0 < rho x)
    (a b : Base → ℝ) (hb : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ b) (lam t : ℝ) (ht : t ≠ 0)
    (hAt : IntrinsicTensorSmooth (fun x ↦ A x+roundTensorPerturbation (fun y ↦ t*a y) x))
    (hst : ∀ x alpha beta, (A x+roundTensorPerturbation (fun y ↦ t*a y) x) alpha beta =
      (A x+roundTensorPerturbation (fun y ↦ t*a y) x) beta alpha)
    (hpt : ∀ x alpha, alpha ≠ 0 → 0 < (A x+roundTensorPerturbation (fun y ↦ t*a y) x) alpha alpha)
    (hrpt : ∀ x, 0 < rho x+t*b x)
    (w f : Base → ℝ) (hw : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ w)
    (hf : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ f)
    (hew : ∀ p z, -intrinsicWeightedChartOperator
      (fun x ↦ A x+roundTensorPerturbation (fun y ↦ t*a y) x)
      (fun x ↦ rho x+t*b x) w p z = lam*w ((extChartAt (𝓡 4) p).symm z))
    (hef : ∀ p z, -intrinsicWeightedChartOperator A rho f p z =
      lam*f ((extChartAt (𝓡 4) p).symm z)) :
    sphereEnergyForm a b lam w f = 0 := by
  let At : IntrinsicTensor := fun x ↦ A x+roundTensorPerturbation (fun y ↦ t*a y) x
  let rt : Base → ℝ := fun x ↦ rho x+t*b x
  have hrt : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ rt := hr.add (contMDiff_const.mul hb)
  obtain ⟨hE0,hD0,h0⟩ := intrinsic_green_eigenfunction_test A hA hs hp rho hr hrp w f hw hf lam hef
  obtain ⟨_,_,hnew⟩ := intrinsic_green_eigenfunction_test At hAt hst hpt rt hrt hrpt f w hf hw lam hew
  have hEt := intrinsic_differential_pair_integrable At hAt hst hpt w f hw hf
  have hDt := sphereWeightedPairing_integrable rt w f hrt.continuous hw.continuous hf.continuous
  have hnew' : (∫ x, At x (sphereDifferential w x) (sphereDifferential f x) ∂sphereReferenceMeasure) =
      lam*sphereWeightedPairing rt w f := by
    rw [sphereWeightedPairing_symm rt w f,← hnew]
    exact integral_congr_ae (Filter.Eventually.of_forall (fun x ↦ hst x _ _))
  have heq (x : Base) : t*sphereEnergyDensity a b lam w f x =
      (At x (sphereDifferential w x) (sphereDifferential f x)-lam*(rt x*w x*f x)) -
      (A x (sphereDifferential w x) (sphereDifferential f x)-lam*(rho x*w x*f x)) := by
    change t*(a x*roundCotangentTensor x (sphereDifferential w x) (sphereDifferential f x)-
      lam*b x*w x*f x) =
      (A x (sphereDifferential w x) (sphereDifferential f x)+
        (t*a x)*roundCotangentTensor x (sphereDifferential w x) (sphereDifferential f x)-
        lam*((rho x+t*b x)*w x*f x)) -
      (A x (sphereDifferential w x) (sphereDifferential f x)-lam*(rho x*w x*f x))
    ring
  have hFt : Integrable (fun x ↦ At x (sphereDifferential w x) (sphereDifferential f x)-
      lam*(rt x*w x*f x)) sphereReferenceMeasure := hEt.sub (hDt.const_mul lam)
  have hF0 : Integrable (fun x ↦ A x (sphereDifferential w x) (sphereDifferential f x)-
      lam*(rho x*w x*f x)) sphereReferenceMeasure := hE0.sub (hD0.const_mul lam)
  have hzero : t*sphereEnergyForm a b lam w f = 0 := by
    rw [sphereEnergyForm,← integral_const_mul]
    simp_rw [heq]
    rw [integral_sub hFt hF0,
      integral_sub hEt (hDt.const_mul lam),integral_sub hE0 (hD0.const_mul lam),
      integral_const_mul,integral_const_mul,hnew',h0]
    change lam*sphereWeightedPairing rt w f-lam*sphereWeightedPairing rt w f-
      (lam*sphereWeightedPairing rho w f-lam*sphereWeightedPairing rho w f)=0
    ring
  exact (mul_eq_zero.mp hzero).resolve_left ht

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Charts_SphereAffinePositiveInterval
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Manifold Yau.Geometry Yau.Analysis Set
open scoped ContDiff
noncomputable section
attribute [local instance] clmTopology clmAdd clmModule
attribute [local instance] intrinsicRoundPerturbationLocalInst17 intrinsicRoundPerturbationLocalInst18

theorem sphere_affine_positive_interval
    (A : IntrinsicTensor) (hA : IntrinsicTensorSmooth A)
    (hs : ∀ x v w, A x v w = A x w v) (hp : ∀ x v, v ≠ 0 → 0 < A x v v)
    (rho : Base → ℝ) (hr : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ rho) (hrp : ∀ x, 0 < rho x)
    (a b : Base → ℝ) (ha : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ a)
    (hb : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ b) (lam : ℝ) :
    ∃ delta > 0,
      (∀ t ∈ Icc (-delta) delta,
        IntrinsicTensorSmooth (fun x ↦ A x+roundTensorPerturbation (fun y ↦ t*a y) x) ∧
        (∀ x v w, (A x+roundTensorPerturbation (fun y ↦ t*a y) x) v w =
          (A x+roundTensorPerturbation (fun y ↦ t*a y) x) w v) ∧
        (∀ x v, v ≠ 0 → 0 < (A x+roundTensorPerturbation (fun y ↦ t*a y) x) v v) ∧
        ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ (fun x ↦ rho x+t*b x) ∧
        (∀ x, 0 < rho x+t*b x)) ∧
      Continuous (fun z : Icc (-delta) delta × Base ↦ rho z.2+(z.1:ℝ)*b z.2) ∧
      (∀ p i j ds, Continuous (fun z : Icc (-delta) delta × Yau.Jets.Coord ↦
        partialJet (fun x ↦ intrinsicDivergencePrincipal
          (fun y ↦ A y+roundTensorPerturbation (fun q ↦ (z.1:ℝ)*a q) y) p x i j) ds z.2)) ∧
      (∀ p ds, Continuous (fun z : Icc (-delta) delta × Yau.Jets.Coord ↦
        partialJet (intrinsicDivergencePotential
          (fun y ↦ rho y+(z.1:ℝ)*b y) lam p) ds z.2)) := by
  obtain ⟨d,hd,hsmall⟩ := small_round_perturbation_in_finite_atlas
    A hA hs hp rho hr hrp a b ha hb ∅ 0 (by norm_num : (0:ℝ)<1)
  refine ⟨d/2,by positivity,?_,?_,?_,?_⟩
  · intro t ht
    have ht' : |t| < d := (abs_le.mpr ht).trans_lt (by linarith)
    obtain ⟨h1,h2,h3,h4,h5,_⟩ := hsmall t ht'
    exact ⟨h1,h2,h3,h4,h5⟩
  · exact (hr.continuous.comp continuous_snd).add
      ((continuous_subtype_val.comp continuous_fst).mul (hb.continuous.comp continuous_snd))
  · exact fun p i j ds ↦ sphere_affine_principal_joint_jets
      Subtype.val continuous_subtype_val A hA hs hp a ha p i j ds
  · exact fun p ds ↦ sphere_affine_potential_joint_jets
      Subtype.val continuous_subtype_val rho b hr hb lam p ds

end
end Yau.Target

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
-- module Solutions.OAIQ237_NY.NodalSets_Charts_SphereAffineNormalizedLimit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Manifold Yau.Analysis Yau.Geometry Set Filter
open scoped Topology ContDiff
noncomputable section
attribute [local instance] clmTopology clmAdd clmModule
attribute [local instance] intrinsicRoundPerturbationLocalInst17 intrinsicRoundPerturbationLocalInst18

theorem sphere_affine_normalized_limit
    (A : IntrinsicTensor) (hA : IntrinsicTensorSmooth A)
    (hs : ∀ x v w, A x v w = A x w v) (hp : ∀ x v, v ≠ 0 → 0 < A x v v)
    (rho : Base → ℝ) (hr : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ rho) (hrp : ∀ x, 0 < rho x)
    (a b : Base → ℝ) (ha : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ a)
    (hb : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ b) (lam : ℝ)
    (t : ℕ → ℝ) (ht : Tendsto t atTop (𝓝 0))
    (w : ℕ → Base → ℝ) (hw : ∀ j, ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ (w j))
    (he : ∀ j p z, -intrinsicWeightedChartOperator
      (fun x ↦ A x+roundTensorPerturbation (fun y ↦ t j*a y) x)
      (fun x ↦ rho x+t j*b x) (w j) p z = lam*w j ((extChartAt (𝓡 4) p).symm z))
    (hn : ∀ j, sphereWeightedPairing (fun x ↦ rho x+t j*b x) (w j) (w j)=1)
    (u : Base → ℝ) (hu : Continuous u)
    (ho : ∀ j, sphereWeightedPairing (fun x ↦ rho x+t j*b x) (w j) u=0) :
    ∃ v : Base → ℝ, ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ v ∧ v ≠ 0 ∧
      (∀ p z, -intrinsicWeightedChartOperator A rho v p z =
        lam*v ((extChartAt (𝓡 4) p).symm z)) ∧
      sphereWeightedPairing rho v v=1 ∧ sphereWeightedPairing rho v u=0 ∧
      ∃ nu : ℕ → ℕ, StrictMono nu ∧ TendstoUniformly (fun j ↦ w (nu j)) v atTop ∧
        (∀ p ds (Q : Set Yau.Jets.Coord), IsCompact Q →
          TendstoUniformlyOn (fun j ↦ partialJet (w (nu j) ∘ sphereChartCoordMap p) ds)
            (partialJet (v ∘ sphereChartCoordMap p) ds) atTop Q) ∧
        (∀ p n (Q : Set Yau.Jets.Coord), IsCompact Q →
          TendstoUniformlyOn (fun j ↦ iteratedFDeriv ℝ n (w (nu j) ∘ sphereChartCoordMap p))
            (iteratedFDeriv ℝ n (v ∘ sphereChartCoordMap p)) atTop Q) := by
  obtain ⟨delta,hdelta,hpos,hrjoint,hCjoint,hVjoint⟩ :=
    sphere_affine_positive_interval A hA hs hp rho hr hrp a b ha hb lam
  have hmem : ∀ᶠ j in atTop, t j ∈ Icc (-delta) delta :=
    ht.eventually (Icc_mem_nhds (by linarith) hdelta)
  obtain ⟨N,hN⟩ := eventually_atTop.mp hmem
  let shift : ℕ → ℕ := fun j ↦ j+N
  have hshift : StrictMono shift := fun i j hij ↦ Nat.add_lt_add_right hij N
  let s : ℕ → Icc (-delta) delta := fun j ↦ ⟨t (shift j),hN _ (Nat.le_add_left N j)⟩
  let s0 : Icc (-delta) delta := ⟨0,by constructor <;> linarith⟩
  have hst : Tendsto s atTop (𝓝 s0) := tendsto_subtype_rng.mpr (ht.comp hshift.tendsto_atTop)
  let Af : Icc (-delta) delta → IntrinsicTensor :=
    fun t x ↦ A x+roundTensorPerturbation (fun y ↦ (t:ℝ)*a y) x
  let rf : Icc (-delta) delta → Base → ℝ := fun t x ↦ rho x+(t:ℝ)*b x
  obtain ⟨v,hv,hvne,hev,hvn,hvo,mu,hmu,hval,hpartial,hderiv⟩ := sphere_normalized_global_limit
    Af rf (fun t ↦ (hpos t t.property).1) (fun t ↦ (hpos t t.property).2.1)
    (fun t ↦ (hpos t t.property).2.2.1) (fun t ↦ (hpos t t.property).2.2.2.1)
    (fun t ↦ (hpos t t.property).2.2.2.2) hrjoint lam hCjoint hVjoint s s0 hst
    (fun j ↦ w (shift j)) (fun j ↦ hw _) (fun j ↦ he _) (fun j ↦ hn _) u hu (fun j ↦ ho _)
  have hAzero : Af s0 = A := by
    funext x
    simp [Af,s0,roundTensorPerturbation]
  have hrzero : rf s0 = rho := by
    funext x
    simp [rf,s0]
  rw [hAzero,hrzero] at hev
  rw [hrzero] at hvn hvo
  exact ⟨v,hv,hvne,hev,hvn,hvo,shift ∘ mu,hshift.comp hmu,hval,hpartial,hderiv⟩

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_CompactUniformIntegralLimit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Analysis
open Set Filter MeasureTheory
open scoped Topology
noncomputable section

theorem compact_uniform_integral_limit {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
    [BorelSpace X] [T2Space X] (mu : Measure X) [IsLocallyFiniteMeasure mu]
    (Q : Set X) (hQ : IsCompact Q) (F : ℕ → X → ℝ) (f : X → ℝ)
    (hF : ∀ j, Continuous (F j)) (hf : Continuous f)
    (hFs : ∀ j x, x ∉ Q → F j x=0) (hfs : ∀ x, x ∉ Q → f x=0)
    (hconv : TendstoUniformlyOn F f atTop Q) :
    Tendsto (fun j ↦ ∫ x, F j x ∂mu) atTop (𝓝 (∫ x, f x ∂mu)) := by
  have hfinite : IsFiniteMeasure (mu.restrict Q) := ⟨by
    rw [Measure.restrict_apply_univ]
    exact hQ.measure_lt_top⟩
  obtain ⟨C,hC⟩ := hQ.exists_bound_of_continuousOn hf.continuousOn
  have hbound : ∃ B, ∀ᶠ j in atTop, ∀ᵐ x ∂mu.restrict Q, ‖F j x‖ ≤ B := by
    refine ⟨C+1,?_⟩
    filter_upwards [Metric.tendstoUniformlyOn_iff.mp hconv 1 (by norm_num)] with j hj
    filter_upwards [ae_restrict_mem hQ.measurableSet] with x hx
    have hb : |f x| ≤ C := hC x hx
    have hd : |f x-F j x| < 1 := by simpa only [Real.dist_eq] using hj x hx
    have h1 := abs_le.mp hb
    have h2 := abs_lt.mp hd
    exact abs_le.mpr ⟨by linarith,by linarith⟩
  have ht := tendsto_integral_filter_of_norm_le_const
    (μ := mu.restrict Q)
    (Eventually.of_forall (fun j ↦ (hF j).aestronglyMeasurable)) hbound
    ((ae_restrict_mem hQ.measurableSet).mono (fun x hx ↦ hconv.tendsto_at hx))
  simpa only [setIntegral_eq_integral_of_forall_compl_eq_zero (hFs _),
    setIntegral_eq_integral_of_forall_compl_eq_zero hfs] using ht

end
end Yau.Analysis

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_CompactUniformProducts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Analysis
open Set Filter
open scoped Topology
noncomputable section

theorem compact_uniform_mul {X : Type*} [TopologicalSpace X] [T2Space X]
    (Q : Set X) (hQ : IsCompact Q) (F G : ℕ → X → ℝ) (f g : X → ℝ)
    (hF : ∀ j, Continuous (F j)) (hG : ∀ j, Continuous (G j))
    (hf : Continuous f) (hg : Continuous g)
    (hFc : TendstoUniformlyOn F f atTop Q) (hGc : TendstoUniformlyOn G g atTop Q) :
    TendstoUniformlyOn (fun j x ↦ F j x*G j x) (fun x ↦ f x*g x) atTop Q := by
  let := isCompact_iff_compactSpace.mp hQ
  have h1 := (hf.continuousOn.tendsto_domRestrict_iff_tendstoUniformlyOn
    (fun j ↦ (hF j).continuousOn)).mpr hFc
  have h2 := (hg.continuousOn.tendsto_domRestrict_iff_tendstoUniformlyOn
    (fun j ↦ (hG j).continuousOn)).mpr hGc
  exact ((hf.mul hg).continuousOn.tendsto_domRestrict_iff_tendstoUniformlyOn
    (fun j ↦ ((hF j).mul (hG j)).continuousOn)).mp (h1.mul h2)

theorem finite_uniform_sum {X I : Type*} (S : Finset I) (Q : Set X)
    (F : I → ℕ → X → ℝ) (f : I → X → ℝ)
    (h : ∀ i ∈ S, TendstoUniformlyOn (F i) (f i) atTop Q) :
    TendstoUniformlyOn (fun j x ↦ ∑ i ∈ S, F i j x) (fun x ↦ ∑ i ∈ S, f i x) atTop Q := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa using ((by intro s hs; exact Eventually.of_forall (fun _ _ _ ↦ refl_mem_uniformity hs)) :
      TendstoUniformlyOn (fun _ : ℕ ↦ fun _ : X ↦ (0:ℝ)) (fun _ ↦ 0) atTop Q)
  | @insert i S hi ih =>
    simpa only [Finset.sum_insert hi,Pi.add_def] using
      (h i (Finset.mem_insert_self i S)).add (ih (fun k hk ↦ h k (Finset.mem_insert_of_mem hk)))

end
end Yau.Analysis

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_CompactFirstJetFunctionalLimit
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Analysis
open Set Filter MeasureTheory
open scoped Topology ContDiff
noncomputable section

theorem compact_first_jet_functional_limit
    (Q : Set Yau.Jets.Coord) (hQ : IsCompact Q)
    (a : Fin 4 → Yau.Jets.Coord → ℝ) (b : Yau.Jets.Coord → ℝ)
    (ha : ∀ i, Continuous (a i)) (hb : Continuous b)
    (has : ∀ i x, x ∉ Q → a i x=0) (hbs : ∀ x, x ∉ Q → b x=0)
    (W : ℕ → Yau.Jets.Coord → ℝ) (v : Yau.Jets.Coord → ℝ)
    (hW : ∀ j, ContDiff ℝ ∞ (W j)) (hv : ContDiff ℝ ∞ v)
    (hconv : ∀ ds, TendstoUniformlyOn (fun j ↦ partialJet (W j) ds) (partialJet v ds) atTop Q) :
    Tendsto (fun j ↦ ∫ x, (∑ i, a i x*partialJet (W j) [i] x)-b x*W j x) atTop
      (𝓝 (∫ x, (∑ i, a i x*partialJet v [i] x)-b x*v x)) := by
  have hcont (f : Yau.Jets.Coord → ℝ) (hf : ContDiff ℝ ∞ f) :
      Continuous (fun x ↦ (∑ i, a i x*partialJet f [i] x)-b x*f x) :=
    (continuous_finsetSum _ (fun i _ ↦ (ha i).mul (partialJet_smooth f hf [i]).continuous)).sub
      (hb.mul hf.continuous)
  have hzero (f : Yau.Jets.Coord → ℝ) (x : Yau.Jets.Coord) (hx : x ∉ Q) :
      (∑ i, a i x*partialJet f [i] x)-b x*f x=0 := by
    simp [has _ x hx,hbs x hx]
  apply compact_uniform_integral_limit volume Q hQ _ _ (fun j ↦ hcont (W j) (hW j)) (hcont v hv)
    (fun j ↦ hzero (W j)) (hzero v)
  have hsum := finite_uniform_sum Finset.univ Q
    (fun i j x ↦ a i x*partialJet (W j) [i] x) (fun i x ↦ a i x*partialJet v [i] x)
    (fun i _ ↦ compact_uniform_mul Q hQ (fun _ ↦ a i) (fun j ↦ partialJet (W j) [i])
      (a i) (partialJet v [i]) (fun _ ↦ ha i) (fun j ↦ (partialJet_smooth (W j) (hW j) [i]).continuous)
      (ha i) (partialJet_smooth v hv [i]).continuous (by intro s hs; exact Eventually.of_forall (fun _ _ _ ↦ refl_mem_uniformity hs)) (hconv [i]))
  exact hsum.sub (compact_uniform_mul Q hQ (fun _ ↦ b) W b v (fun _ ↦ hb)
    (fun j ↦ (hW j).continuous) hb hv.continuous (by intro s hs; exact Eventually.of_forall (fun _ _ _ ↦ refl_mem_uniformity hs)) (hconv []))

end
end Yau.Analysis

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Charts_SphereEnergyFormLimit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Manifold Yau.Analysis Yau.Geometry Set Filter MeasureTheory
open scoped Topology ContDiff
noncomputable section

theorem sphereEnergyForm_limit (a b : Base → ℝ)
    (ha : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ a) (hb : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ b)
    {Q : Set Yau.Jets.Coord} (hQ : IsCompact Q)
    (haQ : tsupport a ⊆ seedSphereFromCoord '' Q) (hbQ : tsupport b ⊆ seedSphereFromCoord '' Q)
    (lam : ℝ) (W : ℕ → Base → ℝ) (v u : Base → ℝ)
    (hW : ∀ j, ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ (W j))
    (hv : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ v) (hu : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ u)
    (hconv : ∀ ds, TendstoUniformlyOn
      (fun j ↦ partialJet (W j ∘ sphereChartCoordMap seedPoint) ds)
      (partialJet (v ∘ sphereChartCoordMap seedPoint) ds) atTop Q) :
    Tendsto (fun j ↦ sphereEnergyForm a b lam (W j) u) atTop (𝓝 (sphereEnergyForm a b lam v u)) := by
  let ac : Fin 4 → Yau.Jets.Coord → ℝ := fun i x ↦
    roundCoordDensity x*a (sphereChartCoordMap seedPoint x)*roundCoordFactor x*
      Yau.coordPartial (u ∘ sphereChartCoordMap seedPoint) x i
  let bc : Yau.Jets.Coord → ℝ := fun x ↦
    roundCoordDensity x*lam*b (sphereChartCoordMap seedPoint x)*u (sphereChartCoordMap seedPoint x)
  have hac (i : Fin 4) : Continuous (ac i) :=
    (((roundCoordDensity_smooth.mul (spherePullback_smooth a ha seedPoint)).mul roundCoordFactor_smooth).mul
      (partialJet_smooth _ (spherePullback_smooth u hu seedPoint) [i])).continuous
  have hbc : Continuous bc :=
    (((roundCoordDensity_smooth.mul contDiff_const).mul (spherePullback_smooth b hb seedPoint)).mul
      (spherePullback_smooth u hu seedPoint)).continuous
  have hsupp (f : Base → ℝ) (hf : tsupport f ⊆ seedSphereFromCoord '' Q)
      (x : Yau.Jets.Coord) (hx : x ∉ Q) : f (sphereChartCoordMap seedPoint x)=0 := by
    apply image_eq_zero_of_notMem_tsupport
    intro hh
    obtain ⟨y,hy,he⟩ := hf hh
    have hxy : y=x := (Function.LeftInverse.injective seedSphereToCoord_from) he
    exact hx (hxy ▸ hy)
  have heq (f : Base → ℝ) (hf : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ f) :
      sphereEnergyForm a b lam f u = ∫ x,
        (∑ i, ac i x*partialJet (f ∘ sphereChartCoordMap seedPoint) [i] x)-
          bc x*(f ∘ sphereChartCoordMap seedPoint) x := by
    rw [sphereEnergyForm_chart a b lam f u hf hu seedPoint]
    apply integral_congr_ae
    exact Eventually.of_forall (fun x ↦ by
      simp only [ac,bc,partialJet,Yau.coordPartial,Function.comp_apply,mul_sub,Finset.mul_sum]
      congr 1
      · apply Finset.sum_congr rfl
        intro i _
        ring
      · ring)
  simp_rw [heq _ (hW _),heq v hv]
  exact compact_first_jet_functional_limit Q hQ ac bc hac hbc
    (fun i x hx ↦ by simp [ac,hsupp a haQ x hx])
    (fun x hx ↦ by simp [bc,hsupp b hbQ x hx])
    (fun j ↦ W j ∘ sphereChartCoordMap seedPoint) (v ∘ sphereChartCoordMap seedPoint)
    (fun j ↦ spherePullback_smooth (W j) (hW j) seedPoint) (spherePullback_smooth v hv seedPoint) hconv

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Charts_SphereWeightedNormalization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Manifold Set
open scoped ContDiff
noncomputable section

lemma sphereWeightedPairing_smul_right (rho u v : Base → ℝ) (t : ℝ) :
    sphereWeightedPairing rho u (t • v) = t*sphereWeightedPairing rho u v := by
  rw [sphereWeightedPairing_symm rho u (t • v),sphereWeightedPairing_smul_left,
    sphereWeightedPairing_symm rho v u]

theorem sphere_weighted_normalization (rho u : Base → ℝ)
    (hr : Continuous rho) (hp : ∀ p, 0 < rho p)
    (hu : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ u) (hne : u ≠ 0) :
    ∃ (t : ℝ) (v : Base → ℝ), 0 < t ∧ v = t • u ∧
      ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ v ∧ v ≠ 0 ∧ sphereWeightedPairing rho v v = 1 := by
  have hpos := sphereWeightedPairing_self_pos rho u hr hp hu.continuous hne
  let t := (Real.sqrt (sphereWeightedPairing rho u u))⁻¹
  have ht : 0 < t := inv_pos.mpr (Real.sqrt_pos.mpr hpos)
  refine ⟨t,t • u,ht,rfl,(contMDiff_const (c := t)).mul hu,?_,?_⟩
  · exact smul_ne_zero ht.ne' hne
  · rw [sphereWeightedPairing_smul_left,sphereWeightedPairing_smul_right]
    have hs := Real.sq_sqrt hpos.le
    dsimp [t]
    have hn : Real.sqrt (sphereWeightedPairing rho u u) ≠ 0 := (Real.sqrt_pos.mpr hpos).ne'
    field_simp
    nlinarith only [hs]

lemma sphere_weighted_orthogonal_remainder (rho u v : Base → ℝ)
    (hr : Continuous rho) (hp : ∀ p, 0 < rho p)
    (hu : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ u) (hv : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ v)
    (hne : u ≠ 0) :
    ∃ (c : ℝ) (w : Base → ℝ), w = v-c • u ∧
      ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ w ∧ sphereWeightedPairing rho w u = 0 ∧
      (w = 0 ↔ v = c • u) := by
  let c := sphereWeightedPairing rho v u / sphereWeightedPairing rho u u
  have hn := (sphereWeightedPairing_self_pos rho u hr hp hu.continuous hne).ne'
  refine ⟨c,v-c • u,rfl,hv.sub ((contMDiff_const (c := c)).mul hu),?_,sub_eq_zero⟩
  have he : v-c • u = v+(-c) • u := by simp only [neg_smul,sub_eq_add_neg]
  rw [he,sphereWeightedPairing_add_left rho v ((-c) • u) u hr hv.continuous
    (((contMDiff_const (c := -c)).mul hu).continuous) hu.continuous,sphereWeightedPairing_smul_left]
  dsimp [c]
  field_simp
  ring

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Charts_SphereSimplicitySequenceContradiction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Manifold Yau.Analysis Yau.Geometry Set Filter
open scoped Topology ContDiff
noncomputable section
attribute [local instance] clmTopology clmAdd clmModule
attribute [local instance] intrinsicRoundPerturbationLocalInst17 intrinsicRoundPerturbationLocalInst18

theorem sphere_affine_orthogonal_sequence_contradiction
    (A : IntrinsicTensor) (hA : IntrinsicTensorSmooth A)
    (hs : ∀ x v w, A x v w = A x w v) (hp : ∀ x v, v ≠ 0 → 0 < A x v v)
    (rho : Base → ℝ) (hr : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ rho) (hrp : ∀ x, 0 < rho x)
    (a b : Base → ℝ) (ha : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ a)
    (hb : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ b) (lam : ℝ)
    (t : ℕ → ℝ) (ht : Tendsto t atTop (𝓝 0))
    (w : ℕ → Base → ℝ) (hw : ∀ j, ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ (w j))
    (he : ∀ j p z, -intrinsicWeightedChartOperator
      (fun x ↦ A x+roundTensorPerturbation (fun y ↦ t j*a y) x)
      (fun x ↦ rho x+t j*b x) (w j) p z = lam*w j ((extChartAt (𝓡 4) p).symm z))
    (hn : ∀ j, sphereWeightedPairing (fun x ↦ rho x+t j*b x) (w j) (w j)=1)
    (u : Base → ℝ) (hu : Continuous u)
    (ho : ∀ j, sphereWeightedPairing (fun x ↦ rho x+t j*b x) (w j) u=0)
    {Q : Set Yau.Jets.Coord} (hQ : IsCompact Q)
    (haQ : tsupport a ⊆ seedSphereFromCoord '' Q) (hbQ : tsupport b ⊆ seedSphereFromCoord '' Q)
    (hkernel : ∀ f : Base → ℝ, ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ f →
      (∀ p z, -intrinsicWeightedChartOperator A rho f p z = lam*f ((extChartAt (𝓡 4) p).symm z)) →
      sphereEnergyForm a b lam f f=0 → ∃ c : ℝ, ∀ p, f p=c*u p)
    (hform : ∀ j (f : Base → ℝ), ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ f →
      (∀ p z, -intrinsicWeightedChartOperator A rho f p z = lam*f ((extChartAt (𝓡 4) p).symm z)) →
      sphereEnergyForm a b lam (w j) f=0) : False := by
  obtain ⟨v,hv,hvne,hev,hvn,hvo,nu,hnu,_,hpartial,_⟩ :=
    sphere_affine_normalized_limit A hA hs hp rho hr hrp a b ha hb lam t ht w hw he hn u hu ho
  have hlim := sphereEnergyForm_limit a b ha hb hQ haQ hbQ lam (fun j ↦ w (nu j)) v v
    (fun j ↦ hw (nu j)) hv hv (fun ds ↦ hpartial seedPoint ds Q hQ)
  have hzero : sphereEnergyForm a b lam v v=0 := by
    apply tendsto_nhds_unique hlim
    simpa only [hform _ v hv hev] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ (0:ℝ)) atTop (𝓝 0))
  obtain ⟨c,hc⟩ := hkernel v hv hev hzero
  have heq : v=c • u := funext hc
  have hnormzero : sphereWeightedPairing rho v v=0 := by
    calc
      _ = sphereWeightedPairing rho v (c • u) := congrArg (sphereWeightedPairing rho v) heq
      _ = c*sphereWeightedPairing rho v u := sphereWeightedPairing_smul_right rho v u c
      _ = 0 := by rw [hvo,mul_zero]
  linarith

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

theorem sphere_normalized_orthogonal_eigenfunction (A : IntrinsicTensor) (hA : IntrinsicTensorSmooth A)
    (hs : ∀ x alpha beta, A x alpha beta = A x beta alpha)
    (hp : ∀ x alpha, alpha ≠ 0 → 0 < A x alpha alpha)
    (rho : Base → ℝ) (hr : Continuous rho) (hrp : ∀ x, 0 < rho x)
    (u v : Base → ℝ) (hu : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ u)
    (hv : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ v) (hune : u ≠ 0) (lam : ℝ)
    (heu : ∀ p z, -intrinsicWeightedChartOperator A rho u p z =
      lam*u ((extChartAt (𝓡 4) p).symm z))
    (hev : ∀ p z, -intrinsicWeightedChartOperator A rho v p z =
      lam*v ((extChartAt (𝓡 4) p).symm z))
    (hnot : ¬ ∃ c : ℝ, v = c • u) :
    ∃ w : Base → ℝ, ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ w ∧ w ≠ 0 ∧
      (∀ p z, -intrinsicWeightedChartOperator A rho w p z =
        lam*w ((extChartAt (𝓡 4) p).symm z)) ∧
      sphereWeightedPairing rho w w = 1 ∧ sphereWeightedPairing rho w u = 0 := by
  obtain ⟨c,q,hq,hqs,hqo,hqzero⟩ := sphere_weighted_orthogonal_remainder rho u v hr hrp hu hv hune
  have hqne : q ≠ 0 := fun hz ↦ hnot ⟨c,hqzero.mp hz⟩
  have hqeq : q = fun x ↦ (-c)*u x+v x := by
    rw [hq]
    funext x
    simp only [Pi.sub_apply,Pi.smul_apply,smul_eq_mul]
    ring
  have hqe : ∀ p z, -intrinsicWeightedChartOperator A rho q p z =
      lam*q ((extChartAt (𝓡 4) p).symm z) := by
    rw [hqeq]
    exact intrinsic_eigenfunction_linear_combination A hA hs hp rho u v hu hv lam heu hev (-c)
  obtain ⟨s,w,_,hw,hws,hwne,hwn⟩ := sphere_weighted_normalization rho q hr hrp hqs hqne
  refine ⟨w,hws,hwne,?_,hwn,?_⟩
  · rw [hw]
    exact intrinsic_eigenfunction_smul A hA hs hp rho q hqs lam s hqe
  · rw [hw,sphereWeightedPairing_smul_left,hqo,mul_zero]

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Charts_SphereAffineSimplicityCriterion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Manifold Yau.Geometry Set Filter
open scoped ContDiff Topology
noncomputable section
attribute [local instance] clmTopology clmAdd clmModule
attribute [local instance] intrinsicRoundPerturbationLocalInst17 intrinsicRoundPerturbationLocalInst18

theorem sphere_affine_kernel_implies_simplicity_oai
    (A : IntrinsicTensor) (hA : IntrinsicTensorSmooth A)
    (hs : ∀ x alpha beta, A x alpha beta = A x beta alpha)
    (hp : ∀ x alpha, alpha ≠ 0 → 0 < A x alpha alpha)
    (rho : Base → ℝ) (hr : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ rho) (hrp : ∀ x, 0 < rho x)
    (a b : Base → ℝ) (ha : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ a)
    (hb : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ b) (lam : ℝ)
    (u : Base → ℝ) (hu : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ u) (hune : u ≠ 0)
    {Q : Set Yau.Jets.Coord} (hQ : IsCompact Q)
    (haQ : tsupport a ⊆ seedSphereFromCoord '' Q) (hbQ : tsupport b ⊆ seedSphereFromCoord '' Q)
    (hkernel : ∀ f : Base → ℝ, ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ f →
      (∀ p z, -intrinsicWeightedChartOperator A rho f p z = lam*f ((extChartAt (𝓡 4) p).symm z)) →
      sphereEnergyForm a b lam f f=0 → ∃ c : ℝ, ∀ p, f p=c*u p)
    (dpre : ℝ) (hdpre : 0 < dpre)
    (hpres : ∀ t : ℝ, |t| < dpre → ∀ p z, -intrinsicWeightedChartOperator
      (fun x ↦ A x+roundTensorPerturbation (fun y ↦ t*a y) x)
      (fun x ↦ rho x+t*b x) u p z = lam*u ((extChartAt (𝓡 4) p).symm z)) :
    ∃ delta > 0, ∀ t : ℝ, |t| < delta → t ≠ 0 →
      ∀ v : Base → ℝ, ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ v →
      (∀ p z, -intrinsicWeightedChartOperator
        (fun x ↦ A x+roundTensorPerturbation (fun y ↦ t*a y) x)
        (fun x ↦ rho x+t*b x) v p z = lam*v ((extChartAt (𝓡 4) p).symm z)) →
      ∃ c : ℝ, v = c • u := by
  classical
  obtain ⟨ds,hds,hsmall⟩ := small_round_perturbation_in_finite_atlas A hA hs hp rho hr hrp
    a b ha hb ∅ 0 (by norm_num : (0:ℝ)<1)
  by_contra h
  push Not at h
  have hbad (j : ℕ) := h (min (min dpre ds) (1/((j:ℝ)+1)))
    (lt_min (lt_min hdpre hds) (by positivity))
  choose t ht htn v hv hev hvnot using hbad
  have hts (j : ℕ) : |t j| < ds := (ht j).trans_le ((min_le_left _ _).trans (min_le_right _ _))
  have htp (j : ℕ) : |t j| < dpre := (ht j).trans_le ((min_le_left _ _).trans (min_le_left _ _))
  have htlim : Tendsto t atTop (𝓝 0) := by
    have habs : Tendsto (fun j ↦ |t j|) atTop (𝓝 0) := squeeze_zero
      (fun j ↦ abs_nonneg (t j)) (fun j ↦ ((ht j).trans_le (min_le_right _ _)).le)
      tendsto_one_div_add_atTop_nhds_zero_nat
    exact tendsto_zero_iff_norm_tendsto_zero.mpr (by simpa only [Real.norm_eq_abs] using habs)
  have hnorm (j : ℕ) := sphere_normalized_orthogonal_eigenfunction
    (fun x ↦ A x+roundTensorPerturbation (fun y ↦ t j*a y) x)
    (hsmall (t j) (hts j)).1 (hsmall (t j) (hts j)).2.1 (hsmall (t j) (hts j)).2.2.1
    (fun x ↦ rho x+t j*b x) (hsmall (t j) (hts j)).2.2.2.1.continuous
    (hsmall (t j) (hts j)).2.2.2.2.1 u (v j) hu (hv j) hune lam
    (hpres (t j) (htp j)) (hev j) (by rintro ⟨c,hc⟩; exact hvnot j c hc)
  choose w hw _ hew hwn hwo using hnorm
  exact sphere_affine_orthogonal_sequence_contradiction A hA hs hp rho hr hrp a b ha hb lam
    t htlim w hw hew hwn u hu.continuous hwo hQ haQ hbQ hkernel
    (fun j f hf hef ↦ sphere_affine_form_annihilates A hA hs hp rho hr hrp a b hb lam (t j)
      (htn j) (hsmall (t j) (hts j)).1 (hsmall (t j) (hts j)).2.1
      (hsmall (t j) (hts j)).2.2.1 (hsmall (t j) (hts j)).2.2.2.2.1
      (w j) f (hw j) hf (hew j) hef)

end
end Yau.Target

end OAI
end

theorem solution : type_of% @OAI.Yau.Target.sphere_affine_kernel_implies_simplicity_oai := @OAI.Yau.Target.sphere_affine_kernel_implies_simplicity_oai
