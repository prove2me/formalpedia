-- Prove2me | solution 1 for OAI.Yau.Target.exists_sphere_simplicity_kernel_form
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T00:30:43.490369+00:00
-- url     : https://prove2.me/submissions/0b451c05-3335-467c-ad98-3942d7ef95c5

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
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.Harmonic.Basic
import Mathlib.Analysis.InnerProductSpace.Laplacian
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Operator.ContinuousLinearMap
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Data.Finsupp.Weight
import Mathlib.Data.Int.Interval
import Mathlib.Data.List.FinRange
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
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Measure.Hausdorff
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
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
import Mathlib.Topology.Compactness.LocallyCompact
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.UniformSpace.HeineCantor
import Definitions.Def_YauCounterexample
import Definitions.Def_OAIQ237Ny004
import Theorems.Thm_OAI_Yau_Geometry_real_global_unique_continuation

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
-- module Solutions.OAIQ237_NY.NodalSets_Charts_SeedChartScalarExtension
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

lemma seedSphereFromCoord_source (x : Yau.Jets.Coord) :
    seedSphereFromCoord x ∈ (extChartAt (𝓡 4) seedPoint).source :=
  (extChartAt (𝓡 4) seedPoint).map_target (by rw [centeredSphereChart_target]; trivial)

lemma seedSphereFromCoord_to {p : Base} (hp : p ∈ (extChartAt (𝓡 4) seedPoint).source) :
    seedSphereFromCoord (seedSphereToCoord p) = p := by
  unfold seedSphereToCoord seedSphereFromCoord
  rw [seedCoordEquiv.apply_symm_apply,(extChartAt (𝓡 4) seedPoint).left_inv hp]

theorem seed_chart_scalar_extension (v : Yau.Jets.Coord → ℝ) (hv : ContDiff ℝ ∞ v)
    (hc : HasCompactSupport v) :
    ∃ F : Base → ℝ, ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ F ∧
      tsupport F ⊆ seedSphereFromCoord '' tsupport v ∧
      ∀ x, F (seedSphereFromCoord x) = v x := by
  let K := seedSphereFromCoord '' tsupport v
  have hK : IsCompact K := hc.image seedSphereFromCoord_continuous
  have hKU : K ⊆ (extChartAt (𝓡 4) seedPoint).source := by
    rintro p ⟨x,hx,rfl⟩
    exact seedSphereFromCoord_source x
  have hU : IsOpen (extChartAt (𝓡 4) seedPoint).source := isOpen_extChartAt_source seedPoint
  obtain ⟨b,hb,hbc,hbs,hbr,hb1⟩ := manifold_compact_smooth_cutoff (I := 𝓡 4) hK hU hKU
  let F : Base → ℝ := fun p ↦ b p*v (seedSphereToCoord p)
  have hF : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ F := by
    intro p
    by_cases hp : p ∈ tsupport b
    · have hcoord : ContMDiffAt (𝓡 4) 𝓘(ℝ,Yau.Jets.Coord) ∞ seedSphereToCoord p :=
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
    have hvne : v (seedSphereToCoord p) ≠ 0 := fun h ↦ hp (by simp [F,h])
    exact ⟨seedSphereToCoord p,subset_closure hvne,
      seedSphereFromCoord_to (hbs (subset_closure hbne))⟩
  refine ⟨F,hF,hs,?_⟩
  intro x
  dsimp [F]
  rw [seedSphereToCoord_from]
  by_cases hx : v x = 0
  · simp [hx]
  · have h := (hb1 (seedSphereFromCoord x) ⟨x,subset_closure hx,rfl⟩).eq_of_nhds
    rw [h,one_mul]

end
end Yau.Target

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
-- module Solutions.OAIQ237_NY.NodalSets_Coefficients_CorrectionAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau

theorem simplicity_preserves {u lam z s d : ℝ} (hlam : lam ≠ 0) :
    (u ^ 2 * d + 2 * z * u * s) +
      lam * (-lam⁻¹ * (u * d + 2 * z * s)) * u = 0 := by
  field_simp
  ring

end Yau

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

theorem weightedDiv_zero_off_support (gamma f : Coord n → ℝ)
    (V : Coord n → Coord n) {x : Coord n} (hx : x ∉ tsupport f) :
    weightedDiv gamma (fun y i ↦ f y * V y i) x = 0 := by
  have he : f =ᶠ[nhds x] 0 := notMem_tsupport_iff_eventuallyEq.mp hx
  have hd (i : Fin n) :
      fderiv ℝ (fun y ↦ gamma y * (f y * V y i)) x = 0 := by
    have heq : (fun y ↦ gamma y * (f y * V y i)) =ᶠ[nhds x] (fun _ ↦ 0) := by
      filter_upwards [he] with y hy
      simp [hy]
    rw [heq.fderiv_eq]
    simp
  simp [weightedDiv, coordDiv, coordPartial, hd]

end
end Yau

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

lemma roundCoordFactor_ge_one (x : Yau.Jets.Coord) : 1 ≤ roundCoordFactor x := by
  unfold roundCoordFactor
  nlinarith [sq_nonneg (‖seedCoordEquiv x‖)]

lemma roundCoordFactor_smooth : ContDiff ℝ ∞ roundCoordFactor := by
  unfold roundCoordFactor
  exact ((((contDiff_norm_sq ℝ).comp seedCoordEquiv.contDiff).add contDiff_const).div_const 4).pow 2

lemma roundCoordGradient_smooth (u : Yau.Jets.Coord → ℝ) (hu : ContDiff ℝ ∞ u) :
    ContDiff ℝ ∞ (roundCoordGradient u) := by
  apply contDiff_pi.mpr
  intro i
  exact roundCoordFactor_smooth.mul ((hu.fderiv_right (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).clm_apply contDiff_const)

lemma roundCoordGradient_pairing (u : Yau.Jets.Coord → ℝ) (x : Yau.Jets.Coord) :
    Yau.pairing u (roundCoordGradient u) x =
      roundCoordFactor x * (sourceEuclideanNorm (fun i ↦ fderiv ℝ u x (Pi.single i 1)))^2 := by
  rw [sourceEuclideanNorm,Real.sq_sqrt (by positivity),Finset.mul_sum]
  unfold Yau.pairing Yau.coordPartial
  apply Finset.sum_congr rfl
  intro i _
  dsimp [roundCoordGradient]
  ring

end
end Yau.Target

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

namespace Yau.Target
open Set
open scoped ContDiff
variable {d : ℕ}

lemma pairing_square_scaled (u zeta : Yau.Coord d → ℝ)
    (V : Yau.Coord d → Yau.Coord d) (x : Yau.Coord d)
    (hu : DifferentiableAt ℝ u x) :
    Yau.pairing (fun y ↦ u y^2) (fun y i ↦ zeta y*V y i) x =
      2*zeta x*u x*Yau.pairing u V x := by
  unfold Yau.pairing Yau.coordPartial
  simp_rw [pow_two,fderiv_fun_mul hu hu]
  simp only [add_apply,smul_apply,smul_eq_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem simplicity_coordinate_cancellation
    (gamma u zeta : Yau.Coord d → ℝ) (V : Yau.Coord d → Yau.Coord d)
    (lam : ℝ) (hlam : lam ≠ 0) (x : Yau.Coord d)
    (hg : DifferentiableAt ℝ gamma x) (hgn : gamma x ≠ 0)
    (hu : DifferentiableAt ℝ u x) (hz : DifferentiableAt ℝ zeta x)
    (hV : ∀ i, DifferentiableAt ℝ (fun y ↦ V y i) x) :
    Yau.weightedDiv gamma (fun y i ↦ (zeta y*u y^2)*V y i) x +
      lam*simplicityDensityPerturbation gamma u zeta V lam x*u x = 0 := by
  have he : (fun y i ↦ (zeta y*u y^2)*V y i) =
      (fun y i ↦ u y^2*(zeta y*V y i)) := by
    funext y i
    ring
  have hu2 : DifferentiableAt ℝ (fun y ↦ u y^2) x := by
    convert hu.mul hu using 1
    all_goals try with_reducible_and_instances rfl
    first | rfl | (funext y; exact pow_two (u y))
  have hd := Yau.weightedDiv_mul (u := fun y ↦ u y^2) (V := fun y i ↦ zeta y*V y i)
    hg hgn hu2 (fun i ↦ hz.mul (hV i))
  rw [he,hd,pairing_square_scaled u zeta V x hu]
  exact Yau.simplicity_preserves hlam

lemma simplicityDensityPerturbation_smooth
    (gamma u zeta : Yau.Coord d → ℝ) (V : Yau.Coord d → Yau.Coord d) (lam : ℝ)
    (hg : ContDiff ℝ ∞ gamma) (hgn : ∀ x, gamma x ≠ 0)
    (hu : ContDiff ℝ ∞ u) (hz : ContDiff ℝ ∞ zeta)
    (hV : ContDiff ℝ ∞ V) :
    ContDiff ℝ ∞ (simplicityDensityPerturbation gamma u zeta V lam) := by
  have hv (i : Fin d) := (contDiff_pi.mp hV) i
  exact contDiff_const.mul ((hu.mul
    (Yau.weightedDiv_smooth hg hgn (fun i ↦ hz.mul (hv i)))).add
    ((contDiff_const.mul hz).mul (Yau.pairing_smooth hu hv)))

lemma simplicityDensityPerturbation_tsupport_subset
    (gamma u zeta : Yau.Coord d → ℝ) (V : Yau.Coord d → Yau.Coord d) (lam : ℝ) :
    tsupport (simplicityDensityPerturbation gamma u zeta V lam) ⊆ tsupport zeta := by
  apply closure_minimal _ (isClosed_tsupport zeta)
  intro x hx
  by_contra h
  have hz := image_eq_zero_of_notMem_tsupport h
  have hd := Yau.weightedDiv_zero_off_support gamma zeta V h
  exact hx (by simp [simplicityDensityPerturbation,hz,hd])

end Yau.Target

end

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_SimplicityRoundCoordinatePerturbation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Yau.Geometry Yau.Jets Set
open scoped ContDiff
noncomputable section

theorem round_simplicity_coordinate_perturbation
    (u zeta : Yau.Jets.Coord → ℝ) (hu : ContDiff ℝ ∞ u) (hz : ContDiff ℝ ∞ zeta)
    (lam : ℝ) (hlam : lam ≠ 0) :
    let alpha := fun x ↦ zeta x*u x^2
    let beta := simplicityDensityPerturbation roundCoordDensity u zeta (roundCoordGradient u) lam
    ContDiff ℝ ∞ alpha ∧ ContDiff ℝ ∞ beta ∧
    tsupport alpha ⊆ tsupport zeta ∧ tsupport beta ⊆ tsupport zeta ∧
    (∀ x, beta x = -lam⁻¹ *
      (u x * Yau.weightedDiv roundCoordDensity (fun y i ↦ zeta y*roundCoordGradient u y i) x +
        2*zeta x*roundCoordFactor x*
          (sourceEuclideanNorm (fun i ↦ fderiv ℝ u x (Pi.single i 1)))^2)) ∧
    ∀ x, Yau.weightedDiv roundCoordDensity (fun y i ↦ alpha y*roundCoordGradient u y i) x +
      lam*beta x*u x = 0 := by
  intro alpha beta
  have hV := roundCoordGradient_smooth u hu
  refine ⟨hz.mul (hu.pow 2),simplicityDensityPerturbation_smooth _ _ _ _ _
    roundCoordDensity_smooth (fun x ↦ (roundCoordDensity_pos x).ne') hu hz hV,
    ?_,simplicityDensityPerturbation_tsupport_subset _ _ _ _ _,?_,?_⟩
  · exact tsupport_mul_subset_left
  · intro x
    dsimp [beta,simplicityDensityPerturbation]
    rw [roundCoordGradient_pairing]
    ring
  · intro x
    exact simplicity_coordinate_cancellation _ _ _ _ _ hlam x
      (roundCoordDensity_smooth.differentiable (by simp) x) (roundCoordDensity_pos x).ne'
      (hu.differentiable (by simp) x) (hz.differentiable (by simp) x)
      (fun i ↦ ((contDiff_pi.mp hV) i).differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) x)

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Charts_SimplicityEnergyDensity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Yau.Geometry Yau.Jets Set
open scoped ContDiff
noncomputable section

lemma roundSimplicitySquare_nonneg (u v : Yau.Jets.Coord → ℝ) (x : Yau.Jets.Coord) :
    0 ≤ roundSimplicitySquare u v x :=
  mul_nonneg ((show (0:ℝ) ≤ 1 by norm_num).trans (roundCoordFactor_ge_one x))
    (Finset.sum_nonneg (fun i _ ↦ sq_nonneg _))

lemma roundSimplicitySquare_smooth (u v : Yau.Jets.Coord → ℝ)
    (hu : ContDiff ℝ ∞ u) (hv : ContDiff ℝ ∞ v) : ContDiff ℝ ∞ (roundSimplicitySquare u v) := by
  apply roundCoordFactor_smooth.mul
  apply ContDiff.sum
  intro i _
  exact ((hu.mul ((hv.fderiv_right (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).clm_apply contDiff_const)).sub
    (hv.mul ((hu.fderiv_right (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).clm_apply contDiff_const))).pow 2

lemma roundSimplicitySquare_expand (u v : Yau.Jets.Coord → ℝ) (x : Yau.Jets.Coord) :
    roundSimplicitySquare u v x =
      u x^2*Yau.pairing v (roundCoordGradient v) x +
      v x^2*Yau.pairing u (roundCoordGradient u) x -
      2*u x*v x*Yau.pairing v (roundCoordGradient u) x := by
  unfold roundSimplicitySquare Yau.pairing roundCoordGradient Yau.coordPartial
  simp only [Finset.mul_sum]
  rw [← Finset.sum_add_distrib,← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

lemma round_pairing_mul_square (u v zeta : Yau.Jets.Coord → ℝ) (x : Yau.Jets.Coord)
    (hu : DifferentiableAt ℝ u x) (hv : DifferentiableAt ℝ v x) :
    Yau.pairing (fun y ↦ u y*v y^2) (fun y i ↦ zeta y*roundCoordGradient u y i) x =
      zeta x*(v x^2*Yau.pairing u (roundCoordGradient u) x +
        2*u x*v x*Yau.pairing v (roundCoordGradient u) x) := by
  have hd (i : Fin 4) : Yau.coordPartial (fun y ↦ u y*v y^2) x i =
      Yau.coordPartial u x i*v x^2+2*u x*v x*Yau.coordPartial v x i := by
    unfold Yau.coordPartial
    simp only [pow_two]
    have hv2 : DifferentiableAt ℝ (fun y ↦ v y*v y) x := hv.mul hv
    rw [fderiv_fun_mul hu hv2,fderiv_fun_mul hv hv]
    simp only [add_apply,smul_apply,smul_eq_mul]
    ring
  unfold Yau.pairing
  simp only [hd,Finset.mul_sum,mul_add]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem round_simplicity_energy_density (u v zeta : Yau.Jets.Coord → ℝ)
    (hu : ContDiff ℝ ∞ u) (hv : ContDiff ℝ ∞ v) (hz : ContDiff ℝ ∞ zeta)
    (lam : ℝ) (hlam : lam ≠ 0) (x : Yau.Jets.Coord) :
    zeta x*u x^2*Yau.pairing v (roundCoordGradient v) x -
      lam*simplicityDensityPerturbation roundCoordDensity u zeta (roundCoordGradient u) lam x*v x^2 =
      zeta x*roundSimplicitySquare u v x +
        Yau.weightedDiv roundCoordDensity
          (fun y i ↦ (u y*v y^2)*(zeta y*roundCoordGradient u y i)) x := by
  have hV := roundCoordGradient_smooth u hu
  have hdiv := Yau.weightedDiv_mul (gamma := roundCoordDensity) (u := fun y ↦ u y*v y^2)
    (V := fun y i ↦ zeta y*roundCoordGradient u y i) (x := x)
    (roundCoordDensity_smooth.differentiable (by simp) x) (roundCoordDensity_pos x).ne'
    ((hu.mul (hv.pow 2)).differentiable (by simp) x)
    (fun i ↦ (hz.mul ((contDiff_pi.mp hV) i)).differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) x)
  rw [hdiv,round_pairing_mul_square u v zeta x
    (hu.differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) x) (hv.differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) x),roundSimplicitySquare_expand]
  unfold simplicityDensityPerturbation
  field_simp
  ring

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_IntrinsicRoundPerturbation
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
lemma roundTensorPerturbation_apply (alpha : Base → ℝ) (x : Base) (v w : SphereCotangent x) :
    roundTensorPerturbation alpha x v w = alpha x * roundCotangentTensor x v w := rfl

attribute [local instance] OAI.Yau.Target.intrinsicRoundPerturbationLocalInst4
attribute [local instance] OAI.Yau.Target.intrinsicRoundPerturbationLocalInst5
attribute [local instance] OAI.Yau.Target.intrinsicRoundPerturbationLocalInst6
attribute [local instance] OAI.Yau.Target.intrinsicRoundPerturbationLocalInst7
attribute [local instance] OAI.Yau.Target.intrinsicRoundPerturbationLocalInst8
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
-- module Solutions.OAIQ237_NY.NodalSets_Charts_SphereReferenceMeasure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Manifold Set MeasureTheory
open scoped ENNReal
noncomputable section

attribute [local instance] OAI.Yau.Target.sphereReferenceMeasureLocal1
attribute [local instance] OAI.Yau.Target.sphereReferenceMeasureLocal2
lemma sphereReferenceMeasure_integral (f : Base → ℝ) :
    (∫ p, f p ∂sphereReferenceMeasure) =
      ∫ x, roundCoordDensity x*f (seedSphereFromCoord x) := by
  rw [sphereReferenceMeasure,seedSphereFromCoord_measurableEmbedding.integral_map]
  rw [integral_withDensity_eq_integral_toReal_smul
    (roundCoordDensity_smooth.continuous.measurable.ennreal_ofReal)
    (Filter.Eventually.of_forall (fun _ ↦ ENNReal.ofReal_lt_top))]
  simp only [ENNReal.toReal_ofReal (roundCoordDensity_pos _).le,smul_eq_mul]

lemma sphereReferenceMeasure_integrable (f : Base → ℝ) :
    Integrable f sphereReferenceMeasure ↔
      Integrable (fun x ↦ roundCoordDensity x*f (seedSphereFromCoord x)) := by
  rw [sphereReferenceMeasure,seedSphereFromCoord_measurableEmbedding.integrable_map_iff,
    integrable_withDensity_iff_integrable_smul'
      (roundCoordDensity_smooth.continuous.measurable.ennreal_ofReal)
      (Filter.Eventually.of_forall (fun _ ↦ ENNReal.ofReal_lt_top))]
  simp only [ENNReal.toReal_ofReal (roundCoordDensity_pos _).le,smul_eq_mul,Function.comp_apply]

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

local instance sphereEnergyFormLocal1_r192374_1 : MeasurableSpace Base := borel Base
local instance sphereEnergyFormLocal2_r192374_1 : BorelSpace Base := ⟨rfl⟩
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

lemma sphereEnergyForm_symm (a b : Base → ℝ) (lam : ℝ) (v w : Base → ℝ) :
    sphereEnergyForm a b lam v w = sphereEnergyForm a b lam w v := by
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro p
  simp only [sphereEnergyDensity,roundTensorPerturbation_apply]
  rw [roundCotangentTensor_symm p (sphereDifferential v p) (sphereDifferential w p)]
  ring

lemma spherePullback_compact_support (a : Base → ℝ) {Q : Set Yau.Jets.Coord}
    (hQ : IsCompact Q) (ha : tsupport a ⊆ seedSphereFromCoord '' Q) :
    HasCompactSupport (a ∘ seedSphereFromCoord) := by
  apply hQ.of_isClosed_subset isClosed_closure
  apply closure_minimal _ hQ.isClosed
  intro x hx
  obtain ⟨y,hy,he⟩ := ha (subset_closure hx)
  have hxy := seedSphereFromCoord_measurableEmbedding.injective he
  exact hxy ▸ hy

lemma sphereEnergyDensity_integrable (a b : Base → ℝ)
    (ha : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ a) (hb : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ b)
    {Q : Set Yau.Jets.Coord} (hQ : IsCompact Q)
    (haQ : tsupport a ⊆ seedSphereFromCoord '' Q) (hbQ : tsupport b ⊆ seedSphereFromCoord '' Q)
    (lam : ℝ) (v w : Base → ℝ)
    (hv : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ v) (hw : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ w) :
    Integrable (sphereEnergyDensity a b lam v w) sphereReferenceMeasure := by
  rw [sphereReferenceMeasure_integrable_chart seedPoint]
  simp only [roundChartDensity_coord_eq,sphereEnergyDensity_chart a b lam v w hv hw]
  have ha' := spherePullback_smooth a ha seedPoint
  have hb' := spherePullback_smooth b hb seedPoint
  have hv' := spherePullback_smooth v hv seedPoint
  have hw' := spherePullback_smooth w hw seedPoint
  have hs : ContDiff ℝ ∞ (fun x ↦ ∑ i, Yau.coordPartial (v ∘ sphereChartCoordMap seedPoint) x i *
      Yau.coordPartial (w ∘ sphereChartCoordMap seedPoint) x i) := by
    apply ContDiff.sum
    intro i _
    exact ((hv'.fderiv_right (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).clm_apply contDiff_const).mul
      ((hw'.fderiv_right (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).clm_apply contDiff_const)
  have hsmooth := roundCoordDensity_smooth.mul
    (((ha'.mul roundCoordFactor_smooth).mul hs).sub ((((contDiff_const (c := lam)).mul hb').mul hv').mul hw'))
  apply hsmooth.continuous.integrable_of_hasCompactSupport
  have hac : HasCompactSupport (fun x ↦ a (sphereChartCoordMap seedPoint x)) :=
    spherePullback_compact_support a hQ haQ
  have hbc : HasCompactSupport (fun x ↦ b (sphereChartCoordMap seedPoint x)) :=
    spherePullback_compact_support b hQ hbQ
  exact ((hac.mul_right.mul_right).sub (hbc.mul_left.mul_right.mul_right)).mul_left

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Charts_SphereEnergyBilinear
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Manifold Yau.Geometry Yau.Jets Set MeasureTheory
open scoped ContDiff
noncomputable section
attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace normedSpaceTangentSpaceVectorSpace

local instance sphereEnergyBilinearLocal1_r192374_1 : MeasurableSpace Base := borel Base
local instance sphereEnergyBilinearLocal2_r192374_1 : BorelSpace Base := ⟨rfl⟩
lemma sphereEnergyDensity_add_left (a b : Base → ℝ) (lam : ℝ) (u v w : Base → ℝ)
    (hu : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ u) (hv : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ v) (p : Base) :
    sphereEnergyDensity a b lam (u+v) w p =
      sphereEnergyDensity a b lam u w p+sphereEnergyDensity a b lam v w p := by
  simp only [sphereEnergyDensity,sphereDifferential_add u v hu hv, map_add,
    _root_.add_apply,Pi.add_apply]
  ring

lemma sphereEnergyForm_add_left (a b : Base → ℝ)
    (ha : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ a) (hb : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ b)
    {Q : Set Yau.Jets.Coord} (hQ : IsCompact Q)
    (haQ : tsupport a ⊆ seedSphereFromCoord '' Q) (hbQ : tsupport b ⊆ seedSphereFromCoord '' Q)
    (lam : ℝ) (u v w : Base → ℝ)
    (hu : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ u) (hv : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ v)
    (hw : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ w) :
    sphereEnergyForm a b lam (u+v) w = sphereEnergyForm a b lam u w+sphereEnergyForm a b lam v w := by
  simp only [sphereEnergyForm,sphereEnergyDensity_add_left a b lam u v w hu hv]
  exact integral_add (sphereEnergyDensity_integrable a b ha hb hQ haQ hbQ lam u w hu hw)
    (sphereEnergyDensity_integrable a b ha hb hQ haQ hbQ lam v w hv hw)

lemma sphereEnergyForm_smul_left (a b : Base → ℝ) (lam : ℝ) (u v : Base → ℝ)
    (hu : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ u) (t : ℝ) :
    sphereEnergyForm a b lam (t • u) v = t*sphereEnergyForm a b lam u v := by
  have he (p : Base) : sphereEnergyDensity a b lam (t • u) v p = t*sphereEnergyDensity a b lam u v p := by
    simp only [sphereEnergyDensity,sphereDifferential_smul u hu, map_smul,
      _root_.smul_apply,Pi.smul_apply,smul_eq_mul]
    ring
  simp only [sphereEnergyForm,he]
  exact integral_const_mul t _

lemma sphereEnergyForm_add_right (a b : Base → ℝ)
    (ha : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ a) (hb : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ b)
    {Q : Set Yau.Jets.Coord} (hQ : IsCompact Q)
    (haQ : tsupport a ⊆ seedSphereFromCoord '' Q) (hbQ : tsupport b ⊆ seedSphereFromCoord '' Q)
    (lam : ℝ) (u v w : Base → ℝ)
    (hu : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ u) (hv : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ v)
    (hw : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ w) :
    sphereEnergyForm a b lam u (v+w) = sphereEnergyForm a b lam u v+sphereEnergyForm a b lam u w := by
  rw [sphereEnergyForm_symm a b lam u (v+w),sphereEnergyForm_add_left a b ha hb hQ haQ hbQ lam v w u hv hw hu,
    sphereEnergyForm_symm a b lam v u,sphereEnergyForm_symm a b lam w u]

lemma sphereEnergyForm_smul_right (a b : Base → ℝ) (lam : ℝ) (u v : Base → ℝ)
    (hv : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ v) (t : ℝ) :
    sphereEnergyForm a b lam u (t • v) = t*sphereEnergyForm a b lam u v := by
  rw [sphereEnergyForm_symm a b lam u (t • v),sphereEnergyForm_smul_left a b lam v u hv t,
    sphereEnergyForm_symm a b lam v u]

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Charts_SphereSimplicitySquare
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Manifold Yau.Geometry Yau.Jets
open scoped ContDiff
noncomputable section
attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace normedSpaceTangentSpaceVectorSpace

lemma roundCotangentTensor_cross_expand (u v : Base → ℝ) (p : Base) :
    roundCotangentTensor p (sphereCrossDifferential u v p) (sphereCrossDifferential u v p) =
      u p^2*roundCotangentTensor p (sphereDifferential v p) (sphereDifferential v p) +
      v p^2*roundCotangentTensor p (sphereDifferential u p) (sphereDifferential u p) -
      2*u p*v p*roundCotangentTensor p (sphereDifferential v p) (sphereDifferential u p) := by
  simp only [sphereCrossDifferential,map_sub,map_smul,sub_apply,
    smul_apply,smul_eq_mul]
  rw [roundCotangentTensor_symm p (sphereDifferential u p) (sphereDifferential v p)]
  ring

lemma sphereCrossDifferential_square_chart (u v : Base → ℝ)
    (hu : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ u) (hv : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ v)
    (p : Base) (x : Yau.Jets.Coord) :
    roundCotangentTensor (sphereChartCoordMap p x)
      (sphereCrossDifferential u v (sphereChartCoordMap p x))
      (sphereCrossDifferential u v (sphereChartCoordMap p x)) =
      roundSimplicitySquare (u ∘ sphereChartCoordMap p) (v ∘ sphereChartCoordMap p) x := by
  rw [roundCotangentTensor_cross_expand,
    roundCotangentTensor_differential_pair v v hv hv,
    roundCotangentTensor_differential_pair u u hu hu,
    roundCotangentTensor_differential_pair v u hv hu]
  unfold roundSimplicitySquare
  simp only [Function.comp_apply,Finset.mul_sum]
  rw [← Finset.sum_add_distrib,← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

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
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_SimplicityCoordinateEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Yau.Geometry Yau.Jets Set MeasureTheory
open scoped ContDiff
noncomputable section

lemma round_simplicity_square_integrable (u v zeta : Yau.Jets.Coord → ℝ)
    (hu : ContDiff ℝ ∞ u) (hv : ContDiff ℝ ∞ v) (hz : ContDiff ℝ ∞ zeta)
    (hc : HasCompactSupport zeta) :
    Integrable (fun x ↦ roundCoordDensity x*zeta x*roundSimplicitySquare u v x) := by
  have hs := ((roundCoordDensity_smooth.mul hz).mul (roundSimplicitySquare_smooth u v hu hv)).continuous
  have hcomp : HasCompactSupport (fun x ↦ roundCoordDensity x*zeta x) := hc.mul_left
  exact hs.integrable_of_hasCompactSupport hcomp.mul_right

theorem round_simplicity_energy_identity (u v zeta : Yau.Jets.Coord → ℝ)
    (hu : ContDiff ℝ ∞ u) (hv : ContDiff ℝ ∞ v) (hz : ContDiff ℝ ∞ zeta)
    (hc : HasCompactSupport zeta) (lam : ℝ) (hlam : lam ≠ 0) :
    Integrable (fun x ↦ roundCoordDensity x * (zeta x*u x^2*Yau.pairing v (roundCoordGradient v) x -
      lam*simplicityDensityPerturbation roundCoordDensity u zeta (roundCoordGradient u) lam x*v x^2)) ∧
    roundSimplicityEnergy u v zeta lam =
      ∫ x, roundCoordDensity x*zeta x*roundSimplicitySquare u v x := by
  let V : Yau.Jets.Coord → Yau.Jets.Coord :=
    fun y i ↦ (u y*v y^2)*(zeta y*roundCoordGradient u y i)
  have hV (i : Fin 4) : ContDiff ℝ ∞ (fun x ↦ V x i) :=
    (hu.mul (hv.pow 2)).mul (hz.mul ((contDiff_pi.mp (roundCoordGradient_smooth u hu)) i))
  have hVc (i : Fin 4) : HasCompactSupport (fun x ↦ V x i) := by
    have h : HasCompactSupport (fun x ↦ zeta x*roundCoordGradient u x i) := hc.mul_right
    exact h.mul_left
  obtain ⟨hiD,hD⟩ := Yau.integral_weightedDiv_compact_zero roundCoordDensity
    roundCoordDensity_smooth (fun x ↦ (roundCoordDensity_pos x).ne') V hV hVc
  have hiS := round_simplicity_square_integrable u v zeta hu hv hz hc
  have he : (fun x ↦ roundCoordDensity x * (zeta x*u x^2*Yau.pairing v (roundCoordGradient v) x -
      lam*simplicityDensityPerturbation roundCoordDensity u zeta (roundCoordGradient u) lam x*v x^2)) =
      (fun x ↦ roundCoordDensity x*zeta x*roundSimplicitySquare u v x +
        roundCoordDensity x*Yau.weightedDiv roundCoordDensity V x) := by
    funext x
    rw [round_simplicity_energy_density u v zeta hu hv hz lam hlam x]
    change _ = _ + roundCoordDensity x*Yau.weightedDiv roundCoordDensity
      (fun y i ↦ (u y*v y^2)*(zeta y*roundCoordGradient u y i)) x
    ring
  constructor
  · rw [he]
    exact hiS.add hiD
  · unfold roundSimplicityEnergy
    rw [he,integral_add hiS hiD,hD,add_zero]

lemma round_simplicity_energy_nonneg (u v zeta : Yau.Jets.Coord → ℝ)
    (hu : ContDiff ℝ ∞ u) (hv : ContDiff ℝ ∞ v) (hz : ContDiff ℝ ∞ zeta)
    (hc : HasCompactSupport zeta) (hzn : ∀ x, 0 ≤ zeta x) (lam : ℝ) (hlam : lam ≠ 0) :
    0 ≤ roundSimplicityEnergy u v zeta lam := by
  rw [(round_simplicity_energy_identity u v zeta hu hv hz hc lam hlam).2]
  exact integral_nonneg (fun x ↦ mul_nonneg (mul_nonneg (roundCoordDensity_pos x).le (hzn x))
    (roundSimplicitySquare_nonneg u v x))

theorem round_simplicity_zero_energy_jet (u v zeta : Yau.Jets.Coord → ℝ)
    (hu : ContDiff ℝ ∞ u) (hv : ContDiff ℝ ∞ v) (hz : ContDiff ℝ ∞ zeta)
    (hc : HasCompactSupport zeta) (hzn : ∀ x, 0 ≤ zeta x) (lam : ℝ) (hlam : lam ≠ 0)
    (he : roundSimplicityEnergy u v zeta lam = 0) :
    ∀ x, 0 < zeta x → ∀ i : Fin 4,
      u x*Yau.coordPartial v x i = v x*Yau.coordPartial u x i := by
  have hi := round_simplicity_square_integrable u v zeta hu hv hz hc
  have hs := ((roundCoordDensity_smooth.mul hz).mul (roundSimplicitySquare_smooth u v hu hv)).continuous
  have hn (x) : 0 ≤ roundCoordDensity x*zeta x*roundSimplicitySquare u v x :=
    mul_nonneg (mul_nonneg (roundCoordDensity_pos x).le (hzn x)) (roundSimplicitySquare_nonneg u v x)
  have hint : (∫ x, roundCoordDensity x*zeta x*roundSimplicitySquare u v x) = 0 :=
    (round_simplicity_energy_identity u v zeta hu hv hz hc lam hlam).2.symm.trans he
  have hzall (x) : roundCoordDensity x*zeta x*roundSimplicitySquare u v x = 0 := by
    by_contra hx
    have hp := integral_pos_of_integrable_nonneg_nonzero hs hi hn hx
    linarith only [hint,hp]
  intro x hx i
  have hsq : roundSimplicitySquare u v x = 0 :=
    (mul_eq_zero.mp (hzall x)).resolve_left (mul_pos (roundCoordDensity_pos x) hx).ne'
  have hfac : 0 < roundCoordFactor x := lt_of_lt_of_le zero_lt_one (roundCoordFactor_ge_one x)
  have hsum : ∑ i : Fin 4, (u x*Yau.coordPartial v x i-v x*Yau.coordPartial u x i)^2 = 0 :=
    (mul_eq_zero.mp hsq).resolve_left hfac.ne'
  have hle := Finset.single_le_sum (fun j (_ : j ∈ Finset.univ) ↦
    sq_nonneg (u x*Yau.coordPartial v x j-v x*Yau.coordPartial u x j)) (Finset.mem_univ i)
  rw [hsum] at hle
  have hzsq := le_antisymm hle (sq_nonneg (u x*Yau.coordPartial v x i-v x*Yau.coordPartial u x i))
  exact sub_eq_zero.mp (sq_eq_zero_iff.mp hzsq)

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Charts_SphereSimplicityEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Manifold Yau.Geometry Yau.Jets Set MeasureTheory
open scoped ContDiff
noncomputable section
attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace normedSpaceTangentSpaceVectorSpace

local instance sphereSimplicityEnergyLocal1_r192374_1 : MeasurableSpace Base := borel Base
local instance sphereSimplicityEnergyLocal2_r192374_1 : BorelSpace Base := ⟨rfl⟩
lemma roundCotangentTensor_seed_diagonal (v : Base → ℝ)
    (hv : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ v) (x : Yau.Jets.Coord) :
    roundCotangentTensor (seedSphereFromCoord x)
      (sphereDifferential v (seedSphereFromCoord x)) (sphereDifferential v (seedSphereFromCoord x)) =
      Yau.pairing (v ∘ seedSphereFromCoord) (roundCoordGradient (v ∘ seedSphereFromCoord)) x := by
  have h := roundCotangentTensor_differential_pair v v hv hv seedPoint x
  change roundCotangentTensor (seedSphereFromCoord x)
    (sphereDifferential v (seedSphereFromCoord x)) (sphereDifferential v (seedSphereFromCoord x)) =
    roundCoordFactor x * ∑ i, Yau.coordPartial (v ∘ seedSphereFromCoord) x i *
    Yau.coordPartial (v ∘ seedSphereFromCoord) x i at h
  rw [h]
  unfold Yau.pairing roundCoordGradient Yau.coordPartial
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

lemma sphere_simplicity_energy_eq_coordinate (u v a b : Base → ℝ)
    (hv : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ v) (zeta : Yau.Jets.Coord → ℝ) (lam : ℝ)
    (ha : ∀ x, a (seedSphereFromCoord x) = zeta x*u (seedSphereFromCoord x)^2)
    (hb : ∀ x, b (seedSphereFromCoord x) = simplicityDensityPerturbation roundCoordDensity
      (u ∘ seedSphereFromCoord) zeta (roundCoordGradient (u ∘ seedSphereFromCoord)) lam x) :
    sphereEnergyForm a b lam v v =
      roundSimplicityEnergy (u ∘ seedSphereFromCoord) (v ∘ seedSphereFromCoord) zeta lam := by
  rw [sphereEnergyForm,sphereReferenceMeasure_integral]
  unfold roundSimplicityEnergy
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro x
  change roundCoordDensity x*sphereEnergyDensity a b lam v v (seedSphereFromCoord x) = _
  rw [sphereEnergyDensity,roundTensorPerturbation_apply,roundCotangentTensor_seed_diagonal v hv,ha,hb]
  simp only [Function.comp_apply]
  ring

theorem sphere_simplicity_energy_identity (u v a b Z : Base → ℝ)
    (hu : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ u) (hv : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ v)
    (zeta : Yau.Jets.Coord → ℝ) (hz : ContDiff ℝ ∞ zeta) (hc : HasCompactSupport zeta)
    (lam : ℝ) (hlam : lam ≠ 0)
    (ha : ∀ x, a (seedSphereFromCoord x) = zeta x*u (seedSphereFromCoord x)^2)
    (hb : ∀ x, b (seedSphereFromCoord x) = simplicityDensityPerturbation roundCoordDensity
      (u ∘ seedSphereFromCoord) zeta (roundCoordGradient (u ∘ seedSphereFromCoord)) lam x)
    (hZ : ∀ x, Z (seedSphereFromCoord x) = zeta x) :
    Integrable (sphereEnergyDensity a b lam v v) sphereReferenceMeasure ∧
    Integrable (fun p ↦ Z p*roundCotangentTensor p (sphereCrossDifferential u v p)
      (sphereCrossDifferential u v p)) sphereReferenceMeasure ∧
    sphereEnergyForm a b lam v v = ∫ p, Z p*roundCotangentTensor p
      (sphereCrossDifferential u v p) (sphereCrossDifferential u v p) ∂sphereReferenceMeasure := by
  have hu' : ContDiff ℝ ∞ (u ∘ seedSphereFromCoord) := spherePullback_smooth u hu seedPoint
  have hv' : ContDiff ℝ ∞ (v ∘ seedSphereFromCoord) := spherePullback_smooth v hv seedPoint
  obtain ⟨hi,he⟩ := round_simplicity_energy_identity _ _ zeta hu' hv' hz hc lam hlam
  have hsq (x : Yau.Jets.Coord) :
      roundCotangentTensor (seedSphereFromCoord x)
        (sphereCrossDifferential u v (seedSphereFromCoord x))
        (sphereCrossDifferential u v (seedSphereFromCoord x)) =
        roundSimplicitySquare (u ∘ seedSphereFromCoord) (v ∘ seedSphereFromCoord) x :=
    sphereCrossDifferential_square_chart u v hu hv seedPoint x
  refine ⟨?_,?_,?_⟩
  · rw [sphereReferenceMeasure_integrable]
    convert hi using 1
    all_goals try with_reducible_and_instances rfl
    funext x
    rw [sphereEnergyDensity,roundTensorPerturbation_apply,roundCotangentTensor_seed_diagonal v hv,ha,hb]
    simp only [Function.comp_apply]
    ring
  · rw [sphereReferenceMeasure_integrable]
    simp only [hsq,hZ,← mul_assoc]
    exact round_simplicity_square_integrable _ _ zeta hu' hv' hz hc
  · rw [sphere_simplicity_energy_eq_coordinate u v a b hv zeta lam ha hb,he,
      sphereReferenceMeasure_integral]
    simp only [hsq,hZ,mul_assoc]

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Charts_SphereSimplicityAnnihilation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Manifold Yau.Geometry Yau.Jets Set MeasureTheory
open scoped ContDiff
noncomputable section
attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace normedSpaceTangentSpaceVectorSpace

local instance sphereSimplicityAnnihilationLocal1_r192374_1 : MeasurableSpace Base := borel Base
local instance sphereSimplicityAnnihilationLocal2_r192374_1 : BorelSpace Base := ⟨rfl⟩
lemma sphereCrossDifferential_self (u : Base → ℝ) (p : Base) : sphereCrossDifferential u u p = 0 := by
  simp [sphereCrossDifferential]

lemma sphereCrossDifferential_add_self (u v : Base → ℝ)
    (hu : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ u) (hv : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ v) (p : Base) :
    sphereCrossDifferential u (u+v) p = sphereCrossDifferential u v p := by
  simp only [sphereCrossDifferential,sphereDifferential_add u v hu hv,Pi.add_apply,smul_add,add_smul]
  abel

theorem sphere_simplicity_form_annihilates (u a b Z : Base → ℝ)
    (hu : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ u)
    (ha : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ a) (hb : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ b)
    {Q : Set Yau.Jets.Coord} (hQ : IsCompact Q)
    (haQ : tsupport a ⊆ seedSphereFromCoord '' Q) (hbQ : tsupport b ⊆ seedSphereFromCoord '' Q)
    (zeta : Yau.Jets.Coord → ℝ) (hz : ContDiff ℝ ∞ zeta) (hc : HasCompactSupport zeta)
    (lam : ℝ) (hlam : lam ≠ 0)
    (haval : ∀ x, a (seedSphereFromCoord x) = zeta x*u (seedSphereFromCoord x)^2)
    (hbval : ∀ x, b (seedSphereFromCoord x) = simplicityDensityPerturbation roundCoordDensity
      (u ∘ seedSphereFromCoord) zeta (roundCoordGradient (u ∘ seedSphereFromCoord)) lam x)
    (hZ : ∀ x, Z (seedSphereFromCoord x) = zeta x)
    (v : Base → ℝ) (hv : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ v) :
    sphereEnergyForm a b lam u v = 0 := by
  have hself := (sphere_simplicity_energy_identity u u a b Z hu hu zeta hz hc lam hlam haval hbval hZ).2.2
  have hsum := (sphere_simplicity_energy_identity u (u+v) a b Z hu (hu.add hv) zeta hz hc lam hlam haval hbval hZ).2.2
  have hvv := (sphere_simplicity_energy_identity u v a b Z hu hv zeta hz hc lam hlam haval hbval hZ).2.2
  have hzero : sphereEnergyForm a b lam u u = 0 := by
    simpa only [sphereCrossDifferential_self,map_zero,mul_zero,integral_zero] using hself
  have heq : sphereEnergyForm a b lam (u+v) (u+v) = sphereEnergyForm a b lam v v := by
    rw [hsum,hvv]
    simp only [sphereCrossDifferential_add_self u v hu hv]
  rw [sphereEnergyForm_add_left a b ha hb hQ haQ hbQ lam u v (u+v) hu hv (hu.add hv),
    sphereEnergyForm_add_right a b ha hb hQ haQ hbQ lam u u v hu hu hv,
    sphereEnergyForm_add_right a b ha hb hQ haQ hbQ lam v u v hv hu hv,hzero,
    sphereEnergyForm_symm a b lam v u] at heq
  linarith

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_SeedCoordPatchTopology
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Yau.Geometry Yau.Jets Set Metric
open scoped Topology
noncomputable section

lemma seedCoordPatch_open (r : ℝ) : IsOpen (seedCoordPatch r) :=
  isOpen_ball.preimage seedCoordEquiv.continuous

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Charts_SphereSimplicityBump
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Manifold Yau.Geometry Yau.Jets Set Metric
open scoped ContDiff Topology
noncomputable section

theorem exists_sphere_simplicity_bump {r : ℝ} (hr : 0 < r) :
    ∃ (Q : Set Yau.Jets.Coord) (zeta : Yau.Jets.Coord → ℝ) (Z : Base → ℝ) (s : ℝ),
      IsCompact Q ∧ Q ⊆ seedCoordPatch r ∧ ContDiff ℝ ∞ zeta ∧ tsupport zeta ⊆ Q ∧
      (∀ x, 0 ≤ zeta x ∧ zeta x ≤ 1) ∧ 0 < s ∧
      (∀ x ∈ closedBall (0 : Yau.Jets.Coord) s, zeta x = 1) ∧
      ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ Z ∧ tsupport Z ⊆ seedSphereFromCoord '' Q ∧
      (∀ x, Z (seedSphereFromCoord x) = zeta x) ∧ (∀ p, 0 ≤ Z p) ∧
      ∃ U : Set Base, IsOpen U ∧ U.Nonempty ∧ U ⊆ seedSpherePatch r ∧ ∀ p ∈ U, 0 < Z p := by
  have hzero : (0 : Yau.Jets.Coord) ∈ seedCoordPatch r := by
    simp [seedCoordPatch,hr]
  obtain ⟨e,he,hes⟩ := Metric.isOpen_iff.mp (seedCoordPatch_open r) 0 hzero
  have he2 : 0 < e/2 := half_pos he
  have hball : closedBall (0 : Yau.Jets.Coord) (e/2) ⊆ seedCoordPatch r :=
    (closedBall_subset_ball (by linarith)).trans hes
  obtain ⟨zeta,hz,hzc,hzs,hzr,hz1⟩ := compact_smooth_cutoff
    (isCompact_closedBall (0 : Yau.Jets.Coord) (e/2)) (seedCoordPatch_open r) hball
  obtain ⟨Z,hZ,hZs,hZval⟩ := seed_chart_scalar_extension zeta hz hzc
  have hZn (p : Base) : 0 ≤ Z p := by
    by_cases hp : p ∈ tsupport Z
    · obtain ⟨x,hx,rfl⟩ := hZs hp
      rw [hZval]
      exact (hzr x).1
    · rw [image_eq_zero_of_notMem_tsupport hp]
  refine ⟨tsupport zeta,zeta,Z,e/2,hzc,hzs,hz,Subset.rfl,hzr,he2,
    (fun x hx ↦ (hz1 x hx).eq_of_nhds),hZ,hZs,hZval,hZn,
    Z ⁻¹' Ioi 0,isOpen_Ioi.preimage hZ.continuous,?_,?_,fun p hp ↦ hp⟩
  · refine ⟨seedSphereFromCoord 0,?_⟩
    change 0 < Z (seedSphereFromCoord 0)
    rw [hZval,(hz1 0 (mem_closedBall_self he2.le)).eq_of_nhds]
    norm_num
  · intro p hp
    have hn : Z p ≠ 0 := (show 0 < Z p from hp).ne'
    obtain ⟨x,hx,rfl⟩ := hZs (subset_closure hn)
    exact ⟨seedCoordEquiv x,hzs hx,rfl⟩

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

lemma seed_scalar_pullback_smooth (b : Base → ℝ)
    (hb : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ b) :
    ContDiff ℝ ∞ (fun x ↦ b (seedSphereFromCoord x)) := by
  apply contDiff_iff_contDiffAt.mpr
  intro x
  exact (smooth_inverse_chart_comp b hb seedPoint
    (by rw [centeredSphereChart_target]; trivial)).comp x seedCoordEquiv.contDiff.contDiffAt

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Charts_SphereSimplicityExtension
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Manifold Yau.Geometry Yau.Jets Set
open scoped ContDiff
noncomputable section

theorem sphere_simplicity_extension (u : Base → ℝ)
    (hu : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ u) (lam : ℝ) (hlam : lam ≠ 0)
    (zeta : Yau.Jets.Coord → ℝ) (hz : ContDiff ℝ ∞ zeta)
    {Q : Set Yau.Jets.Coord} (hQ : IsCompact Q) (hzQ : tsupport zeta ⊆ Q) :
    ∃ a b : Base → ℝ,
      ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ a ∧ ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ b ∧
      tsupport a ⊆ seedSphereFromCoord '' Q ∧ tsupport b ⊆ seedSphereFromCoord '' Q ∧
      (∀ x, a (seedSphereFromCoord x) = zeta x*(u (seedSphereFromCoord x))^2) ∧
      (∀ x, b (seedSphereFromCoord x) = simplicityDensityPerturbation roundCoordDensity
        (fun y ↦ u (seedSphereFromCoord y)) zeta
        (roundCoordGradient (fun y ↦ u (seedSphereFromCoord y))) lam x) ∧
      ∀ x, Yau.weightedDiv roundCoordDensity
        (fun y i ↦ a (seedSphereFromCoord y)*
          roundCoordGradient (fun z ↦ u (seedSphereFromCoord z)) y i) x +
        lam*b (seedSphereFromCoord x)*u (seedSphereFromCoord x) = 0 := by
  obtain ⟨ha,hb,haS,hbS,hformula,hcancel⟩ := round_simplicity_coordinate_perturbation
    (fun y ↦ u (seedSphereFromCoord y)) zeta (seed_scalar_pullback_smooth u hu) hz lam hlam
  obtain ⟨a,has,haQ,haval⟩ := seed_chart_scalar_extension _ ha
    (hQ.of_isClosed_subset isClosed_closure (haS.trans hzQ))
  obtain ⟨b,hbs,hbQ,hbval⟩ := seed_chart_scalar_extension _ hb
    (hQ.of_isClosed_subset isClosed_closure (hbS.trans hzQ))
  refine ⟨a,b,has,hbs,haQ.trans (image_mono (haS.trans hzQ)),
    hbQ.trans (image_mono (hbS.trans hzQ)),haval,hbval,?_⟩
  simpa only [haval,hbval] using hcancel

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_SimplicityLocalRigidity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Yau.Geometry Yau.Jets Set
open scoped ContDiff
noncomputable section

theorem round_simplicity_local_rigidity (u v zeta : Yau.Jets.Coord → ℝ)
    (hu : ContDiff ℝ ∞ u) (hv : ContDiff ℝ ∞ v) (hz : ContDiff ℝ ∞ zeta)
    (hc : HasCompactSupport zeta) (hzn : ∀ x, 0 ≤ zeta x) (lam : ℝ) (hlam : lam ≠ 0)
    (he : roundSimplicityEnergy u v zeta lam = 0)
    {U : Set Yau.Jets.Coord} (hU : IsOpen U) (hUc : IsPreconnected U)
    (hUz : ∀ x ∈ U, 0 < zeta x) (hUn : ∀ x ∈ U, u x ≠ 0) :
    ∃ c : ℝ, ∀ x ∈ U, v x = c*u x := by
  let q : Yau.Jets.Coord → ℝ := fun x ↦ v x/u x
  have hq (x) (hx : x ∈ U) : DifferentiableAt ℝ q x :=
    ((hv.contDiffAt.div hu.contDiffAt (hUn x hx)).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top))
  have hj := round_simplicity_zero_energy_jet u v zeta hu hv hz hc hzn lam hlam he
  have hqd (x) (hx : x ∈ U) : fderiv ℝ q x = 0 := by
    have hd := (hasDerivAt_inv (hUn x hx)).comp_hasFDerivAt x
      (hu.differentiable (by simp) x).hasFDerivAt
    have hm := (hv.differentiable (by simp) x).hasFDerivAt.mul hd
    have heq : q = fun y ↦ v y*(u y)⁻¹ := by funext y; exact div_eq_mul_inv _ _
    have hmf := hm.fderiv
    change fderiv ℝ (fun y ↦ v y*(u y)⁻¹) x = _ at hmf
    have hL : (fderiv ℝ q x).toLinearMap = 0 := by
      apply (Pi.basisFun ℝ (Fin 4)).ext
      intro i
      simp only [Pi.basisFun_apply,LinearMap.zero_apply]
      change fderiv ℝ q x (Pi.single i 1) = 0
      rw [heq,hmf]
      simp only [add_apply,smul_apply,smul_eq_mul,Function.comp_def]
      have h := hj x (hUz x hx) i
      unfold Yau.coordPartial at h
      field_simp [hUn x hx]
      nlinarith only [h]
    ext w
    exact congrArg (fun L : Yau.Jets.Coord →ₗ[ℝ] ℝ ↦ L w) hL
  obtain ⟨c,hc⟩ := hU.exists_is_const_of_fderiv_eq_zero hUc
    (fun x hx ↦ (hq x hx).differentiableWithinAt) (fun x hx ↦ hqd x hx)
  refine ⟨c,?_⟩
  intro x hx
  exact (div_eq_iff (hUn x hx)).mp (hc x hx)

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Charts_SphereSimplicityRigidity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Manifold Yau.Geometry Yau.Jets Set MeasureTheory Metric
open scoped ContDiff Topology
noncomputable section
attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace normedSpaceTangentSpaceVectorSpace

variable (u v a b : Base → ℝ)
    (hu : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ u) (hv : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ v)
    (zeta : Yau.Jets.Coord → ℝ) (hz : ContDiff ℝ ∞ zeta) (hc : HasCompactSupport zeta)
    (hzn : ∀ x, 0 ≤ zeta x) (lam : ℝ) (hlam : lam ≠ 0)
    (ha : ∀ x, a (seedSphereFromCoord x) = zeta x*u (seedSphereFromCoord x)^2)
    (hb : ∀ x, b (seedSphereFromCoord x) = simplicityDensityPerturbation roundCoordDensity
      (u ∘ seedSphereFromCoord) zeta (roundCoordGradient (u ∘ seedSphereFromCoord)) lam x)

include hu hv hz hc hzn hlam ha hb

local instance sphereSimplicityRigidityLocal1_r192374_1 : MeasurableSpace Base := borel Base
local instance sphereSimplicityRigidityLocal2_r192374_1 : BorelSpace Base := ⟨rfl⟩
lemma sphere_simplicity_energy_nonneg : 0 ≤ sphereEnergyForm a b lam v v := by
  rw [sphere_simplicity_energy_eq_coordinate u v a b hv zeta lam ha hb]
  exact round_simplicity_energy_nonneg _ _ zeta (spherePullback_smooth u hu seedPoint)
    (spherePullback_smooth v hv seedPoint) hz hc hzn lam hlam

theorem sphere_simplicity_local_ball
    (he : sphereEnergyForm a b lam v v = 0) (x : Yau.Jets.Coord)
    (hxz : 0 < zeta x) (hxu : u (seedSphereFromCoord x) ≠ 0) :
    ∃ (c : ℝ) (U : Set Base), IsOpen U ∧ seedSphereFromCoord x ∈ U ∧
      ∀ p ∈ U, v p = c*u p := by
  have hu' : ContDiff ℝ ∞ (u ∘ seedSphereFromCoord) := spherePullback_smooth u hu seedPoint
  have hv' : ContDiff ℝ ∞ (v ∘ seedSphereFromCoord) := spherePullback_smooth v hv seedPoint
  let W : Set Yau.Jets.Coord := {y | 0 < zeta y ∧ u (seedSphereFromCoord y) ≠ 0}
  have hWo : IsOpen W := (isOpen_lt continuous_const hz.continuous).inter
    (isOpen_ne_fun hu'.continuous continuous_const)
  obtain ⟨r,hr,hrW⟩ := Metric.isOpen_iff.mp hWo x ⟨hxz,hxu⟩
  have he' := (sphere_simplicity_energy_eq_coordinate u v a b hv zeta lam ha hb).symm.trans he
  obtain ⟨c,hc⟩ := round_simplicity_local_rigidity _ _ zeta hu' hv' hz hc hzn lam hlam he'
    isOpen_ball (convex_ball x r).isPreconnected
    (fun y hy ↦ (hrW hy).1) (fun y hy ↦ (hrW hy).2)
  refine ⟨c,seedSphereFromCoord '' ball x r,?_,⟨x,mem_ball_self hr,rfl⟩,?_⟩
  · exact sphereChartCoordMap_isOpenMap seedPoint _ isOpen_ball
  · rintro p ⟨y,hy,rfl⟩
    exact hc y hy

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
-- module Solutions.OAIQ237_NY.NodalSets_Persistence_SphereWeakUniqueContinuation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Manifold Yau.Geometry Set Filter
open scoped ContDiff Topology
noncomputable section

lemma sphere_base_preconnected : PreconnectedSpace Base := by
  apply isPreconnected_iff_preconnectedSpace.mp
  apply isPreconnected_sphere
  rw [← Module.finrank_eq_rank]
  norm_num [AmbientBase]

lemma intrinsic_chart_zero_from_germ (A : IntrinsicTensor) (hA : IntrinsicTensorSmooth A)
    (hs : ∀ p v w, A p v w = A p w v) (hp : ∀ p v, v ≠ 0 → 0 < A p v v)
    (rho : Base → ℝ) (hr : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ rho) (hrp : ∀ p, 0 < rho p)
    (w : Base → ℝ) (hw : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ w) (lam : ℝ)
    (he : ∀ p z, -intrinsicWeightedChartOperator A rho w p z =
      lam*w ((extChartAt (𝓡 4) p).symm z))
    (p : Base) (y : Yau.Jets.Coord) (hy : w =ᶠ[𝓝 (sphereChartCoordMap p y)] (fun _ ↦ 0)) :
    ∀ x, w (sphereChartCoordMap p x) = 0 := by
  have hy' : (w ∘ sphereChartCoordMap p) =ᶠ[𝓝 y] (fun _ ↦ 0) :=
    hy.comp_tendsto (sphereChartCoordMap_smooth p).continuous.continuousAt
  have hEq (x) : realEllipticResidual roundCoordDensity (intrinsicRealPotential rho lam p)
      (intrinsicRealPrincipal A p) (w ∘ sphereChartCoordMap p) x = 0 :=
    intrinsic_real_divergence_equation A rho hrp w lam he p x
  have hzero := real_global_unique_continuation roundCoordDensity (intrinsicRealPotential rho lam p)
    (w ∘ sphereChartCoordMap p) (intrinsicRealPrincipal A p) roundCoordDensity_smooth roundCoordDensity_pos
    (intrinsicRealPotential_smooth rho hr lam p) (intrinsicRealPrincipal_smooth A hA hs hp p)
    (intrinsicRealPrincipal_symmetric A hs p) (spherePullback_smooth w hw p)
    (intrinsicRealPrincipal_posDef A hs hp p) hEq y hy'
  intro x
  exact congrFun hzero x

theorem sphere_weak_unique_continuation (A : IntrinsicTensor) (hA : IntrinsicTensorSmooth A)
    (hs : ∀ p v w, A p v w = A p w v) (hp : ∀ p v, v ≠ 0 → 0 < A p v v)
    (rho : Base → ℝ) (hr : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ rho) (hrp : ∀ p, 0 < rho p)
    (w : Base → ℝ) (hw : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ w) (lam : ℝ)
    (he : ∀ p z, -intrinsicWeightedChartOperator A rho w p z =
      lam*w ((extChartAt (𝓡 4) p).symm z))
    (p : Base) (hz : w =ᶠ[𝓝 p] (fun _ ↦ 0)) : w = 0 := by
  let := sphere_base_preconnected
  let Z := (tsupport w)ᶜ
  have hZ : IsOpen Z := (isClosed_tsupport w).isOpen_compl
  have hne : (univ ∩ Z).Nonempty := ⟨p,mem_univ _,notMem_tsupport_iff_eventuallyEq.mpr hz⟩
  have hclosed : closure Z ∩ univ ⊆ Z := by
    intro q hq
    let V := sphereChartCoordMap q '' (univ : Set Yau.Jets.Coord)
    have hV : IsOpen V := sphereChartCoordMap_isOpenMap q _ isOpen_univ
    have hqV : q ∈ V := ⟨0,mem_univ _,sphereChartCoordMap_zero q⟩
    obtain ⟨a,haV,haZ⟩ := mem_closure_iff.mp hq.1 V hV hqV
    obtain ⟨y,_,rfl⟩ := haV
    have hchart := intrinsic_chart_zero_from_germ A hA hs hp rho hr hrp w hw lam he q y
      (notMem_tsupport_iff_eventuallyEq.mp haZ)
    have hh : w =ᶠ[𝓝 q] (fun _ ↦ 0) := by
      filter_upwards [hV.mem_nhds hqV] with a ha
      obtain ⟨x,_,rfl⟩ := ha
      exact hchart x
    exact notMem_tsupport_iff_eventuallyEq.mpr hh
  have hall := isPreconnected_univ.subset_of_closure_inter_subset hZ hne hclosed
  funext q
  exact image_eq_zero_of_notMem_tsupport (hall (mem_univ q))

theorem sphere_eigenfunction_nonzero_on_open (A : IntrinsicTensor) (hA : IntrinsicTensorSmooth A)
    (hs : ∀ p v w, A p v w = A p w v) (hp : ∀ p v, v ≠ 0 → 0 < A p v v)
    (rho : Base → ℝ) (hr : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ rho) (hrp : ∀ p, 0 < rho p)
    (w : Base → ℝ) (hw : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ w) (lam : ℝ)
    (he : ∀ p z, -intrinsicWeightedChartOperator A rho w p z =
      lam*w ((extChartAt (𝓡 4) p).symm z)) (hne : w ≠ 0)
    (U : Set Base) (hU : IsOpen U) (hUn : U.Nonempty) : ∃ p ∈ U, w p ≠ 0 := by
  by_contra hn
  push Not at hn
  obtain ⟨p,hpU⟩ := hUn
  have hh : w =ᶠ[𝓝 p] (fun _ ↦ 0) := by
    filter_upwards [hU.mem_nhds hpU] with q hq
    exact hn q hq
  exact hne (sphere_weak_unique_continuation A hA hs hp rho hr hrp w hw lam he p hh)

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
-- module Solutions.OAIQ237_NY.NodalSets_Charts_SphereSimplicityKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Manifold Yau.Geometry Set Filter MeasureTheory
open scoped ContDiff Topology
noncomputable section

lemma sphere_simplicity_self_energy_zero (u a b : Base → ℝ)
    (hu : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ u)
    (zeta : Yau.Jets.Coord → ℝ) (hz : ContDiff ℝ ∞ zeta) (hc : HasCompactSupport zeta)
    (lam : ℝ) (hlam : lam ≠ 0)
    (ha : ∀ x, a (seedSphereFromCoord x) = zeta x*u (seedSphereFromCoord x)^2)
    (hb : ∀ x, b (seedSphereFromCoord x) = simplicityDensityPerturbation roundCoordDensity
      (u ∘ seedSphereFromCoord) zeta (roundCoordGradient (u ∘ seedSphereFromCoord)) lam x) :
    sphereEnergyForm a b lam u u = 0 := by
  rw [sphere_simplicity_energy_eq_coordinate u u a b hu zeta lam ha hb,
    (round_simplicity_energy_identity (u ∘ seedSphereFromCoord) (u ∘ seedSphereFromCoord) zeta (spherePullback_smooth u hu seedPoint)
      (spherePullback_smooth u hu seedPoint) hz hc lam hlam).2]
  simp [roundSimplicitySquare]

theorem sphere_simplicity_zero_energy_global (A : IntrinsicTensor) (hA : IntrinsicTensorSmooth A)
    (hs : ∀ p v w, A p v w = A p w v) (hp : ∀ p v, v ≠ 0 → 0 < A p v v)
    (rho : Base → ℝ) (hr : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ rho) (hrp : ∀ p, 0 < rho p)
    (u v a b : Base → ℝ)
    (hu : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ u) (hv : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ v) (hune : u ≠ 0)
    (lam : ℝ) (hlam : lam ≠ 0)
    (heu : ∀ p z, -intrinsicWeightedChartOperator A rho u p z = lam*u ((extChartAt (𝓡 4) p).symm z))
    (hev : ∀ p z, -intrinsicWeightedChartOperator A rho v p z = lam*v ((extChartAt (𝓡 4) p).symm z))
    (zeta : Yau.Jets.Coord → ℝ) (hz : ContDiff ℝ ∞ zeta) (hc : HasCompactSupport zeta)
    (hzn : ∀ x, 0 ≤ zeta x) (hzpos : ∃ x, 0 < zeta x)
    (ha : ∀ x, a (seedSphereFromCoord x) = zeta x*u (seedSphereFromCoord x)^2)
    (hb : ∀ x, b (seedSphereFromCoord x) = simplicityDensityPerturbation roundCoordDensity
      (u ∘ seedSphereFromCoord) zeta (roundCoordGradient (u ∘ seedSphereFromCoord)) lam x)
    (henergy : sphereEnergyForm a b lam v v = 0) : ∃ c : ℝ, ∀ p, v p = c*u p := by
  let O := {x : Yau.Jets.Coord | 0 < zeta x}
  have hO : IsOpen O := isOpen_lt continuous_const hz.continuous
  obtain ⟨p,⟨x,hxz,rfl⟩,hxu⟩ := sphere_eigenfunction_nonzero_on_open A hA hs hp rho hr hrp u hu lam
    heu hune (seedSphereFromCoord '' O) (sphereChartCoordMap_isOpenMap seedPoint O hO)
    (Set.Nonempty.image _ hzpos)
  obtain ⟨c,U,hU,hxU,hlocal⟩ := sphere_simplicity_local_ball u v a b hu hv zeta hz hc hzn lam hlam
    ha hb henergy x hxz hxu
  let w := fun p : Base ↦ (-c)*u p+v p
  have hw : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ w := (contMDiff_const.mul hu).add hv
  have hew : ∀ p z, -intrinsicWeightedChartOperator A rho w p z = lam*w ((extChartAt (𝓡 4) p).symm z) :=
    intrinsic_eigenfunction_linear_combination A hA hs hp rho u v hu hv lam heu hev (-c)
  have hw0 : w =ᶠ[𝓝 (seedSphereFromCoord x)] (fun _ ↦ 0) := by
    filter_upwards [hU.mem_nhds hxU] with p hpU
    dsimp [w]
    rw [hlocal p hpU]
    ring
  have hglobal := sphere_weak_unique_continuation A hA hs hp rho hr hrp w hw lam hew
    (seedSphereFromCoord x) hw0
  refine ⟨c,?_⟩
  intro p
  have hh := congrFun hglobal p
  change (-c)*u p+v p=0 at hh
  linarith

theorem sphere_simplicity_energy_kernel_iff (A : IntrinsicTensor) (hA : IntrinsicTensorSmooth A)
    (hs : ∀ p v w, A p v w = A p w v) (hp : ∀ p v, v ≠ 0 → 0 < A p v v)
    (rho : Base → ℝ) (hr : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ rho) (hrp : ∀ p, 0 < rho p)
    (u v a b : Base → ℝ)
    (hu : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ u) (hv : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ v) (hune : u ≠ 0)
    (lam : ℝ) (hlam : lam ≠ 0)
    (heu : ∀ p z, -intrinsicWeightedChartOperator A rho u p z = lam*u ((extChartAt (𝓡 4) p).symm z))
    (hev : ∀ p z, -intrinsicWeightedChartOperator A rho v p z = lam*v ((extChartAt (𝓡 4) p).symm z))
    (zeta : Yau.Jets.Coord → ℝ) (hz : ContDiff ℝ ∞ zeta) (hc : HasCompactSupport zeta)
    (hzn : ∀ x, 0 ≤ zeta x) (hzpos : ∃ x, 0 < zeta x)
    (ha : ∀ x, a (seedSphereFromCoord x) = zeta x*u (seedSphereFromCoord x)^2)
    (hb : ∀ x, b (seedSphereFromCoord x) = simplicityDensityPerturbation roundCoordDensity
      (u ∘ seedSphereFromCoord) zeta (roundCoordGradient (u ∘ seedSphereFromCoord)) lam x) :
    sphereEnergyForm a b lam v v = 0 ↔ ∃ c : ℝ, ∀ p, v p = c*u p := by
  constructor
  · exact sphere_simplicity_zero_energy_global A hA hs hp rho hr hrp u v a b hu hv hune lam hlam
      heu hev zeta hz hc hzn hzpos ha hb
  · rintro ⟨c,hcval⟩
    have hvval : v = c • u := funext hcval
    rw [hvval,sphereEnergyForm_smul_left a b lam u _ hu,
      sphereEnergyForm_smul_right a b lam u u hu,
      sphere_simplicity_self_energy_zero u a b hu zeta hz hc lam hlam ha hb,mul_zero,mul_zero]

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Charts_SphereSimplicityKernelForm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Manifold Yau.Geometry Set
open scoped ContDiff
noncomputable section

theorem exists_sphere_simplicity_kernel_form_oai (A : IntrinsicTensor) (hA : IntrinsicTensorSmooth A)
    (hs : ∀ p v w, A p v w = A p w v) (hp : ∀ p v, v ≠ 0 → 0 < A p v v)
    (rho : Base → ℝ) (hr : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ rho) (hrp : ∀ p, 0 < rho p)
    (u : Base → ℝ) (hu : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ u) (hune : u ≠ 0)
    (lam : ℝ) (hlam : 0 < lam)
    (heu : ∀ p z, -intrinsicWeightedChartOperator A rho u p z = lam*u ((extChartAt (𝓡 4) p).symm z))
    (r : ℝ) (hradius : 0 < r) :
    ∃ (Q : Set Yau.Jets.Coord) (zeta : Yau.Jets.Coord → ℝ) (a b : Base → ℝ),
      IsCompact Q ∧ Q ⊆ seedCoordPatch r ∧ ContDiff ℝ ∞ zeta ∧ tsupport zeta ⊆ Q ∧
      (∀ x, 0 ≤ zeta x) ∧ (∃ x, 0 < zeta x) ∧
      ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ a ∧ ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ b ∧
      tsupport a ⊆ seedSphereFromCoord '' Q ∧ tsupport b ⊆ seedSphereFromCoord '' Q ∧
      (∀ x, a (seedSphereFromCoord x) = zeta x*u (seedSphereFromCoord x)^2) ∧
      (∀ x, b (seedSphereFromCoord x) = simplicityDensityPerturbation roundCoordDensity
        (u ∘ seedSphereFromCoord) zeta (roundCoordGradient (u ∘ seedSphereFromCoord)) lam x) ∧
      (∀ x, Yau.weightedDiv roundCoordDensity
        (fun y i ↦ a (seedSphereFromCoord y)*roundCoordGradient (u ∘ seedSphereFromCoord) y i) x+
        lam*b (seedSphereFromCoord x)*u (seedSphereFromCoord x) = 0) ∧
      (∀ v : Base → ℝ, ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ v →
        0 ≤ sphereEnergyForm a b lam v v ∧ sphereEnergyForm a b lam u v = 0) ∧
      ∀ v : Base → ℝ, ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ v →
        (∀ p z, -intrinsicWeightedChartOperator A rho v p z = lam*v ((extChartAt (𝓡 4) p).symm z)) →
        (sphereEnergyForm a b lam v v = 0 ↔ ∃ c : ℝ, ∀ p, v p = c*u p) := by
  obtain ⟨Q,zeta,Z,s,hQ,hQr,hz,hzQ,hzn,hs0,hz1,hZ,hZQ,hZval,hZn,hU⟩ :=
    exists_sphere_simplicity_bump hradius
  obtain ⟨a,b,ha,hb,haQ,hbQ,haval,hbval,hcancel⟩ :=
    sphere_simplicity_extension u hu lam hlam.ne' zeta hz hQ hzQ
  have hzc : HasCompactSupport zeta := hQ.of_isClosed_subset isClosed_closure hzQ
  have hzpos : ∃ x, 0 < zeta x := ⟨0,by rw [hz1 0 (Metric.mem_closedBall_self hs0.le)]; norm_num⟩
  refine ⟨Q,zeta,a,b,hQ,hQr,hz,hzQ,(fun x ↦ (hzn x).1),hzpos,ha,hb,haQ,hbQ,haval,hbval,hcancel,?_,?_⟩
  · intro v hv
    exact ⟨sphere_simplicity_energy_nonneg u v a b hu hv zeta hz hzc (fun x ↦ (hzn x).1)
        lam hlam.ne' haval hbval,
      sphere_simplicity_form_annihilates u a b Z hu ha hb hQ haQ hbQ zeta hz hzc lam hlam.ne'
        haval hbval hZval v hv⟩
  · intro v hv hev
    exact sphere_simplicity_energy_kernel_iff A hA hs hp rho hr hrp u v a b hu hv hune lam hlam.ne'
      heu hev zeta hz hzc (fun x ↦ (hzn x).1) hzpos haval hbval

end
end Yau.Target

end OAI
end

theorem solution : type_of% @OAI.Yau.Target.exists_sphere_simplicity_kernel_form_oai := @OAI.Yau.Target.exists_sphere_simplicity_kernel_form_oai
