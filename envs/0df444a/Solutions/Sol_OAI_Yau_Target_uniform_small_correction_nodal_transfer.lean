-- Prove2me | solution 1 for OAI.Yau.Target.uniform_small_correction_nodal_transfer
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T00:36:06.285444+00:00
-- url     : https://prove2.me/submissions/bb99a4e2-dffa-4724-a4eb-82cf1ff5cca2

import Mathlib
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.ContDiff.RestrictScalars
import Mathlib.Analysis.Calculus.Deriv.Abs
import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.Calculus.TaylorIntegral
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Data.Finsupp.Weight
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
import Mathlib.MeasureTheory.Measure.Hausdorff
import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Definitions.Def_YauCounterexample
import Definitions.Def_OAIQ237Ny004
import Theorems.Thm_OAI_Yau_Target_uniform_intrinsic_coefficient_nodal_transfer

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

end
end Yau.Target

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
-- module Solutions.OAIQ237_NY.NodalSets_Charts_TargetShortCircleArc
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Manifold Set Yau.Jets
open scoped ContDiff Topology
noncomputable section

lemma productChartDomain_iff (p : Manifold5) (a b : ℝ) (z : _root_.OAI.Yau.Jets.Coord × ℝ) :
    z ∈ productChartDomain p a b ↔
      WithLp.toLp 2 z.1 ∈ (extChartAt (𝓡 4) p.1).target ∧
      WithLp.toLp 2 (fun _ : Fin 1 ↦ a+b*z.2) ∈ (extChartAt (𝓡 1) p.2).target := by
  have he : modelCoordinateEquiv.symm (z.1,a+b*z.2) =
      (WithLp.toLp 2 z.1, WithLp.toLp 2 (fun _ : Fin 1 ↦ a+b*z.2)) := rfl
  change modelCoordinateEquiv.symm (z.1,a+b*z.2) ∈
    (extChartAt modelWithCorners p).target ↔ _
  rw [he]
  simp [modelWithCorners]
  rfl

lemma exists_short_circle_arc (p : Manifold5) :
    ∃ a b : ℝ, 0 < b ∧ ∀ {K : Set _root_.OAI.Yau.Jets.Coord},
      (∀ y ∈ K, WithLp.toLp 2 y ∈ (extChartAt (𝓡 4) p.1).target) →
      K ×ˢ Icc (-1:ℝ) 1 ⊆ productChartDomain p a b := by
  let e : EuclideanSpace ℝ (Fin 1) ≃L[ℝ] ℝ :=
    PiLp.equivOfUnique (p := 2) (𝕜 := ℝ) (β := fun _ : Fin 1 ↦ ℝ)
  let a := e (extChartAt (𝓡 1) p.2 p.2)
  let V := e.symm ⁻¹' (extChartAt (𝓡 1) p.2).target
  have hV : IsOpen V := (isOpen_extChartAt_target p.2).preimage e.symm.continuous
  have ha : a ∈ V := by simp [V,a]
  obtain ⟨r,hr,hball⟩ := Metric.mem_nhds_iff.mp (hV.mem_nhds ha)
  refine ⟨a,r/2,by positivity,?_⟩
  intro K hK z hz
  rw [productChartDomain_iff]
  refine ⟨hK z.1 hz.1,?_⟩
  have habs : |z.2| ≤ 1 := abs_le.mpr hz.2
  have hin : a+(r/2)*z.2 ∈ V := by
    apply hball
    rw [Metric.mem_ball,Real.dist_eq]
    have hnorm : |a+(r/2)*z.2-a| = (r/2)*|z.2| := by
      rw [add_sub_cancel_left,abs_mul,abs_of_pos (by positivity : 0 < r/2)]
    rw [hnorm]
    nlinarith
  exact hin

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_IntrinsicPairUniformBounds
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

lemma intrinsic_sphere_upper_bound (A : IntrinsicTensor) (hA : IntrinsicTensorSmooth A)
    (hs : ∀ x v w, A x v w = A x w v)
    (hp : ∀ x v, v ≠ 0 → 0 < A x v v) :
    ∃ c > 0, ∀ x v, A x v v ≤ c*roundCotangentTensor x v v := by
  let B := fun x ↦ ambientMatrixForm (intrinsicAmbientMatrix A x)
  have hB : Continuous B := (ambientMatrixForm_smooth _ (intrinsicAmbientMatrix_smooth A hA)).continuous
  have hpos (x : Base) (v : AmbientBase) (hv : v ≠ 0) : 0 < B x v v :=
    ambientMatrixForm_pos _ (intrinsicAmbientMatrix_posDef A hs hp x) v hv
  have hc : Continuous (fun z : Base × AmbientBase ↦ B z.1 z.2 z.2) :=
    ((hB.comp continuous_fst).clm_apply continuous_snd).clm_apply continuous_snd
  obtain ⟨_,_,c,hc0,hbound⟩ := compact_positive_bounds
    (isCompact_univ.prod (isCompact_sphere (0:AmbientBase) 1)) _ hc.continuousOn
    (fun z hz ↦ hpos z.1 z.2 (by intro he; simpa [he] using hz.2))
  have hb (x : Base) (v : AmbientBase) : B x v v ≤ c*‖v‖^2 := by
    by_cases hv : v = 0
    · simp [hv]
    have hn : 0 < ‖v‖ := norm_pos_iff.mpr hv
    have hu : ‖(‖v‖⁻¹:ℝ) • v‖ = 1 := by
      rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hn),inv_mul_cancel₀ hn.ne']
    have hh := (hbound (x,(‖v‖⁻¹:ℝ) • v)
      ⟨mem_univ _,by simpa only [Metric.mem_sphere,dist_zero_right] using hu⟩).2
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

lemma intrinsic_pair_uniform_bounds (A : IntrinsicTensor) (hA : IntrinsicTensorSmooth A)
    (hs : ∀ x v w, A x v w = A x w v)
    (hp : ∀ x v, v ≠ 0 → 0 < A x v v) (rho : Base → ℝ)
    (hr : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ rho) (hrp : ∀ x, 0 < rho x) :
    ∃ c > 0, ∃ B > 0, ∃ R > 0,
      (∀ x v, c*roundCotangentTensor x v v ≤ A x v v) ∧
      (∀ x v, A x v v ≤ B*roundCotangentTensor x v v) ∧
      (∀ x, c ≤ rho x) ∧ (∀ x, rho x ≤ R) := by
  obtain ⟨c,hc,hlo,hrlo⟩ := intrinsic_pair_positive_margin A hA hs hp rho hr hrp
  obtain ⟨B,hB,hhi⟩ := intrinsic_sphere_upper_bound A hA hs hp
  obtain ⟨_,_,R,hR,hb⟩ := compact_positive_bounds isCompact_univ rho hr.continuous.continuousOn
    (fun x _ ↦ hrp x)
  exact ⟨c,hc,B,hB,R,hR,hlo,hhi,hrlo,fun x ↦ (hb x (mem_univ _)).2⟩

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

lemma roundTensorPerturbation_tangent (alpha : Base → ℝ) (x : Base) (v w : AmbientBase)
    (hv : ⟪(x:AmbientBase),v⟫ = 0) (hw : ⟪(x:AmbientBase),w⟫ = 0) :
    roundTensorPerturbation alpha x (sphereCovectorRestriction x v) (sphereCovectorRestriction x w) =
      alpha x * ⟪v,w⟫ := by
  rw [roundTensorPerturbation_apply,roundCotangentTensor_tangent x v w hv hw]

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Hausdorff_PerturbedNodalTransfer
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Manifold Yau.Geometry Yau.Jets Set MeasureTheory
open scoped ContDiff Topology RealInnerProductSpace ENNReal NNReal
noncomputable section
attribute [local instance] clmTopology clmAdd clmModule

local instance perturbedNodalTransferLocalInst1_r35f701_1 : NormedAddCommGroup CotangentModel := ContinuousLinearMap.toNormedAddCommGroup
local instance perturbedNodalTransferLocalInst2_r35f701_1 : NormedSpace ℝ CotangentModel := ContinuousLinearMap.toNormedSpace
local instance perturbedNodalTransferLocalInst3_r35f701_1 : NormedAddCommGroup (CotangentModel →L[ℝ] ℝ) := ContinuousLinearMap.toNormedAddCommGroup
local instance perturbedNodalTransferLocalInst4_r35f701_1 : NormedSpace ℝ (CotangentModel →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace
local instance perturbedNodalTransferLocalInst5_r35f701_1 : NormedAddCommGroup (CotangentModel →L[ℝ] CotangentModel →L[ℝ] ℝ) := ContinuousLinearMap.toNormedAddCommGroup
local instance perturbedNodalTransferLocalInst6_r35f701_1 : NormedSpace ℝ (CotangentModel →L[ℝ] CotangentModel →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace
attribute [local instance] OAI.Yau.Target.perturbedNodalTransferLocalInst7
attribute [local instance] OAI.Yau.Target.perturbedNodalTransferLocalInst8
attribute [local instance] OAI.Yau.Target.perturbedNodalTransferLocalInst9
local instance perturbedNodalTransferLocalInst10_r35f701_1 (x : Base) : Module ℝ (SphereCotangent x →L[ℝ] ℝ) := ContinuousLinearMap.module
attribute [local instance] OAI.Yau.Target.perturbedNodalTransferLocalInst11
local instance perturbedNodalTransferLocalInst12_r35f701_1 (x : Base) : ContinuousSMul ℝ (SphereCotangent x →L[ℝ] ℝ) := ContinuousLinearMap.continuousSMul
local instance perturbedNodalTransferLocalInst13_r35f701_1 (x : Base) : TopologicalSpace (SphereCotangent x →L[ℝ] ℝ) := ContinuousLinearMap.topologicalSpace
local instance perturbedNodalTransferLocalInst14_r35f701_1 : TopologicalSpace (Bundle.TotalSpace (CotangentModel →L[ℝ] CotangentModel →L[ℝ] ℝ)
    (fun x : Base ↦ SphereCotangent x →L[ℝ] SphereCotangent x →L[ℝ] ℝ)) :=
  Bundle.ContinuousLinearMap.topologicalSpaceTotalSpace (RingHom.id ℝ) CotangentModel SphereCotangent
    (CotangentModel →L[ℝ] ℝ) (fun x : Base ↦ SphereCotangent x →L[ℝ] ℝ)
local instance perturbedNodalTransferLocalInst15_r35f701_1 (x : Base) : AddCommGroup (SphereCotangent x →L[ℝ] SphereCotangent x →L[ℝ] ℝ) := ContinuousLinearMap.addCommGroup
local instance perturbedNodalTransferLocalInst16_r35f701_1 (x : Base) : Module ℝ (SphereCotangent x →L[ℝ] SphereCotangent x →L[ℝ] ℝ) := ContinuousLinearMap.module
lemma small_round_correction_bounds (A : IntrinsicTensor) (rho alpha beta : Base → ℝ)
    {c B R : ℝ}
    (hlo : ∀ x v, c*roundCotangentTensor x v v ≤ A x v v)
    (hhi : ∀ x v, A x v v ≤ B*roundCotangentTensor x v v)
    (hrlo : ∀ x, c ≤ rho x) (hrhi : ∀ x, rho x ≤ R)
    (ha : ∀ x, |alpha x| ≤ min (c/2) 1) (hb : ∀ x, |beta x| ≤ min (c/2) 1) :
    (∀ (x : Base) (v : AmbientBase), ⟪(x:AmbientBase),v⟫ = 0 →
      (c/2)*‖v‖^2 ≤ (A x+roundTensorPerturbation alpha x)
        (sphereCovectorRestriction x v) (sphereCovectorRestriction x v)) ∧
    (∀ (x : Base) (v : AmbientBase), ⟪(x:AmbientBase),v⟫ = 0 →
      (A x+roundTensorPerturbation alpha x)
        (sphereCovectorRestriction x v) (sphereCovectorRestriction x v) ≤ (B+1)*‖v‖^2) ∧
    (∀ x, c/2 ≤ rho x+beta x) ∧ (∀ x, rho x+beta x ≤ R+1) := by
  have hab (x : Base) := abs_le.mp (ha x)
  have hbb (x : Base) := abs_le.mp (hb x)
  refine ⟨?_,?_,?_,?_⟩
  · intro x v hv
    have hh := hlo x (sphereCovectorRestriction x v)
    rw [roundCotangentTensor_tangent x v v hv hv,real_inner_self_eq_norm_sq] at hh
    change _ ≤ A x _ _ + roundTensorPerturbation alpha x _ _
    rw [roundTensorPerturbation_tangent alpha x v v hv hv,real_inner_self_eq_norm_sq]
    have hal : -(c/2) ≤ alpha x := (neg_le_neg (min_le_left _ _)).trans (hab x).1
    nlinarith [mul_le_mul_of_nonneg_right hal (sq_nonneg ‖v‖)]
  · intro x v hv
    have hh := hhi x (sphereCovectorRestriction x v)
    rw [roundCotangentTensor_tangent x v v hv hv,real_inner_self_eq_norm_sq] at hh
    change A x _ _ + roundTensorPerturbation alpha x _ _ ≤ _
    rw [roundTensorPerturbation_tangent alpha x v v hv hv,real_inner_self_eq_norm_sq]
    have hal : alpha x ≤ 1 := (hab x).2.trans (min_le_right _ _)
    nlinarith [mul_le_mul_of_nonneg_right hal (sq_nonneg ‖v‖)]
  · intro x
    have hh := (neg_le_neg (min_le_left (c/2) 1)).trans (hbb x).1
    linarith [hrlo x]
  · intro x
    have hh := (hbb x).2.trans (min_le_right (c/2) 1)
    linarith [hrhi x]

lemma circleLift_productChartInverse (f : Base → ℝ) (a b : ℝ) (q : Circle) (z : _root_.OAI.Yau.Jets.Coord × ℝ) :
    circleLift f (productChartInverse (seedPoint,q) a b z) = f (seedSphereFromCoord z.1) := by
  unfold circleLift productChartInverse
  rw [extChartAt_prod]
  rfl

theorem uniform_small_correction_nodal_transfer_oai (A : IntrinsicTensor) (hA : IntrinsicTensorSmooth A)
    (hs : ∀ x v w, A x v w = A x w v)
    (hp : ∀ x v, v ≠ 0 → 0 < A x v v) (rho : Base → ℝ)
    (hr : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ rho) (hrp : ∀ x, 0 < rho x)
    {H : Set _root_.OAI.Yau.Jets.Coord} (hH : IsCompact H) :
    ∃ eta > 0, ∃ C : ℝ≥0, 0 < C ∧
      ∀ (alpha beta : Base → ℝ)
        (hnew : IntrinsicTensorSmooth (fun x ↦ A x+roundTensorPerturbation alpha x))
        (hnewSym : ∀ x v w, (A x+roundTensorPerturbation alpha x) v w =
          (A x+roundTensorPerturbation alpha x) w v)
        (hnewPos : ∀ x v, v ≠ 0 → 0 < (A x+roundTensorPerturbation alpha x) v v)
        (hrnew : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ (fun x ↦ rho x+beta x))
        (hrnewPos : ∀ x, 0 < rho x+beta x),
        (∀ x, |alpha x| ≤ eta) → (∀ x, |beta x| ≤ eta) →
        ∀ (u : _root_.OAI.Yau.Jets.Coord → ℝ) (ug : Base → ℝ) (U : Set _root_.OAI.Yau.Jets.Coord), U ⊆ H →
          (∀ x, ug (seedSphereFromCoord x) = u x) →
          Measure.hausdorffMeasure (4:ℝ) ((U ×ˢ Icc (-1:ℝ) 1) ∩ {z : _root_.OAI.Yau.Jets.Coord × ℝ | u z.1 = 0}) ≤
            (C:ℝ≥0∞)^4 * nodalMeasure
              (intrinsicWeightedMetric (fun x ↦ A x+roundTensorPerturbation alpha x) hnew hnewSym hnewPos
                (fun x ↦ rho x+beta x) hrnew hrnewPos) (circleLift ug) := by
  obtain ⟨c,hc,B,hB,R,hR,hlo,hhi,hrlo,hrhi⟩ := intrinsic_pair_uniform_bounds A hA hs hp rho hr hrp
  obtain ⟨a,b,hb,hchart⟩ := exists_short_circle_arc (seedPoint,(1:Circle))
  obtain ⟨C,hC,htransfer⟩ := uniform_intrinsic_coefficient_nodal_transfer
    (c/2) (B+1) (c/2) (R+1) (by positivity) (by positivity) (by positivity) (by positivity)
    (seedPoint,(1:Circle)) a hb.ne' (hH.prod isCompact_Icc)
    (hchart (fun y hy ↦ by rw [centeredSphereChart_target]; trivial))
  refine ⟨min (c/2) 1,by positivity,C,hC,?_⟩
  intro alpha beta hnew hnewSym hnewPos hrnew hrnewPos ha hb u ug U hUH he
  obtain ⟨hblo,hbhi,hbrlo,hbrhi⟩ := small_round_correction_bounds A rho alpha beta hlo hhi hrlo hrhi ha hb
  apply htransfer _ hnew hnewSym hnewPos _ hrnew hrnewPos hblo hbhi hbrlo hbrhi
  · rintro z ⟨hz,hzero⟩
    exact ⟨hUH hz.1,hz.2⟩
  · rintro z ⟨hz,hzero⟩
    rw [circleLift_productChartInverse,he]
    exact hzero

end
end Yau.Target

end OAI
end

theorem solution : type_of% @OAI.Yau.Target.uniform_small_correction_nodal_transfer_oai := @OAI.Yau.Target.uniform_small_correction_nodal_transfer_oai
