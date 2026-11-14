-- Prove2me | solution 1 for OAI.WeakPureInfiniteness.freeDiagonalFunctional_bound_of_kernel
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T07:20:10.319248+00:00
-- url     : https://prove2.me/submissions/e8aceace-89d6-4544-afbc-b70c9ed5c468

import Mathlib
import Definitions.Def_ExactInfiniteness
import Definitions.Def_OAIQ246W003
import Definitions.Def_OAIQ246W004

section
-- module Solutions.OAIQ246_WI.Compat
attribute [-instance] _root_.OAI.WeakPureInfiniteness.uliftCStarAlgebra _root_.OAI.WeakPureInfiniteness.uliftInnerProduct _root_.OAI.WeakPureInfiniteness.uliftStarRing
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem ite_eq_right {α : Sort _} {c : Prop} {_ : Decidable c} {a b : α} (h : ¬c) :
    (if c then a else b) = b := if_neg h
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ246_WI.WeakInfiniteness_FellAbsorption
attribute [-instance] _root_.OAI.WeakPureInfiniteness.completedTensorCStar _root_.OAI.WeakPureInfiniteness.groupHilbertNontrivial _root_.OAI.WeakPureInfiniteness.hilbertOperatorsCStar _root_.OAI.WeakPureInfiniteness.instCStarAlgebraReducedGroupAlgebra _root_.OAI.WeakPureInfiniteness.uliftCStarAlgebra _root_.OAI.WeakPureInfiniteness.uliftInnerProduct _root_.OAI.WeakPureInfiniteness.uliftStarRing
attribute [-simp] _root_.OAI.WeakPureInfiniteness.tensorSequence_apply _root_.OAI.WeakPureInfiniteness.tensorToHilbertSumMap_tmul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct ENNReal ComplexOrder
open UniformSpace
open CStarAlgebra
open scoped NNReal
open scoped TensorProduct ComplexConjugate
open scoped ENNReal InnerProductSpace
open scoped InnerProductSpace
open scoped TensorProduct InnerProductSpace

namespace WeakPureInfiniteness.HilbertValued

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable {G K : Type*}

section SchurBound

variable {X I : Type*} [Fintype I]

omit [InnerProductSpace ℂ H] [CompleteSpace H] in
lemma l2_summable_norm_sq (ξ : HilbertSum X H) : Summable (fun x => ‖ξ x‖ ^ 2) := by
  have h := Memℓp.summable (by norm_num : (0 : ℝ) < (2 : ℝ≥0∞).toReal) ξ.property
  norm_num at h
  exact h

omit [InnerProductSpace ℂ H] [CompleteSpace H] in
lemma l2_norm_sq (ξ : HilbertSum X H) : ‖ξ‖ ^ 2 = ∑' x, ‖ξ x‖ ^ 2 := by
  have h := lp.norm_rpow_eq_tsum (by norm_num : (0 : ℝ) < (2 : ℝ≥0∞).toReal) ξ
  norm_num at h
  exact h

lemma weighted_two_mul_le (a b w : ℝ) (hw : 0 < w) :
    2 * a * b ≤ w * a ^ 2 + w⁻¹ * b ^ 2 := by
  have h := sq_nonneg (w * a - b)
  have hi : w * w⁻¹ = 1 := mul_inv_cancel₀ hw.ne'
  apply (mul_le_mul_iff_right₀ hw).mp
  nlinarith

omit [InnerProductSpace ℂ H] [CompleteSpace H] in
lemma weighted_squares_summable (w : X → ℝ) (hw : ∀ x, 0 < w x)
    (e : I → X ≃ X) (C : ℝ)
    (hrow : ∀ x, ∑ i, w ((e i).symm x) / w x ≤ C)
    (ξ : HilbertSum X H) (i : I) :
    Summable (fun x => (w ((e i).symm x) / w x) * ‖ξ x‖ ^ 2) := by
  apply Summable.of_nonneg_of_le
    (fun x => mul_nonneg (div_nonneg (hw _).le (hw _).le) (sq_nonneg _))
    (fun x => mul_le_mul_of_nonneg_right
      ((Finset.single_le_sum (fun j _ => div_nonneg (hw _).le (hw _).le)
        (Finset.mem_univ i)).trans (hrow x)) (sq_nonneg _))
    ((l2_summable_norm_sq ξ).mul_left C)

omit [InnerProductSpace ℂ H] [CompleteSpace H] in
lemma weighted_squares_sum_le (w : X → ℝ) (hw : ∀ x, 0 < w x)
    (e : I → X ≃ X) (C : ℝ)
    (hrow : ∀ x, ∑ i, w ((e i).symm x) / w x ≤ C)
    (ξ : HilbertSum X H) :
    ∑ i, ∑' x, (w ((e i).symm x) / w x) * ‖ξ x‖ ^ 2 ≤ C * ‖ξ‖ ^ 2 := by
  have hs (i : I) := weighted_squares_summable w hw e C hrow ξ i
  rw [← Summable.tsum_finsetSum (fun i _ => hs i)]
  simp_rw [← Finset.sum_mul]
  rw [l2_norm_sq ξ, ← tsum_mul_left]
  apply Summable.tsum_le_tsum
    (fun x => mul_le_mul_of_nonneg_right (hrow x) (sq_nonneg _))
  · simpa only [Finset.sum_mul] using summable_sum (fun i _ => hs i)
  · exact (l2_summable_norm_sq ξ).mul_left C

omit [CompleteSpace H] in
theorem norm_permutationSum_le (w : X → ℝ) (hw : ∀ x, 0 < w x)
    (e : I → X ≃ X) (C : ℝ) (hC : 0 ≤ C)
    (hrow : ∀ x, ∑ i, w ((e i).symm x) / w x ≤ C)
    (hcol : ∀ x, ∑ i, w (e i x) / w x ≤ C) :
    ‖permutationSum (H := H) e‖ ≤ C := by
  classical
  apply ContinuousLinearMap.opNorm_le_of_re_inner_le hC
  intro ξ η hξ hη
  have hs₁ (i : I) := weighted_squares_summable w hw e C hrow η i
  have hs₂ (i : I) : Summable (fun x =>
      (w x / w ((e i).symm x)) * ‖ξ ((e i).symm x)‖ ^ 2) := by
    have h := weighted_squares_summable w hw (fun i => (e i).symm) C hcol ξ i
    convert (e i).symm.summable_iff.mpr h using 1
    all_goals try with_reducible_and_instances rfl
    ext x
    simp
  have hpoint (i : I) (x : X) :
      2 * (inner ℂ (ξ ((e i).symm x)) (η x)).re ≤
        (w ((e i).symm x) / w x) * ‖η x‖ ^ 2 +
        (w x / w ((e i).symm x)) * ‖ξ ((e i).symm x)‖ ^ 2 := by
    have hr := (Complex.re_le_norm (inner ℂ (ξ ((e i).symm x)) (η x))).trans
      (norm_inner_le_norm (ξ ((e i).symm x)) (η x))
    have he := weighted_two_mul_le ‖η x‖ ‖ξ ((e i).symm x)‖
      (w ((e i).symm x) / w x) (div_pos (hw _) (hw _))
    rw [inv_div] at he
    nlinarith
  have hi (i : I) :
      2 * (inner ℂ (l2Reindex (e i) ξ) η).re ≤
        (∑' x, (w ((e i).symm x) / w x) * ‖η x‖ ^ 2) +
        (∑' x, (w x / w ((e i).symm x)) * ‖ξ ((e i).symm x)‖ ^ 2) := by
    have hin := lp.summable_inner (𝕜 := ℂ) (l2Reindex (e i) ξ) η
    have hre := (Complex.reCLM.hasSum hin.hasSum).summable
    have hret : (inner ℂ (l2Reindex (e i) ξ) η).re =
        ∑' x, (inner ℂ (ξ ((e i).symm x)) (η x)).re := by
      exact Complex.reCLM.map_tsum hin
    rw [hret, ← tsum_mul_left, ← (hs₁ i).tsum_add (hs₂ i)]
    exact Summable.tsum_le_tsum (hpoint i) (hre.mul_left 2) ((hs₁ i).add (hs₂ i))
  have hsecond :
      (∑ i, ∑' x, (w x / w ((e i).symm x)) * ‖ξ ((e i).symm x)‖ ^ 2) =
      (∑ i, ∑' x, (w (e i x) / w x) * ‖ξ x‖ ^ 2) := by
    apply Finset.sum_congr rfl
    intro i _
    convert (e i).symm.tsum_eq (fun x => (w (e i x) / w x) * ‖ξ x‖ ^ 2) using 1
    all_goals try with_reducible_and_instances rfl
    simp
  have htotal := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hi i)
  rw [Finset.sum_add_distrib, hsecond] at htotal
  have hb₁ := weighted_squares_sum_le w hw e C hrow η
  have hb₂ := weighted_squares_sum_le w hw (fun i => (e i).symm) C hcol ξ
  simp only [Equiv.symm_symm] at hb₂
  have heval : (inner ℂ (permutationSum e ξ) η).re =
      ∑ i, (inner ℂ (l2Reindex (e i) ξ) η).re := by
    simp [permutationSum]
  change (inner ℂ (permutationSum e ξ) η).re ≤ C
  rw [heval]
  rw [← Finset.mul_sum] at htotal
  simp only [hξ, hη, one_pow, mul_one] at hb₁ hb₂
  nlinarith

end SchurBound

variable [Group G]

theorem fell_intertwines (π : G →* H ≃ₗᵢ[ℂ] H) (s : G) :
    (fellUnitary π).conjStarAlgEquiv
      (l2Reindex (Equiv.mulLeft s)).toContinuousLinearEquiv.toContinuousLinearMap =
      twistedRegular π s := by
  ext ξ g
  change π g ((π (s⁻¹ * g)).symm (ξ (s⁻¹ * g))) = π s (ξ (s⁻¹ * g))
  have he : (π g) * (π (s⁻¹ * g))⁻¹ = π s := by
    rw [← map_inv, ← map_mul]
    simp
  exact congrArg (fun f : H ≃ₗᵢ[ℂ] H => f (ξ (s⁻¹ * g))) he

theorem norm_twistedRegular_sum {I : Type*} (s : I → G) (F : Finset I)
    (π : G →* H ≃ₗᵢ[ℂ] H) :
    ‖∑ i ∈ F, twistedRegular π (s i)‖ =
      ‖∑ i ∈ F, (l2Reindex (H := H) (Equiv.mulLeft (s i))).toContinuousLinearEquiv.toContinuousLinearMap‖ := by
  simp_rw [← fell_intertwines π]
  rw [← map_sum]
  exact NonUnitalStarAlgHom.norm_map
    ((fellUnitary π).conjStarAlgEquiv.toStarAlgHom.toNonUnitalStarAlgHom)
    (fellUnitary π).conjStarAlgEquiv.injective _

end WeakPureInfiniteness.HilbertValued
end

end OAI
end

section
-- module Solutions.OAIQ246_WI.WeakInfiniteness_FiniteDiagonalState
attribute [-instance] _root_.OAI.WeakPureInfiniteness.uliftCStarAlgebra _root_.OAI.WeakPureInfiniteness.uliftInnerProduct _root_.OAI.WeakPureInfiniteness.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct ENNReal ComplexOrder
open UniformSpace
open CStarAlgebra
open scoped NNReal
open scoped TensorProduct ComplexConjugate

namespace WeakPureInfiniteness

lemma tensor_inner_smul_smul {E K : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    (x y : E ⊗[ℂ] K) (c : ℂ) :
    inner ℂ (c • x) (c • y) = star c * c * inner ℂ x y := by
  calc
    _ = star c * inner ℂ x (c • y) := inner_smul_left x (c • y) c
    _ = star c * (c * inner ℂ x y) := congrArg (star c * ·) (inner_smul_right x y c)
    _ = _ := by ring

variable (F : Type*) [Group F] [Fintype F] [DecidableEq F]

lemma inner_finiteDiagonalVector_translate (s t : F) :
    inner ℂ (finiteDiagonalVector F)
      (TensorProduct.mapL (finiteLeftRegular F s : EuclideanSpace ℂ F →L[ℂ] EuclideanSpace ℂ F)
        (finiteLeftRegular F t : EuclideanSpace ℂ F →L[ℂ] EuclideanSpace ℂ F)
        (finiteDiagonalVector F)) = if s = t then (Fintype.card F : ℂ) else 0 := by
  classical
  simp only [finiteDiagonalVector, map_sum, TensorProduct.mapL_tmul,
    finiteLeftRegular_single, inner_sum, sum_inner, TensorProduct.inner_tmul,
    EuclideanSpace.inner_single_left, map_one, one_mul, PiLp.single_apply]
  by_cases hst : s = t
  · subst t
    simp
  · rw [ite_eq_right hst]
    apply Finset.sum_eq_zero
    intro g _
    apply Finset.sum_eq_zero
    intro h _
    by_cases hg : h = s * g
    · simp [hg, hst]
    · simp [hg]

lemma normalizedFiniteDiagonalVector_inner_translate (s t : F) :
    inner ℂ (normalizedFiniteDiagonalVector F)
      (TensorProduct.mapL (finiteLeftRegular F s : EuclideanSpace ℂ F →L[ℂ] EuclideanSpace ℂ F)
        (finiteLeftRegular F t : EuclideanSpace ℂ F →L[ℂ] EuclideanSpace ℂ F)
        (normalizedFiniteDiagonalVector F)) = if s = t then 1 else 0 := by
  classical
  have hc : (Fintype.card F : ℝ) > 0 := by exact_mod_cast Fintype.card_pos
  have hs : Real.sqrt (Fintype.card F : ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hc)
  have hsq : (Real.sqrt (Fintype.card F : ℝ) : ℂ) ^ 2 = (Fintype.card F : ℂ) := by
    exact_mod_cast Real.sq_sqrt hc.le
  let c : ℂ := (Real.sqrt (Fintype.card F : ℝ) : ℂ)⁻¹
  let T := TensorProduct.mapL
    (finiteLeftRegular F s : EuclideanSpace ℂ F →L[ℂ] EuclideanSpace ℂ F)
    (finiteLeftRegular F t : EuclideanSpace ℂ F →L[ℂ] EuclideanSpace ℂ F)
  have hi := tensor_inner_smul_smul (finiteDiagonalVector F) (T (finiteDiagonalVector F)) c
  have ht := inner_finiteDiagonalVector_translate F s t
  change inner ℂ (c • finiteDiagonalVector F) (T (c • finiteDiagonalVector F)) = _
  rw [map_smul]
  calc
    _ = star c * c * inner ℂ (finiteDiagonalVector F) (T (finiteDiagonalVector F)) := hi
    _ = star c * c * (if s = t then (Fintype.card F : ℂ) else 0) :=
      congrArg (star c * c * ·) ht
    _ = _ := by
      simp only [c, star_inv₀, Complex.star_def, Complex.conj_ofReal]
      by_cases hst : s = t
      · simp only [ite_eq_left hst]
        rw [← hsq]
        have hsc : (Real.sqrt (Fintype.card F : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hs
        field_simp
      · simp [hst]

lemma norm_normalizedFiniteDiagonalVector : ‖normalizedFiniteDiagonalVector F‖ = 1 := by
  have h : inner ℂ (normalizedFiniteDiagonalVector F) (normalizedFiniteDiagonalVector F) = 1 := by
    simpa using normalizedFiniteDiagonalVector_inner_translate F 1 1
  calc
    _ = Real.sqrt (Complex.re (inner ℂ (normalizedFiniteDiagonalVector F)
      (normalizedFiniteDiagonalVector F))) :=
      norm_eq_sqrt_re_inner (𝕜 := ℂ) (normalizedFiniteDiagonalVector F)
    _ = 1 := by rw [h]; simp

end WeakPureInfiniteness
end

end OAI
end

section
-- module Solutions.OAIQ246_WI.WeakInfiniteness_SpatialVectorStates
attribute [-instance] _root_.OAI.WeakPureInfiniteness.crossTensorGraphCStar _root_.OAI.WeakPureInfiniteness.instCoeFunContractionAmbientForallContinuousLinearMapComplexIdCarrierHilbert _root_.OAI.WeakPureInfiniteness.instCoeFunFullGroupAmbientForallContinuousLinearMapComplexIdCarrierHilbert _root_.OAI.WeakPureInfiniteness.uliftCStarAlgebra _root_.OAI.WeakPureInfiniteness.uliftInnerProduct _root_.OAI.WeakPureInfiniteness.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct ENNReal ComplexOrder
open UniformSpace
open CStarAlgebra
open scoped NNReal

namespace WeakPureInfiniteness

universe u v

section SpatialVectorStates

variable {A : Type u} {B : Type v} [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]

lemma norm_spatialVectorFunctional_le (π : SpatialRepresentation A B) (ξ : π.space) :
    ‖spatialVectorFunctional π ξ‖ ≤ ‖ξ‖ * ‖ξ‖ :=
  LinearMap.mkContinuous_norm_le _ (mul_self_nonneg _) _

end SpatialVectorStates

end WeakPureInfiniteness
end

end OAI
end

section
-- module Solutions.OAIQ246_WI.WeakInfiniteness_FiniteGroupTensor
attribute [-instance] _root_.OAI.WeakPureInfiniteness.crossTensorGraphCStar _root_.OAI.WeakPureInfiniteness.instCStarAlgebraReducedGroupAlgebra _root_.OAI.WeakPureInfiniteness.instCoeFunContractionAmbientForallContinuousLinearMapComplexIdCarrierHilbert _root_.OAI.WeakPureInfiniteness.uliftCStarAlgebra _root_.OAI.WeakPureInfiniteness.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u

noncomputable section
open scoped TensorProduct ENNReal ComplexOrder
open UniformSpace
open CStarAlgebra
open scoped NNReal
open scoped TensorProduct ComplexConjugate

namespace WeakPureInfiniteness

section TensorConjugation

variable {H K L M : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  [NormedAddCommGroup L] [InnerProductSpace ℂ L] [CompleteSpace L]
  [NormedAddCommGroup M] [InnerProductSpace ℂ M] [CompleteSpace M]

lemma tensor_map_conj (e : H ≃ₗᵢ[ℂ] L) (f : K ≃ₗᵢ[ℂ] M)
    (S : H →L[ℂ] H) (T : K →L[ℂ] K) (ξ : H ⊗[ℂ] K) :
    TensorProduct.mapL (e.conjStarAlgEquiv S) (f.conjStarAlgEquiv T)
      (TensorProduct.congrIsometry e f ξ) =
      TensorProduct.congrIsometry e f (TensorProduct.mapL S T ξ) := by
  induction ξ using OAI.tensorInductionOn with
  | tmul x y => simp
  | add x y hx hy => simp only [map_add, hx, hy]

end TensorConjugation

section FiniteGroupSpatial

variable {G F : Type u} [Group G] [Group F] [Fintype F] [DecidableEq F]

lemma norm_finiteGroupSpatialDiagonal (q : G →* F) : ‖finiteGroupSpatialDiagonal q‖ = 1 := by
  unfold finiteGroupSpatialDiagonal
  exact (LinearIsometryEquiv.norm_map _ _).trans (norm_normalizedFiniteDiagonalVector F)

lemma finiteGroupSpatialDiagonal_coefficient (q : G →* F) (s t : G) :
    spatialVectorFunctional (finiteGroupSpatialRepresentation q)
      (finiteGroupSpatialDiagonal q : Completion
        (ULift.{u+1} (EuclideanSpace ℂ F) ⊗[ℂ] ULift.{u+1} (EuclideanSpace ℂ F)))
      (spatialElementary (fullGroupElement s) (fullGroupElement t)) =
      if q s = q t then (1 : ℂ) else 0 := by
  rw [spatialVectorFunctional_elementary]
  change inner ℂ (TensorProduct.congrIsometry
    (LinearIsometryEquiv.ulift ℂ (EuclideanSpace ℂ F)).symm
    (LinearIsometryEquiv.ulift ℂ (EuclideanSpace ℂ F)).symm (normalizedFiniteDiagonalVector F)) (TensorProduct.mapL
    ((LinearIsometryEquiv.ulift ℂ (EuclideanSpace ℂ F)).symm.conjStarAlgEquiv (finiteLeftRegular F (q s)))
    ((LinearIsometryEquiv.ulift ℂ (EuclideanSpace ℂ F)).symm.conjStarAlgEquiv (finiteLeftRegular F (q t)))
    (TensorProduct.congrIsometry
      (LinearIsometryEquiv.ulift ℂ (EuclideanSpace ℂ F)).symm
      (LinearIsometryEquiv.ulift ℂ (EuclideanSpace ℂ F)).symm (normalizedFiniteDiagonalVector F))) = _
  rw [tensor_map_conj]
  exact (LinearIsometryEquiv.inner_map_map ..).trans
    (normalizedFiniteDiagonalVector_inner_translate F (q s) (q t))

end FiniteGroupSpatial

end WeakPureInfiniteness
end

end OAI
end

section
-- module Solutions.OAIQ246_WI.WeakInfiniteness_FreeFiniteQuotients
attribute [-instance] _root_.OAI.WeakPureInfiniteness.uliftCStarAlgebra _root_.OAI.WeakPureInfiniteness.uliftInnerProduct _root_.OAI.WeakPureInfiniteness.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct ENNReal ComplexOrder
open UniformSpace
open CStarAlgebra
open scoped NNReal
open scoped TensorProduct ComplexConjugate

namespace WeakPureInfiniteness

open FreeGroup

variable {α : Type*} [Fintype α] [DecidableEq α]

lemma freeBallTranslation_apply (m : ℕ) (a : α) (x : freeWordBall (α := α) m)
    (hx : FreeGroup.of a * x.val ∈ freeWordBall m) :
    (freeBallTranslation m a x).val = FreeGroup.of a * x.val :=
  (exists_freeBallTranslation m a).choose_spec x hx

lemma freeBallTranslation_inv_apply (m : ℕ) (a : α) (x : freeWordBall (α := α) m)
    (hx : (FreeGroup.of a)⁻¹ * x.val ∈ freeWordBall m) :
    ((freeBallTranslation m a)⁻¹ x).val = (FreeGroup.of a)⁻¹ * x.val := by
  let y : freeWordBall (α := α) m := ⟨(FreeGroup.of a)⁻¹ * x.val, hx⟩
  have hy : freeBallTranslation m a y = x := by
    apply Subtype.ext
    rw [freeBallTranslation_apply]
    · simp [y]
    · simp [y, x.property]
  have hiy := congrArg (freeBallTranslation m a).symm hy
  simp only [Equiv.symm_apply_apply] at hiy
  exact congrArg Subtype.val hiy.symm

lemma freeFiniteQuotient_of (m : ℕ) (a : α) :
    freeFiniteQuotient m (FreeGroup.of a) = freeBallTranslation m a := by
  simp [freeFiniteQuotient]

omit [Fintype α] [DecidableEq α] in
lemma free_mk_cons_pos (a : α) (w : List (α × Bool)) :
    FreeGroup.mk ((a, true) :: w) = FreeGroup.of a * FreeGroup.mk w := rfl

omit [Fintype α] [DecidableEq α] in
lemma free_mk_cons_neg (a : α) (w : List (α × Bool)) :
    FreeGroup.mk ((a, false) :: w) = (FreeGroup.of a)⁻¹ * FreeGroup.mk w := rfl

lemma freeFiniteQuotient_word_apply (m : ℕ) (w : List (α × Bool)) (hw : w.length ≤ m) :
    (freeFiniteQuotient m (FreeGroup.mk w) ⟨1, one_mem_freeWordBall m⟩).val =
      FreeGroup.mk w := by
  induction w with
  | nil => simp [← FreeGroup.one_eq_mk]
  | cons x w ih =>
    have hw' : w.length ≤ m := (Nat.le_succ w.length).trans hw
    have ih' := ih hw'
    have hmem : FreeGroup.mk (x :: w) ∈ freeWordBall (α := α) m :=
      (mem_freeWordBall _ _).mpr (FreeGroup.norm_mk_le.trans hw)
    rcases x with ⟨a, b⟩
    cases b
    · rw [free_mk_cons_neg] at hmem ⊢
      simp only [_root_.map_mul, _root_.map_inv, freeFiniteQuotient_of, Equiv.Perm.coe_mul,
        Function.comp_apply]
      rw [freeBallTranslation_inv_apply, ih']
      simpa only [ih'] using hmem
    · rw [free_mk_cons_pos] at hmem ⊢
      simp only [_root_.map_mul, freeFiniteQuotient_of, Equiv.Perm.coe_mul, Function.comp_apply]
      rw [freeBallTranslation_apply, ih']
      simpa only [ih'] using hmem

lemma freeFiniteQuotient_apply_base (m : ℕ) (g : FreeGroup α) (hg : g ∈ freeWordBall m) :
    (freeFiniteQuotient m g ⟨1, one_mem_freeWordBall m⟩).val = g := by
  have hw := freeFiniteQuotient_word_apply m g.toWord ((mem_freeWordBall g m).mp hg)
  simpa only [FreeGroup.mk_toWord] using hw

lemma freeFiniteQuotient_injOn_ball (m : ℕ) :
    Set.InjOn (freeFiniteQuotient (α := α) m) (↑(freeWordBall (α := α) m) : Set (FreeGroup α)) := by
  intro x hx y hy h
  have he := congrArg (fun σ : Equiv.Perm (freeWordBall (α := α) m) =>
    (σ ⟨1, one_mem_freeWordBall m⟩).val) h
  simpa only [freeFiniteQuotient_apply_base m x hx,
    freeFiniteQuotient_apply_base m y hy] using he

lemma freeFiniteQuotient_injOn_finset (S : Finset (FreeGroup α)) :
    ∃ m : ℕ, Set.InjOn (freeFiniteQuotient (α := α) m) (↑S : Set (FreeGroup α)) := by
  refine ⟨S.sup FreeGroup.norm, fun x hx y hy h => ?_⟩
  apply freeFiniteQuotient_injOn_ball _ ?_ ?_ h
  · exact (mem_freeWordBall _ _).mpr (Finset.le_sup hx)
  · exact (mem_freeWordBall _ _).mpr (Finset.le_sup hy)

end WeakPureInfiniteness
end

end OAI
end

section
-- module Solutions.OAIQ246_WI.WeakInfiniteness_FreeTwistedNorm
attribute [-instance] _root_.OAI.WeakPureInfiniteness.groupHilbertNontrivial _root_.OAI.WeakPureInfiniteness.instCStarAlgebraReducedGroupAlgebra _root_.OAI.WeakPureInfiniteness.uliftCStarAlgebra _root_.OAI.WeakPureInfiniteness.uliftInnerProduct _root_.OAI.WeakPureInfiniteness.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct ENNReal ComplexOrder
open UniformSpace
open CStarAlgebra
open scoped NNReal
open scoped TensorProduct ComplexConjugate
open scoped ENNReal InnerProductSpace
open scoped InnerProductSpace
open scoped TensorProduct InnerProductSpace

namespace WeakPureInfiniteness

lemma toWord_freeLetter_mul (s : FreeLetter) (g : FreeTwo) :
    (freeLetter s * g).toWord =
      match g.toWord with
      | [] => [s]
      | t :: l => if s = inverseLetter t then l else s :: t :: l := by
  rw [FreeGroup.toWord_mul, toWord_freeLetter]
  simp only [List.singleton_append, FreeGroup.reduce.cons, FreeGroup.reduce_toWord]
  cases h : g.toWord with
  | nil => rfl
  | cons t l =>
    simp only [inverseLetter, Prod.ext_iff]

lemma freeTreeWeight_pos (g : FreeTwo) : 0 < freeTreeWeight g := by
  exact zpow_pos (Real.sqrt_pos.mpr (by norm_num)) _

lemma freeTreeWeight_step_nil (s : FreeLetter) {g : FreeTwo} (h : g.toWord = []) :
    freeTreeWeight (freeLetter s * g) / freeTreeWeight g = (Real.sqrt 3)⁻¹ := by
  simp [freeTreeWeight, toWord_freeLetter_mul, h]

lemma freeTreeWeight_step_cons (s t : FreeLetter) (l : List FreeLetter)
    {g : FreeTwo} (h : g.toWord = t :: l) :
    freeTreeWeight (freeLetter s * g) / freeTreeWeight g =
      if s = inverseLetter t then Real.sqrt 3 else (Real.sqrt 3)⁻¹ := by
  have hs : Real.sqrt 3 ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by norm_num))
  rw [freeTreeWeight, toWord_freeLetter_mul, h]
  unfold freeTreeWeight
  rw [h]
  by_cases he : s = inverseLetter t
  · simp only [ite_eq_left he, List.length_cons, Nat.cast_add, Nat.cast_one]
    rw [← zpow_sub₀ hs]
    convert zpow_one (Real.sqrt 3) using 1
    all_goals try with_reducible_and_instances rfl
    congr 1
    omega
  · simp only [ite_eq_right he, List.length_cons, Nat.cast_add, Nat.cast_one]
    rw [← zpow_sub₀ hs]
    convert zpow_neg_one (Real.sqrt 3) using 1
    all_goals try with_reducible_and_instances rfl
    congr 1
    omega

theorem freeTreeWeight_sum_le (g : FreeTwo) :
    ∑ s : FreeLetter, freeTreeWeight (freeLetter s * g) / freeTreeWeight g ≤
      2 * Real.sqrt 3 := by
  have hs0 : 0 < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  have hs2 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  cases h : g.toWord with
  | nil =>
    simp_rw [freeTreeWeight_step_nil _ h]
    norm_num
    have hi : Real.sqrt 3 * (Real.sqrt 3)⁻¹ = 1 := mul_inv_cancel₀ hs0.ne'
    nlinarith
  | cons t l =>
    simp_rw [freeTreeWeight_step_cons _ t l h]
    have hsum : (∑ s : FreeLetter, if s = inverseLetter t then Real.sqrt 3
        else (Real.sqrt 3)⁻¹) = Real.sqrt 3 + 3 * (Real.sqrt 3)⁻¹ := by
      rcases t with ⟨a,b⟩
      cases a <;> cases b <;> norm_num [Fintype.sum_prod_type, inverseLetter] <;> ring
    rw [hsum]
    have hi : Real.sqrt 3 * (Real.sqrt 3)⁻¹ = 1 := mul_inv_cancel₀ hs0.ne'
    nlinarith

theorem norm_freeTwisted_sum_le {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (π : FreeTwo →* H ≃ₗᵢ[ℂ] H) :
    ‖∑ s : FreeLetter, HilbertValued.twistedRegular π (freeLetter s)‖ ≤
      2 * Real.sqrt 3 := by
  rw [HilbertValued.norm_twistedRegular_sum freeLetter Finset.univ π]
  apply HilbertValued.norm_permutationSum_le freeTreeWeight freeTreeWeight_pos
    (fun s : FreeLetter => Equiv.mulLeft (freeLetter s)) (2 * Real.sqrt 3)
    (by positivity)
  · intro g
    let e : FreeLetter ≃ FreeLetter :=
      ⟨inverseLetter, inverseLetter, inverseLetter_inverseLetter, inverseLetter_inverseLetter⟩
    have he := e.sum_comp (fun s => freeTreeWeight (freeLetter s * g) / freeTreeWeight g)
    simp only [e, Equiv.coe_fn_mk, freeLetter_inverseLetter] at he
    change (∑ s : FreeLetter, freeTreeWeight ((freeLetter s)⁻¹ * g) / freeTreeWeight g) ≤ _
    rw [he]
    exact freeTreeWeight_sum_le g
  · exact freeTreeWeight_sum_le

end WeakPureInfiniteness
end

end OAI
end

section
-- module Solutions.OAIQ246_WI.WeakInfiniteness_FullGroupDensity
attribute [-instance] _root_.OAI.WeakPureInfiniteness.instCStarAlgebraReducedGroupAlgebra _root_.OAI.WeakPureInfiniteness.uliftCStarAlgebra _root_.OAI.WeakPureInfiniteness.uliftInnerProduct _root_.OAI.WeakPureInfiniteness.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct ENNReal ComplexOrder
open UniformSpace
open CStarAlgebra
open scoped NNReal

namespace WeakPureInfiniteness

universe u

section GroupPolynomialDensity

variable {G : Type u} [Group G]

lemma groupSpan_eq_adjoin : groupSpan (G := G) =
    StarAlgebra.adjoin ℂ (Set.range (fullGroupOperator (G := G))) := by
  apply le_antisymm
  · change Submodule.span ℂ (Set.range (fullGroupOperator (G := G))) ≤
      (StarAlgebra.adjoin ℂ (Set.range (fullGroupOperator (G := G)))).toSubalgebra.toSubmodule
    exact Submodule.span_le.mpr (StarAlgebra.subset_adjoin ℂ _)
  · exact StarAlgebra.adjoin_le (fun _ hx => Submodule.subset_span hx)

lemma fullGroupSubalgebra_eq_closure_span :
    (fullGroupSubalgebra G : Set (FullGroupAmbient G)) =
      closure (Submodule.span ℂ (Set.range (fullGroupOperator (G := G))) : Set (FullGroupAmbient G)) := by
  rw [fullGroupSubalgebra, closedStarSpan, ← groupSpan_eq_adjoin]
  rfl

end GroupPolynomialDensity

end WeakPureInfiniteness
end

end OAI
end

section
-- module Solutions.OAIQ246_WI.WeakInfiniteness_GroupPolynomials
attribute [-instance] _root_.OAI.WeakPureInfiniteness.instCStarAlgebraReducedGroupAlgebra _root_.OAI.WeakPureInfiniteness.uliftCStarAlgebra _root_.OAI.WeakPureInfiniteness.uliftInnerProduct _root_.OAI.WeakPureInfiniteness.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct ENNReal ComplexOrder
open UniformSpace
open CStarAlgebra
open scoped NNReal

namespace WeakPureInfiniteness

variable {G : Type*} [Group G]

lemma fullGroupPolynomial_val (c : G →₀ ℂ) :
    (fullGroupPolynomial c).val = c.sum (fun g z => z • fullGroupOperator g) := by
  simp only [fullGroupPolynomial, Finsupp.linearCombination_apply, Finsupp.sum]
  change (fullGroupAmbientInclusion (G := G)) (∑ g ∈ c.support, c g • fullGroupElement g) = _
  simp only [map_sum, map_smul]
  rfl

lemma fullGroupPolynomial_dense : DenseRange (fullGroupPolynomial (G := G)) := by
  rw [Metric.denseRange_iff]
  intro x ε hε
  have hx : x.val ∈ (fullGroupSubalgebra G : Set (FullGroupAmbient G)) := x.property
  rw [fullGroupSubalgebra_eq_closure_span] at hx
  obtain ⟨y, hy, hdist⟩ := Metric.mem_closure_iff.mp hx ε hε
  obtain ⟨c, rfl⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp hy
  refine ⟨c, ?_⟩
  rw [dist_eq_norm]
  change ‖x.val - (fullGroupPolynomial c).val‖ < ε
  rw [fullGroupPolynomial_val]
  simpa only [dist_eq_norm] using hdist

end WeakPureInfiniteness
end

end OAI
end

section
-- module Solutions.OAIQ246_WI.WeakInfiniteness_TensorHilbertSum
attribute [-instance] _root_.OAI.WeakPureInfiniteness.groupHilbertNontrivial _root_.OAI.WeakPureInfiniteness.instCStarAlgebraReducedGroupAlgebra _root_.OAI.WeakPureInfiniteness.uliftCStarAlgebra _root_.OAI.WeakPureInfiniteness.uliftInnerProduct _root_.OAI.WeakPureInfiniteness.uliftStarRing
attribute [-simp] _root_.OAI.WeakPureInfiniteness.fullToReduced_element
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct ENNReal ComplexOrder
open UniformSpace
open CStarAlgebra
open scoped NNReal
open scoped TensorProduct ComplexConjugate
open scoped ENNReal InnerProductSpace
open scoped InnerProductSpace
open scoped TensorProduct InnerProductSpace

namespace WeakPureInfiniteness

section TensorHilbertSum

variable {H G : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

variable [Group G]

lemma tensorToHilbertSum_intertwining (π : G →* H ≃ₗᵢ[ℂ] H) (s : G)
    (z : H ⊗[ℂ] GroupHilbert G) :
    tensorToHilbertSum (TensorProduct.mapL
      (π s).toContinuousLinearEquiv.toContinuousLinearMap (leftRegular s) z) =
      HilbertValued.twistedRegular π s (tensorToHilbertSum z) := by
  induction z using OAI.tensorInductionOn with
  | tmul ξ η =>
    ext g
    change (((leftRegular s : GroupHilbert G →L[ℂ] GroupHilbert G) η) g) • π s ξ =
      π s (η (s⁻¹ * g) • ξ)
    simp
  | add z w hz hw => simp only [map_add, hz, hw]

end TensorHilbertSum

theorem norm_freeTensor_sum_le {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (π : FreeTwo →* H ≃ₗᵢ[ℂ] H) :
    ‖∑ s : FreeLetter, TensorProduct.mapL
      (π (freeLetter s)).toContinuousLinearEquiv.toContinuousLinearMap
      (leftRegular (freeLetter s) : GroupHilbert FreeTwo →L[ℂ] GroupHilbert FreeTwo)‖ ≤ 2 * Real.sqrt 3 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro z
  have he : tensorToHilbertSum ((∑ s : FreeLetter, TensorProduct.mapL
      (π (freeLetter s)).toContinuousLinearEquiv.toContinuousLinearMap
      (leftRegular (freeLetter s) : GroupHilbert FreeTwo →L[ℂ] GroupHilbert FreeTwo)) z) =
      (∑ s : FreeLetter, HilbertValued.twistedRegular π (freeLetter s))
        (tensorToHilbertSum z) := by
    simp only [sum_apply, map_sum, tensorToHilbertSum_intertwining]
  rw [← (tensorToHilbertSum (H := H) (G := FreeTwo)).norm_map, he]
  exact (ContinuousLinearMap.le_opNorm _ _).trans
    (by
      simpa using mul_le_mul_of_nonneg_right (norm_freeTwisted_sum_le π)
        (norm_nonneg (tensorToHilbertSum z)))

end WeakPureInfiniteness
end

end OAI
end

section
-- module Solutions.OAIQ246_WI.WeakInfiniteness_NonUnitalGroupTensor
attribute [-instance] _root_.OAI.WeakPureInfiniteness.completedTensorCStar _root_.OAI.WeakPureInfiniteness.groupHilbertNontrivial _root_.OAI.WeakPureInfiniteness.hilbertOperatorsCStar _root_.OAI.WeakPureInfiniteness.instCStarAlgebraReducedGroupAlgebra _root_.OAI.WeakPureInfiniteness.uliftCStarAlgebra _root_.OAI.WeakPureInfiniteness.uliftInnerProduct _root_.OAI.WeakPureInfiniteness.uliftStarRing
attribute [-simp] _root_.OAI.WeakPureInfiniteness.fullToReduced_element
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct ENNReal ComplexOrder
open UniformSpace
open CStarAlgebra
open scoped NNReal
open scoped TensorProduct ComplexConjugate
open scoped ENNReal InnerProductSpace
open scoped InnerProductSpace
open scoped TensorProduct InnerProductSpace

namespace WeakPureInfiniteness

section NonUnitalGroup

variable {A B G : Type*} [CStarAlgebra A] [CStarAlgebra B] [Group G]

lemma projection_mul_completedGroup (φ : A →⋆ₙₐ[ℂ] B) (u : G →* unitary A) (g : G) :
    φ 1 * completedGroupOperator φ u g = φ (u g) := by
  simp only [completedGroupOperator, mul_add, mul_sub, mul_one, ← map_mul,
    one_mul, sub_self, add_zero]

end NonUnitalGroup

theorem norm_freeTensor_nonunital_sum_le {A H : Type*} [CStarAlgebra A]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (φ : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (u : FreeTwo →* unitary A) :
    ‖∑ s : FreeLetter, TensorProduct.mapL (φ (u (freeLetter s)))
      (leftRegular (freeLetter s) : GroupHilbert FreeTwo →L[ℂ] GroupHilbert FreeTwo)‖ ≤
      2 * Real.sqrt 3 := by
  let π : FreeTwo →* H ≃ₗᵢ[ℂ] H :=
    Unitary.linearIsometryEquiv.toMonoidHom.comp (completedGroupUnitary φ u)
  let T := ∑ s : FreeLetter, TensorProduct.mapL
    (π (freeLetter s)).toContinuousLinearEquiv.toContinuousLinearMap
    (leftRegular (freeLetter s) : GroupHilbert FreeTwo →L[ℂ] GroupHilbert FreeTwo)
  have he : (∑ s : FreeLetter, TensorProduct.mapL (φ (u (freeLetter s)))
      (leftRegular (freeLetter s) : GroupHilbert FreeTwo →L[ℂ] GroupHilbert FreeTwo)) =
      ((φ 1).rTensor (GroupHilbert FreeTwo)).comp T := by
    apply ContinuousLinearMap.ext
    intro z
    induction z using OAI.tensorInductionOn with
    | tmul ξ η =>
      simp only [T, sum_apply, TensorProduct.mapL_tmul, ContinuousLinearMap.comp_apply,
        map_sum, ContinuousLinearMap.rTensor_tmul]
      apply Finset.sum_congr rfl
      intro s _
      congr 1
      exact (congrArg (fun f : H →L[ℂ] H => f ξ)
        (projection_mul_completedGroup φ u (freeLetter s))).symm
    | add z w hz hw => simp only [map_add, hz, hw]
  rw [he]
  have hp : ‖(φ 1).rTensor (GroupHilbert FreeTwo)‖ ≤ 1 := by
    apply (ContinuousLinearMap.norm_rTensor_le _ _).trans
    apply (NonUnitalStarAlgHom.norm_apply_le φ 1).trans
    cases subsingleton_or_nontrivial A with
    | inl h => simp [Subsingleton.elim (1 : A) 0]
    | inr h => simp
  have ht : ‖T‖ ≤ 2 * Real.sqrt 3 := norm_freeTensor_sum_le π
  exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
    (by
      simpa only [one_mul] using mul_le_mul hp ht
        (ContinuousLinearMap.opNorm_nonneg T) zero_le_one)

end WeakPureInfiniteness
end

end OAI
end

section
-- module Solutions.OAIQ246_WI.WeakInfiniteness_TensorDensity
attribute [-instance] _root_.OAI.WeakPureInfiniteness.crossTensorGraphCStar _root_.OAI.WeakPureInfiniteness.instCStarAlgebraReducedGroupAlgebra _root_.OAI.WeakPureInfiniteness.instNonUnitalCStarAlgebraSubtypeMemNonUnitalStarSubalgebraComplexKernelAlgebra _root_.OAI.WeakPureInfiniteness.uliftCStarAlgebra _root_.OAI.WeakPureInfiniteness.uliftInnerProduct _root_.OAI.WeakPureInfiniteness.uliftStarRing
attribute [-simp] _root_.OAI.WeakPureInfiniteness.minimalElementaryLeft_apply _root_.OAI.WeakPureInfiniteness.minimalElementaryRight_apply _root_.OAI.WeakPureInfiniteness.minimalMapAny_elementary _root_.OAI.WeakPureInfiniteness.minimalMapLeftAny_elementary _root_.OAI.WeakPureInfiniteness.minimalMapLeft_elementary _root_.OAI.WeakPureInfiniteness.rightElementaryHom_apply _root_.OAI.WeakPureInfiniteness.spatialMapLeft_elementary _root_.OAI.WeakPureInfiniteness.spatialVectorFunctional_elementary
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct ENNReal ComplexOrder
open UniformSpace
open CStarAlgebra
open scoped NNReal
open scoped TensorProduct ComplexConjugate

namespace WeakPureInfiniteness

universe u v

section TensorContinuity

variable {A : Type u} {B : Type v} [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]

lemma spatialElementary_sum_left {I : Type*} (s : Finset I) (a : I → A) (b : B) :
    spatialElementary (∑ i ∈ s, a i) b = ∑ i ∈ s, spatialElementary (a i) b := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih => simp only [Finset.sum_insert hi, spatialElementary_add_left, ih]

lemma spatialElementary_sum_right {I : Type*} (s : Finset I) (a : A) (b : I → B) :
    spatialElementary a (∑ i ∈ s, b i) = ∑ i ∈ s, spatialElementary a (b i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih => simp only [Finset.sum_insert hi, spatialElementary_add_right, ih]

end TensorContinuity

section GroupTensorDensity

variable {G : Type u} [Group G]

lemma groupTensorPolynomial_val (c : G × G →₀ ℂ) :
    (groupTensorPolynomial c).val = c.sum (fun p z => z •
      spatialElementary (fullGroupElement p.1) (fullGroupElement p.2)) := by
  simp only [groupTensorPolynomial, Finsupp.linearCombination_apply, Finsupp.sum]
  change (minimalAmbientInclusion (A := FullGroupAlgebra G) (B := FullGroupAlgebra G))
    (∑ p ∈ c.support, c p • minimalElementary (fullGroupElement p.1) (fullGroupElement p.2)) = _
  simp only [map_sum, map_smul]
  rfl

lemma groupTensorPolynomial_dense : DenseRange (groupTensorPolynomial (G := G)) := by
  let S : Submodule ℂ (SpatialAmbient (FullGroupAlgebra G) (FullGroupAlgebra G)) :=
    Submodule.span ℂ (Set.range fun p : G × G =>
      spatialElementary (fullGroupElement p.1) (fullGroupElement p.2))
  have hgen (s t : G) : spatialElementary (fullGroupElement s) (fullGroupElement t) ∈ S :=
    Submodule.subset_span (Set.mem_range_self (s,t))
  have hpoly (c d : G →₀ ℂ) :
      spatialElementary (fullGroupPolynomial c) (fullGroupPolynomial d) ∈ S := by
    change spatialElementary (c.sum (fun s z => z • fullGroupElement s))
      (d.sum (fun t z => z • fullGroupElement t)) ∈ S
    have hl := spatialElementary_sum_left (A := FullGroupAlgebra G) (B := FullGroupAlgebra G)
      c.support (fun s => c s • fullGroupElement s) (d.sum (fun t z => z • fullGroupElement t))
    refine hl.symm ▸ ?_
    apply Submodule.sum_mem S
    intro s hs
    have hsm := spatialElementary_smul_left (A := FullGroupAlgebra G) (B := FullGroupAlgebra G)
      (c s) (fullGroupElement s) (d.sum (fun t z => z • fullGroupElement t))
    refine hsm.symm ▸ ?_
    apply Submodule.smul_mem S
    have hr := spatialElementary_sum_right (A := FullGroupAlgebra G) (B := FullGroupAlgebra G)
      d.support (fullGroupElement s) (fun t => d t • fullGroupElement t)
    refine hr.symm ▸ ?_
    apply Submodule.sum_mem S
    intro t ht
    have hsm' := spatialElementary_smul_right (A := FullGroupAlgebra G) (B := FullGroupAlgebra G)
      (d t) (fullGroupElement s) (fullGroupElement t)
    exact hsm'.symm ▸ Submodule.smul_mem S _ (hgen s t)
  have hall (a b : FullGroupAlgebra G) : spatialElementary a b ∈ S.topologicalClosure := by
    refine (fullGroupPolynomial_dense (G := G)).induction_on a ?_ ?_
    · exact S.isClosed_topologicalClosure.preimage (spatialElementaryLeft b).continuous
    · intro c
      refine (fullGroupPolynomial_dense (G := G)).induction_on b ?_ ?_
      · exact S.isClosed_topologicalClosure.preimage (spatialElementaryRight (fullGroupPolynomial c)).continuous
      · intro d
        exact Submodule.le_topologicalClosure S (hpoly c d)
  have hr (x : MinimalTensor (FullGroupAlgebra G) (FullGroupAlgebra G)) : x.val ∈ S.topologicalClosure := by
    have hx : x.val ∈ (minimalTensorSubalgebra (FullGroupAlgebra G) (FullGroupAlgebra G) : Set _) := x.property
    rw [minimalTensor_eq_closure_span] at hx
    exact closure_minimal (Submodule.span_le.mpr (by rintro _ ⟨⟨a,b⟩,rfl⟩; exact hall a b))
      S.isClosed_topologicalClosure hx
  rw [Metric.denseRange_iff]
  intro x ε hε
  obtain ⟨y, hy, hd⟩ := Metric.mem_closure_iff.mp (hr x) ε hε
  obtain ⟨c, rfl⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp hy
  refine ⟨c, ?_⟩
  rw [dist_eq_norm]
  change ‖x.val - (groupTensorPolynomial c).val‖ < ε
  rw [groupTensorPolynomial_val]
  simpa only [dist_eq_norm] using hd

end GroupTensorDensity

end WeakPureInfiniteness
end

end OAI
end

section
-- module Solutions.OAIQ246_WI.WeakInfiniteness_ScalarDiagonal
attribute [-instance] _root_.OAI.WeakPureInfiniteness.crossTensorGraphCStar _root_.OAI.WeakPureInfiniteness.instCStarAlgebraReducedGroupAlgebra _root_.OAI.WeakPureInfiniteness.instCoeFunContractionAmbientForallContinuousLinearMapComplexIdCarrierHilbert _root_.OAI.WeakPureInfiniteness.instNonUnitalCStarAlgebraSubtypeMemNonUnitalStarSubalgebraComplexKernelAlgebra _root_.OAI.WeakPureInfiniteness.uliftCStarAlgebra _root_.OAI.WeakPureInfiniteness.uliftStarRing
attribute [-simp] _root_.OAI.WeakPureInfiniteness.fullToReduced_element _root_.OAI.WeakPureInfiniteness.fullToUniversal_element _root_.OAI.WeakPureInfiniteness.minimalElementaryLeft_apply _root_.OAI.WeakPureInfiniteness.minimalElementaryRight_apply _root_.OAI.WeakPureInfiniteness.minimalMapAny_elementary _root_.OAI.WeakPureInfiniteness.minimalMapLeftAny_elementary _root_.OAI.WeakPureInfiniteness.minimalMapLeft_elementary _root_.OAI.WeakPureInfiniteness.rightElementaryHom_apply _root_.OAI.WeakPureInfiniteness.spatialMapLeft_elementary
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct ENNReal ComplexOrder
open UniformSpace
open CStarAlgebra
open scoped NNReal
open scoped TensorProduct ComplexConjugate

namespace WeakPureInfiniteness

universe u

section DiagonalPolynomial

variable {G : Type u} [Group G]

lemma finite_diagonal_polynomial (F : Type u) [Group F] [Fintype F] [DecidableEq F]
    (q : G →* F) (c : G × G →₀ ℂ) :
    spatialVectorFunctional (finiteGroupSpatialRepresentation q)
      (finiteGroupSpatialDiagonal q : Completion
        (ULift.{u+1} (EuclideanSpace ℂ F) ⊗[ℂ] ULift.{u+1} (EuclideanSpace ℂ F)))
      (groupTensorPolynomial c).val =
      c.sum (fun p z => z • (if q p.1 = q p.2 then (1 : ℂ) else 0)) := by
  rw [groupTensorPolynomial_val]
  simp only [Finsupp.sum, map_sum, map_smul, finiteGroupSpatialDiagonal_coefficient]

lemma finite_diagonal_polynomial_bound (F : Type u) [Group F] [Fintype F] [DecidableEq F]
    (q : G →* F) (c : G × G →₀ ℂ) :
    ‖c.sum (fun p z => z • (if q p.1 = q p.2 then (1 : ℂ) else 0))‖ ≤
      ‖groupTensorPolynomial c‖ := by
  rw [← finite_diagonal_polynomial F q c]
  apply (ContinuousLinearMap.le_opNorm _ _).trans
  have hb := norm_spatialVectorFunctional_le (finiteGroupSpatialRepresentation q)
    (finiteGroupSpatialDiagonal q : Completion
      (ULift.{u+1} (EuclideanSpace ℂ F) ⊗[ℂ] ULift.{u+1} (EuclideanSpace ℂ F)))
  simp only [Completion.norm_coe, norm_finiteGroupSpatialDiagonal, one_mul] at hb
  exact (mul_le_mul_of_nonneg_right hb (norm_nonneg _)).trans_eq (one_mul _)

end DiagonalPolynomial

section FreeDiagonal

variable {α : Type u} [Fintype α] [DecidableEq α]

lemma norm_free_diagonalCoefficient_le (c : FreeGroup α × FreeGroup α →₀ ℂ) :
    ‖diagonalCoefficient c‖ ≤ ‖groupTensorPolynomial c‖ := by
  classical
  let S := c.support.image Prod.fst ∪ c.support.image Prod.snd
  obtain ⟨m, hm⟩ := freeFiniteQuotient_injOn_finset S
  have heq (p : FreeGroup α × FreeGroup α) (hp : p ∈ c.support) :
      freeFiniteQuotient m p.1 = freeFiniteQuotient m p.2 ↔ p.1 = p.2 := by
    constructor
    · exact hm (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨p,hp,rfl⟩))
        (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨p,hp,rfl⟩))
    · rintro h; rw [h]
  have hv : diagonalCoefficient c = c.sum (fun p z =>
      z • (if freeFiniteQuotient m p.1 = freeFiniteQuotient m p.2 then (1 : ℂ) else 0)) := by
    simp only [diagonalCoefficient, Finsupp.linearCombination_apply, Finsupp.sum]
    apply Finset.sum_congr rfl
    intro p hp
    by_cases h : p.1 = p.2
    · simp [h]
    · simp [h, not_congr (heq p hp)]
  rw [hv]
  exact finite_diagonal_polynomial_bound _ (freeFiniteQuotient m) c

lemma norm_freeDiagonalFunctional_le : ‖freeDiagonalFunctional (α := α)‖ ≤ 1 := by
  apply LinearMap.opNorm_extendOfNorm_le groupTensorPolynomial_dense zero_le_one
  intro c
  simpa only [one_mul] using norm_free_diagonalCoefficient_le c

end FreeDiagonal

end WeakPureInfiniteness
end

end OAI
end

section
-- module Solutions.OAIQ246_WI.WeakInfiniteness_ReducedOperators
attribute [-instance] _root_.OAI.WeakPureInfiniteness.crossTensorGraphCStar _root_.OAI.WeakPureInfiniteness.instCoeFunContractionAmbientForallContinuousLinearMapComplexIdCarrierHilbert _root_.OAI.WeakPureInfiniteness.instNonUnitalCStarAlgebraSubtypeMemNonUnitalStarSubalgebraComplexKernelAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct ENNReal ComplexOrder
open UniformSpace
open CStarAlgebra
open scoped NNReal
open scoped TensorProduct ComplexConjugate
open scoped ENNReal InnerProductSpace
open scoped InnerProductSpace
open scoped TensorProduct InnerProductSpace

namespace WeakPureInfiniteness

lemma reducedLargeToOperators_injective : Function.Injective reducedLargeToOperators := by
  intro x y h
  exact ULift.down_injective (Subtype.ext h)

lemma completion_sum {ι H K : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
    [NormedAddCommGroup K] [NormedSpace ℂ K] (s : Finset ι) (T : ι → H →L[ℂ] K) :
    (∑ i ∈ s, T i).completion = ∑ i ∈ s, (T i).completion := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty, completion_zero]
  | @insert i s hi ih => simp only [Finset.sum_insert hi, completion_add, ih]

lemma norm_freeDiagonalWitness_reduced_le :
    ‖minimalMapRight (A := FullGroupAlgebra (FreeGroup Bool)) (C := FullGroupAlgebra (FreeGroup Bool)) (D := ReducedFreeLarge) fullToReducedLarge.toNonUnitalStarAlgHom freeDiagonalWitness‖ ≤ 2 * Real.sqrt 3 := by
  let := CStarAlgebra.spectralOrder ReducedFreeLarge
  let := CStarAlgebra.spectralOrderedRing ReducedFreeLarge
  change ‖(minimalMapRight (A := FullGroupAlgebra (FreeGroup Bool)) (C := FullGroupAlgebra (FreeGroup Bool)) (D := ReducedFreeLarge) fullToReducedLarge.toNonUnitalStarAlgHom freeDiagonalWitness).val‖ ≤ _
  apply lp.norm_le_of_forall_le (by positivity)
  intro π
  have he : (minimalMapRight (A := FullGroupAlgebra (FreeGroup Bool)) (C := FullGroupAlgebra (FreeGroup Bool)) (D := ReducedFreeLarge) fullToReducedLarge.toNonUnitalStarAlgHom freeDiagonalWitness).val π =
      (∑ s : FreeLetter, TensorProduct.mapL
        (π.leftRep (fullGroupElement (freeLetter s)))
        (π.rightRep (fullToReducedLarge (fullGroupElement (freeLetter s))))).completion := by
    rw [completion_sum]
    change (∑ s : FreeLetter, spatialElementary (fullGroupElement (freeLetter s))
      (fullToReducedLarge (fullGroupElement (freeLetter s)))) π = _
    rfl
  rw [he, norm_completion]
  have h := tensor_norm_le_faithful Finset.univ
    (fun s : FreeLetter => π.leftRep (fullGroupElement (freeLetter s)))
    (fun s : FreeLetter => fullToReducedLarge (fullGroupElement (freeLetter s)))
    reducedLargeToOperators.toNonUnitalStarAlgHom π.rightRep reducedLargeToOperators_injective
  apply h.trans
  change ‖∑ s : FreeLetter, TensorProduct.mapL (π.leftRep (fullGroupElement (freeLetter s)))
    (leftRegular (freeLetter s) : GroupHilbert FreeTwo →L[ℂ] GroupHilbert FreeTwo)‖ ≤ _
  exact norm_freeTensor_nonunital_sum_le π.leftRep (fullGroupUnitary (G := FreeTwo))

end WeakPureInfiniteness
end

end OAI
end

section
-- module Solutions.OAIQ246_WI.WeakInfiniteness_NormKernelWitness
attribute [-instance] _root_.OAI.WeakPureInfiniteness.crossTensorGraphCStar _root_.OAI.WeakPureInfiniteness.instNonUnitalCStarAlgebraSubtypeMemNonUnitalStarSubalgebraComplexKernelAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct ENNReal ComplexOrder
open UniformSpace
open CStarAlgebra
open scoped NNReal
open scoped TensorProduct ComplexConjugate
open scoped ENNReal InnerProductSpace
open scoped InnerProductSpace
open scoped TensorProduct InnerProductSpace

namespace WeakPureInfiniteness

lemma functional_norm_le_image {A B : Type*}
    [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
    (q : A →⋆ₙₐ[ℂ] B) (φ : A →L[ℂ] ℂ)
    (hφ : ∀ y, q y = 0 → φ y = 0) (hφn : ‖φ‖ ≤ 1)
    (x : A) {M : ℝ} (hM : 0 < M) (hxn : ‖q x‖ ≤ M) : ‖φ x‖ ≤ M := by
  obtain ⟨z,hz,hzn⟩ := nonUnitalStarHom_exists_lift_norm_le q x hM hxn
  have hker : q (x-z) = 0 := by rw [map_sub,hz,sub_self]
  have hzero := hφ (x-z) hker
  have hval : φ x = φ z := sub_eq_zero.mp (by simpa only [map_sub] using hzero)
  rw [hval]
  exact (φ.le_opNorm z).trans
    ((mul_le_mul_of_nonneg_right hφn (norm_nonneg z)).trans
      (by simpa only [one_mul] using hzn))

lemma freeDiagonalFunctional_bound_of_kernel_oai
    (hk : ∀ y : MinimalTensor (FullGroupAlgebra (FreeGroup Bool)) (FullGroupAlgebra (FreeGroup Bool)), minimalMapRight (A := FullGroupAlgebra (FreeGroup Bool)) (C := FullGroupAlgebra (FreeGroup Bool)) (D := ReducedFreeLarge) fullToReducedLarge.toNonUnitalStarAlgHom y = 0 →
      freeDiagonalFunctional y = 0) :
    ‖freeDiagonalFunctional freeDiagonalWitness‖ ≤ 2 * Real.sqrt 3 := by
  exact functional_norm_le_image (minimalMapRight (A := FullGroupAlgebra (FreeGroup Bool)) (C := FullGroupAlgebra (FreeGroup Bool)) (D := ReducedFreeLarge) fullToReducedLarge.toNonUnitalStarAlgHom)
    freeDiagonalFunctional hk norm_freeDiagonalFunctional_le freeDiagonalWitness
    (by positivity) norm_freeDiagonalWitness_reduced_le

end WeakPureInfiniteness
end

end OAI
end

theorem solution : type_of% @OAI.WeakPureInfiniteness.freeDiagonalFunctional_bound_of_kernel_oai := @OAI.WeakPureInfiniteness.freeDiagonalFunctional_bound_of_kernel_oai
