-- Prove2me | solution 1 for ReciprocityTheory.ReducedBases.T2.det_gram_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:22:35.014065+00:00
-- url     : https://prove2.me/submissions/e1e2ad59-d8bf-4061-87b6-1941879e49d5

import Definitions.Def_ReciprocityTheory_ReducedBases_GsInnerBOfLt
import Definitions.Def_ReciprocityTheory_ReducedBases_LatDefs
import Definitions.Def_ReciprocityTheory_ReducedBases_TBInjective
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
namespace ReciprocityTheory.ReducedBases.T2
open Finset InnerProductSpace Matrix
private lemma eq_sum_smul_gs {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {m : ℕ}
    (v : Fin m → E) (a : Fin m) :
    v a = ∑ b, (if b = a then (1 : ℝ) else if b < a then ⟪gs v b, v a⟫_ℝ / ‖gs v b‖ ^ 2 else 0) •
      gs v b := by
  have hterm : ∀ b, (if b = a then (1 : ℝ) else if b < a then ⟪gs v b, v a⟫_ℝ / ‖gs v b‖ ^ 2 else 0) •
      gs v b = (if b = a then gs v b else 0) +
        (if b < a then (⟪gs v b, v a⟫_ℝ / ‖gs v b‖ ^ 2) • gs v b else 0) := by
    intro b
    by_cases h1 : b = a
    · subst h1; simp
    · by_cases h2 : b < a <;> simp [h1, h2]
  rw [Finset.sum_congr rfl (fun b _ => hterm b), Finset.sum_add_distrib]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [← Finset.sum_filter]
  have hf : Finset.univ.filter (fun b => b < a) = Finset.Iio a := by ext; simp
  rw [hf]
  conv_lhs => rw [gramSchmidt_def'' ℝ v a]
  simp
variable {d : ℕ}
end ReciprocityTheory.ReducedBases.T2
end
end

set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ReducedBases ReciprocityTheory.ReducedBases.T2
open Finset InnerProductSpace Matrix
namespace ReciprocityTheory.ReducedBases.T2
theorem _root_.solution {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {m : ℕ}
    (v : Fin m → E) (hv : LinearIndependent ℝ v) :
    (Matrix.gram ℝ v).det = ∏ j, ‖gs v j‖ ^ 2 := by
  set C : Matrix (Fin m) (Fin m) ℝ := Matrix.of fun a b =>
    if b = a then (1 : ℝ) else if b < a then ⟪gs v b, v a⟫_ℝ / ‖gs v b‖ ^ 2 else 0 with hCdef
  have hexp : ∀ a, v a = ∑ b, C a b • gs v b := fun a => by
    simpa [C] using eq_sum_smul_gs v a
  have hin : ∀ a b, ⟪v a, v b⟫_ℝ = ∑ c, C a c * ‖gs v c‖ ^ 2 * C b c := by
    intro a b
    rw [hexp a, hexp b]
    simp only [sum_inner, inner_sum, real_inner_smul_left, real_inner_smul_right]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [Finset.sum_eq_single c]
    · rw [real_inner_self_eq_norm_sq]; ring
    · intro d _ hdc
      rw [gramSchmidt_orthogonal ℝ v hdc]; ring
    · simp
  have hG : Matrix.gram ℝ v = C * Matrix.diagonal (fun c => ‖gs v c‖ ^ 2) * Cᵀ := by
    ext a b
    rw [Matrix.gram_apply, hin, Matrix.mul_apply]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [Matrix.mul_apply, Finset.sum_eq_single c]
    · simp [Matrix.diagonal_apply_eq, Matrix.transpose_apply]
    · intro d _ hdc
      simp [Matrix.diagonal_apply_ne _ hdc]
    · simp
  have hC : C.det = 1 := by
    rw [Matrix.det_of_lowerTriangular C ?_]
    · simp [C]
    · intro i j hij
      have hlt : i < j := OrderDual.toDual_lt_toDual.1 hij
      simp [C, hlt.ne', not_lt.2 hlt.le]
  rw [hG, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, hC, Matrix.det_diagonal]
  simp
end ReciprocityTheory.ReducedBases.T2
