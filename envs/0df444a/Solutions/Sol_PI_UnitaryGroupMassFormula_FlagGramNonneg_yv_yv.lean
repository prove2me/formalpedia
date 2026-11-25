-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.FlagGramNonneg.yv_yv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:40:41.743277+00:00
-- url     : https://prove2.me/submissions/ac8c2634-9a82-4f6d-aff5-1f60fc88bd8b

import Definitions.Def_Formalism_PeriodIntegrals_FlagGramNonneg
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FlagGramNonnegativity_SumMulCommMulVec
import Theorems.Thm_PI_UnitaryGroupMassFormula_FlagGramNonneg_herm
import Theorems.Thm_PI_UnitaryGroupMassFormula_FlagGramNonneg_left_sub_sum
import Theorems.Thm_PI_UnitaryGroupMassFormula_FlagGramNonneg_right_sub_sum

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix PI.FlagGramNonneg
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.FlagGramNonneg
variable {E : Type} [Field E] [StarRing E] {V : Type} [AddCommGroup V] [Module E V]
variable (hT : V →ₗ⋆[E] V →ₗ[E] E) {r : ℕ} (e e' : Fin r → V) (z z' : V)
namespace PI.UnitaryGroupMassFormula.FlagGramNonneg
theorem _root_.solution (hS : hT.IsSymm) (hA : IsUnit (amat hT e e').det) (he : ∀ a b, hT (e a) (e b) = 0)
    (he' : ∀ a b, hT (e' a) (e' b) = 0) (a c : Fin r) :
    hT (yv hT e e' a) (yv hT e e' c) = if a = c then -2 else 0 := by
  have hAA : amat hT e e' * (amat hT e e')⁻¹ = 1 := Matrix.mul_nonsing_inv _ hA
  have key : ∀ a c, ∑ d, hT (e a) (e' d) * (amat hT e e')⁻¹ d c = if a = c then 1 else 0 := by
    intro a c
    have h := congrFun (congrFun hAA a) c
    rw [Matrix.mul_apply, Matrix.one_apply] at h
    exact h
  have h1 : ∑ d, (amat hT e e')⁻¹ d c * hT (e a) (e' d) = if a = c then 1 else 0 := by
    rw [← key a c]
    exact Finset.sum_congr rfl fun d _ => mul_comm _ _
  have h2 : ∑ b, star ((amat hT e e')⁻¹ b a) * hT (e' b) (e c) = if a = c then 1 else 0 := by
    have h3 : ∑ b, star ((amat hT e e')⁻¹ b a) * hT (e' b) (e c) =
        star (∑ b, hT (e c) (e' b) * (amat hT e e')⁻¹ b a) := by
      rw [star_sum]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [star_mul', herm hS (e' b) (e c), mul_comm]
    rw [h3, key c a]
    rcases eq_or_ne a c with h | h
    · subst h
      simp
    · simp [h, Ne.symm h]
  unfold yv
  simp only [left_sub_sum, right_sub_sum, he, he', mul_zero, Finset.sum_const_zero, sub_zero, zero_sub]
  rw [h1, h2]
  split_ifs <;> ring
end PI.UnitaryGroupMassFormula.FlagGramNonneg
