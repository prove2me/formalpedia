-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FieldNumbers_PolyOfDiffs_exists_pow_antideriv_69ad4af11f37
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T03:53:07.483836+00:00
-- url     : https://prove2.me/submissions/ebf83cb1-2fb1-4f33-82b9-1b31741ffc03

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PPolyOfDiffs

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FieldNumbers
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR
open GroundTheory.Heights₂.Heights.FieldNumbers.PolyOfDiffs
variable {K : Type}
variable [DecidableEq K]
namespace GroundTheory.Heights₂.Heights.FieldNumbers.PolyOfDiffs
theorem _root_.solution (a : ℕ) : ∃ F : Polynomial ℚ, F.natDegree ≤ a + 1 ∧
    ∀ x : ℚ, F.eval x - F.eval (x - 1) = x ^ a := by
  refine ⟨Polynomial.C ((a + 1 : ℚ)⁻¹) *
    (Polynomial.bernoulli (a + 1)).comp (Polynomial.X + 1), ?_, fun x => ?_⟩
  · refine (Polynomial.natDegree_C_mul_le _ _).trans ?_
    refine Polynomial.natDegree_comp_le.trans ?_
    have hX : (Polynomial.X + 1 : Polynomial ℚ).natDegree = 1 := by
      rw [← Polynomial.C_1]; exact Polynomial.natDegree_X_add_C 1
    rw [hX, mul_one, Polynomial.bernoulli]
    refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun i _ => ?_
    exact (Polynomial.natDegree_monomial_le _).trans (Nat.sub_le _ _)
  · have h := Polynomial.bernoulli_eval_one_add (a + 1) x
    rw [Nat.add_sub_cancel] at h
    simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_comp, Polynomial.eval_add,
      Polynomial.eval_X, Polynomial.eval_one, sub_add_cancel]
    rw [add_comm x 1, h]
    push_cast
    field_simp
    ring
end GroundTheory.Heights₂.Heights.FieldNumbers.PolyOfDiffs
