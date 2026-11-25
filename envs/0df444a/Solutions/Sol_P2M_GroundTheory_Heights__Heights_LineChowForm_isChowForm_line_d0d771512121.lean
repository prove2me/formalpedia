-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_LineChowForm_isChowForm_line_d0d771512121
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T05:54:15.871449+00:00
-- url     : https://prove2.me/submissions/cafa8c1e-8fec-44da-be47-21897e4c0111

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LineInhabitant
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LineChowForm_pseudo_db09f682ed74
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LineChowForm_cancelN_35a0c58da760
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LineChowForm_aeval_substZeroOneOne_8aa7d728ad3e
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LineChowForm_det_two_ne_zero_1d68ea83fc5a

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial
noncomputable section
open GroundTheory.Heights₂.Heights.LineChowForm
variable {F : Type*} [Field F]
variable {F : Type*} [Field F]
namespace GroundTheory.Heights₂.Heights.LineChowForm
theorem _root_.solution :
    IsChowForm (⊥ : Ideal (MvPolynomial (Fin 2) F)) 2 (D2 : MvPolynomial (Fin 2 × Fin 2) F) := by
  refine ⟨det_two_ne_zero, fun g => ⟨fun hg => ?_, ?_⟩⟩
  ·
    obtain ⟨N, q, r, h1, h2⟩ := pseudo g
    have hr : r = 0 := by
      have hz : MvPolynomial.map (algebraMap F (AlgebraicClosure F)) (X (0,0) * r) = 0 := by
        apply MvPolynomial.funext
        intro w
        have key : aeval w (X (0,0) * r) = 0 := by
          by_cases hw : w (0,0) = 0
          · simp [hw]
          · let u : Fin 2 × Fin 2 → AlgebraicClosure F :=
              Function.update w (1,1) (w (0,1) * w (1,0) / w (0,0))
            have u00 : u (0,0) = w (0,0) := Function.update_of_ne (by decide) _ _
            have u01 : u (0,1) = w (0,1) := Function.update_of_ne (by decide) _ _
            have u10 : u (1,0) = w (1,0) := Function.update_of_ne (by decide) _ _
            have u11 : u (1,1) = w (0,1) * w (1,0) / w (0,0) := Function.update_self _ _ _
            have hinc : u ∈ incidence (⊥ : Ideal (MvPolynomial (Fin 2) F)) 2 := by
              refine ⟨![w (0,1), -w (0,0)], fun h => ?_, fun g' hg' => ?_, fun i => ?_⟩
              · have := congrFun h 1
                simp at this
                exact hw this
              · rw [Ideal.mem_bot] at hg'
                simp [hg']
              · fin_cases i
                · simp [Fin.sum_univ_two, u00, u01]; ring
                · simp [Fin.sum_univ_two, u10, u11]; field_simp; ring
            have hg' := hg u hinc
            have hD : aeval u (D2 : MvPolynomial (Fin 2 × Fin 2) F) = 0 := by
              simp only [D2, map_sub, map_mul, aeval_X, u00, u01, u10, u11]
              field_simp
              ring
            have h3 := congrArg (aeval u) h1
            simp only [map_mul, map_add, map_pow, hg', hD, mul_zero, zero_add] at h3
            have hw' : aeval w r = aeval u r := by
              rw [← h2, aeval_substZeroOneOne, aeval_substZeroOneOne]
              congr 1
              simp only [u, Function.update_idem]
            rw [map_mul, hw', ← h3, mul_zero]
        rw [eval_map, map_zero]
        simpa [aeval_def] using key
      have hz' : (X (0,0) * r : MvPolynomial (Fin 2 × Fin 2) F) = 0 :=
        MvPolynomial.map_injective _ (algebraMap F (AlgebraicClosure F)).injective (by simpa using hz)
      exact (mul_eq_zero.mp hz').resolve_left (X_ne_zero _)
    rw [hr, add_zero] at h1
    exact cancelN N g ⟨q, by rw [h1]; ring⟩
  · rintro ⟨h, rfl⟩ u ⟨x, hx, -, hu⟩
    have E0 := hu 0
    have E1 := hu 1
    simp only [Fin.sum_univ_two] at E0 E1
    have hD : aeval u (D2 : MvPolynomial (Fin 2 × Fin 2) F) = 0 := by
      simp only [D2, map_sub, map_mul, aeval_X]
      by_cases h0 : x 0 = 0
      · have h1 : x 1 ≠ 0 := fun h1 => hx (funext fun j => by fin_cases j <;> simpa [*])
        apply mul_right_cancel₀ h1
        linear_combination (-(u (1,0))) * E0 + u (0,0) * E1
      · apply mul_right_cancel₀ h0
        linear_combination u (1,1) * E0 - u (0,1) * E1
    rw [map_mul, hD, zero_mul]
end GroundTheory.Heights₂.Heights.LineChowForm
