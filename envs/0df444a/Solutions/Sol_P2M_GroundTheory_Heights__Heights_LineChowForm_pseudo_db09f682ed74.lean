-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_LineChowForm_pseudo_db09f682ed74
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T04:39:38.622203+00:00
-- url     : https://prove2.me/submissions/a466f2fc-6151-4a55-9907-61ecaf5edb86

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LineInhabitant
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LineChowForm_substZeroOneOne_X_zero_zero_8d8cd2c59b46
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LineChowForm_substZeroOneOne_X_of_ne_0b3fd90d8c9f

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
theorem _root_.solution (g : MvPolynomial (Fin 2 × Fin 2) F) :
    ∃ (N : ℕ) (q r : MvPolynomial (Fin 2 × Fin 2) F),
      X (0,0) ^ N * g = q * D2 + r ∧ substZeroOneOne r = r := by
  induction g using MvPolynomial.induction_on with
  | C a => exact ⟨0, 0, C a, by simp, by simp [substZeroOneOne]⟩
  | add p q hp hq =>
    obtain ⟨N, a, r, h1, h2⟩ := hp
    obtain ⟨M, b, s, h3, h4⟩ := hq
    refine ⟨N + M, X (0,0) ^ M * a + X (0,0) ^ N * b, X (0,0) ^ M * r + X (0,0) ^ N * s, ?_, ?_⟩
    · have : X (0,0) ^ (N + M) * (p + q) = X (0,0) ^ M * (X (0,0) ^ N * p) + X (0,0) ^ N * (X (0,0) ^ M * q) := by
        ring
      rw [this, h1, h3]; ring
    · simp only [map_add, map_mul, map_pow, substZeroOneOne_X_zero_zero, h2, h4]
  | mul_X p i hp =>
    obtain ⟨N, a, r, h1, h2⟩ := hp
    by_cases hi : i = (1,1)
    · subst hi
      refine ⟨N + 1, X (0,0) * X (1,1) * a + r, r * (X (0,1) * X (1,0)), ?_, ?_⟩
      · have : X (0,0) ^ (N + 1) * (p * X (1,1)) = (X (0,0) ^ N * p) * (X (0,0) * X (1,1)) := by ring
        rw [this, h1]; simp only [D2]; ring
      · rw [map_mul, map_mul, h2, substZeroOneOne_X_of_ne _ (by decide), substZeroOneOne_X_of_ne _ (by decide)]
    · refine ⟨N, a * X i, r * X i, ?_, ?_⟩
      · have : X (0,0) ^ N * (p * X i) = (X (0,0) ^ N * p) * X i := by ring
        rw [this, h1]; ring
      · rw [map_mul, h2, substZeroOneOne_X_of_ne _ hi]
end GroundTheory.Heights₂.Heights.LineChowForm
