-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_SnapperDiffPoly_isNumPolyLT_comp_26fb9bdb9ce0
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T08:17:48.653751+00:00
-- url     : https://prove2.me/submissions/93585d2a-05a3-4d7f-8a5f-42919220606e

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_SnapperDiffPolySt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PPolyOfDiffs
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PSnapperDiffPoly
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_SnapperDiffPoly_eval_aeval_eq_30a4cefc8185
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_PolyOfDiffs_totalDegree_aeval_le_30e9887fa60b


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman
open MvPolynomial
noncomputable section
open GroundTheory.Heights₂.Heights.Kleiman.SnapperDiffPoly
namespace GroundTheory.Heights₂.Heights.Kleiman.SnapperDiffPoly
theorem _root_.solution {t D : ℕ} {F G : (Fin t → ℕ) → ℤ → ℚ} (σ : Fin (t + 1) → MvPolynomial (Fin (t + 1)) ℚ)
    (hσ : ∀ i, (σ i).totalDegree ≤ 1) (a : (Fin t → ℕ) → ℤ → (Fin t → ℕ)) (b : (Fin t → ℕ) → ℤ → ℤ)
    (hab : ∀ n c, (fun i => eval (numPt n c) (σ i)) = numPt (a n c) (b n c))
    (hG : ∀ n c, G n c = F (a n c) (b n c)) (hF : IsNumPolyLT t D F) : IsNumPolyLT t D G := by
  obtain ⟨Q, hQ, hE⟩ := hF
  refine ⟨aeval σ Q, ?_, fun n c => ?_⟩
  · rcases hQ with rfl | hQ
    · left; simp
    · exact Or.inr ((FieldNumbers.PolyOfDiffs.totalDegree_aeval_le σ hσ Q).trans_lt hQ)
  · rw [hG, hE]
    change _ = eval (numPt n c) (aeval σ Q)
    rw [eval_aeval_eq, hab]
    rfl
end GroundTheory.Heights₂.Heights.Kleiman.SnapperDiffPoly
