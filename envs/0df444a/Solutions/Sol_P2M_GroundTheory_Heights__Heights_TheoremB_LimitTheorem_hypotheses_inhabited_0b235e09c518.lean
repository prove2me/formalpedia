-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_TheoremB_LimitTheorem_hypotheses_inhabited_0b235e09c518
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T05:08:50.494195+00:00
-- url     : https://prove2.me/submissions/b444f079-6fd1-4729-8163-f46c79db9978

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MultinomialWeights_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MultinomialWeights_StatementsEnd

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.TheoremB
open MvPolynomial Finset Filter Topology
variable (d : IndexData)
variable {d}
namespace GroundTheory.Heights₂.Heights.TheoremB
namespace LimitTheorem
theorem _root_.solution :
    (0 : ℝ) < 1 ∧ ∀ s : ℚ, 0 < s → (s : ℝ) ≤ 1 →
      |(s : ℝ) - eval (fun o : Option (Fin 1) => o.elim (s : ℝ) (fun p => (0 : Fin 1 → ℝ) p - s * (0 : Fin 1 → ℝ) p))
        (X none : MvPolynomial (Option (Fin 1)) ℝ)| ≤ 0 * s := by
  refine ⟨one_pos, fun s _ _ => ?_⟩
  simp
end LimitTheorem
end GroundTheory.Heights₂.Heights.TheoremB
