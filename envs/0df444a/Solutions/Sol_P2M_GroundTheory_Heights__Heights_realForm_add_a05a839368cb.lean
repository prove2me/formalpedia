-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_realForm_add_a05a839368cb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T08:38:57.978263+00:00
-- url     : https://prove2.me/submissions/062d92cc-dc3c-41ff-a557-290ff561b5be

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StatementsArea
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PComplexJacobian

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
open Matrix
noncomputable section
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution {p q : ℕ} (A B : Matrix (Fin p) (Fin q) ℂ) :
    realForm (A + B) = realForm A + realForm B := by
  ext ⟨i, a⟩ ⟨k, c⟩
  fin_cases a <;> fin_cases c <;> simp [realForm] <;> ring
end GroundTheory.Heights₂.Heights
