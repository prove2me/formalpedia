-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_realForm_conjTranspose_41c2e7eb6733
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T08:39:03.268543+00:00
-- url     : https://prove2.me/submissions/1144f814-d1cc-4ef3-864a-559ed2d0a856

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
theorem _root_.solution {p q : ℕ} (A : Matrix (Fin p) (Fin q) ℂ) :
    realForm Aᴴ = (realForm A)ᵀ := by
  ext ⟨i, a⟩ ⟨k, c⟩
  fin_cases a <;> fin_cases c <;> simp [realForm]
end GroundTheory.Heights₂.Heights
