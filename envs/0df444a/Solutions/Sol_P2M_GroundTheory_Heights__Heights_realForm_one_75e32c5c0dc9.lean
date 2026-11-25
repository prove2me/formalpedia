-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_realForm_one_75e32c5c0dc9
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T08:39:12.608701+00:00
-- url     : https://prove2.me/submissions/a6b8d5c7-fa2e-494b-abcd-92928ce62823

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
theorem _root_.solution {q : ℕ} : realForm (1 : Matrix (Fin q) (Fin q) ℂ) = 1 := by
  ext ⟨i, a⟩ ⟨k, c⟩
  by_cases h : i = k <;> fin_cases a <;> fin_cases c <;> simp [realForm, Matrix.one_apply, h]
end GroundTheory.Heights₂.Heights
