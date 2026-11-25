-- Prove2me | solution 1 for PI.IsoDerivBFintype.le_of_oe
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T09:43:29.971102+00:00
-- url     : https://prove2.me/submissions/463c477c-2b76-499d-8604-2dcde77318a9

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_IsoDerivB
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IsometryDerivative_ExistsOePerm
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IsometryDerivative_ApplyAt0EqSum

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
open PI PI.IsoDerivBFintype
open PI.IsoDerivB
namespace PI.IsoDerivBFintype
theorem _root_.solution {h n : ℕ} (J : Fin h ↪o Fin n) : h ≤ n := by
  simpa using Fintype.card_le_of_embedding J.toEmbedding
end PI.IsoDerivBFintype
