-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UsCost.top_prod_lsz_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:48:53.302878+00:00
-- url     : https://prove2.me/submissions/f72a663c-6d4e-4887-a090-ea598b7fd30f

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCost_LetterSize
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCost_UnitarySumCostOfParts
import Theorems.Thm_PI_UnitaryGroupMassFormula_UsCost_top_lsz_ge_one

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U Formalism.FourierDecayAlt.P.BetaSesquilinearity
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.UsCost
namespace PI.UnitaryGroupMassFormula.UsCost
theorem _root_.solution {k r : ℕ} (l : List (B.Mat k r)) : 0 ≤ (l.map lsz).prod := by
  apply List.prod_nonneg
  intro a ha
  obtain ⟨X, -, rfl⟩ := List.mem_map.1 ha
  exact le_trans zero_le_one (top_lsz_ge_one X)
end PI.UnitaryGroupMassFormula.UsCost
