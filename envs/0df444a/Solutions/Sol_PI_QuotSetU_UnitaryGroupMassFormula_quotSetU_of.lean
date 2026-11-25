-- Prove2me | solution 1 for PI.QuotSetU.UnitaryGroupMassFormula.quotSetU_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:12:39.381136+00:00
-- url     : https://prove2.me/submissions/8cab97c2-2769-41a8-9b57-b4ef1b808d5a

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryQuotientCompactness_SsetGroup
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryQuotientCompactness_QuotSetUOf

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix
open PI PI.QuotSetU PI.QuotSetU.UnitaryGroupMassFormula
open PI PI.QuotSetU
namespace PI.QuotSetU.UnitaryGroupMassFormula
theorem _root_.solution (hUH : UHGroup) (hSub : SsetSub) (hSG : SsetGroup) (hMod : ModExists)
    (hTG : TrivG) (hTS : TrivS) : PI.QuotSetU := by
  intro k r z hz hT
  refine ⟨hUH k r, hSG k r z hz hT, hSub k r z, ?_, ?_⟩
  · intro μG hμ
    obtain ⟨D, hD, hD1⟩ := hMod _ _ (hUH k r)
    exact hD1 (hTG k r D hD) μG hμ
  · intro μS hμ
    obtain ⟨D, hD, hD1⟩ := hMod _ _ (hSG k r z hz hT)
    exact hD1 (hTS k r z hz hT D hD) μS hμ
end PI.QuotSetU.UnitaryGroupMassFormula
