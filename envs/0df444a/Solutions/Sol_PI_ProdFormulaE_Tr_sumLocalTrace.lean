-- Prove2me | solution 1 for PI.ProdFormulaE.Tr.sumLocalTrace
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:27:47.244137+00:00
-- url     : https://prove2.me/submissions/8fb9d474-9211-4c2d-aef2-1ef8ff77da00

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProductFormulaHaar_TrSumOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProductFormulaHaar_InjectiveOfLinearIndependent
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProductFormulaHaar_T2SpaceOfIsValuativeTopology
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProductFormulaHaar_SumLocalTrace
import Theorems.Thm_PI_ProdFormulaE_Tr_toPi_injective
import Theorems.Thm_PI_ProdFormulaE_Tr_toPi_surjective
import Theorems.Thm_PI_ProdFormulaE_Tr_trSum_of


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.ProdFormulaE PI.ProdFormulaE.Tr
namespace PI.ProdFormulaE.Tr
theorem _root_.solution : TrSum := trSum_of toPi_injective toPi_surjective
end PI.ProdFormulaE.Tr
