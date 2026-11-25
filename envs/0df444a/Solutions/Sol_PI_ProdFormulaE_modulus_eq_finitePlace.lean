-- Prove2me | solution 1 for PI.ProdFormulaE.modulus_eq_finitePlace
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:41:03.297096+00:00
-- url     : https://prove2.me/submissions/4fcb0486-4cd6-478a-97a5-e21b249018da

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProductFormulaHaar_ResCharIff
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProductFormulaHaar_ModFIotaFinitePlace
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProductFormulaHaar_NormIndex
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProductFormulaHaar_CardQuotientEqAbsNorm
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProductFormulaHaar_NormSt
import Theorems.Thm_PI_ProdFormulaE_normLoc_of_card
import Theorems.Thm_PI_ProdFormulaE_card_quotient_eq_absNorm


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsDedekindDomain NumberField
open PI PI.ProdFormulaE
namespace PI.ProdFormulaE
theorem _root_.solution : St.NormLoc := normLoc_of_card card_quotient_eq_absNorm
end PI.ProdFormulaE
