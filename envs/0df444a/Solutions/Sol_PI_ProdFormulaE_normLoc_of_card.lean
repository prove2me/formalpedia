-- Prove2me | solution 1 for PI.ProdFormulaE.normLoc_of_card
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:35:32.572447+00:00
-- url     : https://prove2.me/submissions/87f90c72-88b0-4b5a-b295-446c2ee2c6c2

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProductFormulaHaar_ResCharIff
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProductFormulaHaar_ModFIotaFinitePlace
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProductFormulaHaar_NormIndex
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProductFormulaHaar_CardQuotientEqAbsNorm
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProductFormulaHaar_NormSt
import Theorems.Thm_PI_ProdFormulaE_normLoc_of
import Theorems.Thm_PI_ProdFormulaE_modulus_mul_card_quotient


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
theorem _root_.solution (hC : CardStep) : St.NormLoc := normLoc_of modulus_mul_card_quotient hC
end PI.ProdFormulaE
