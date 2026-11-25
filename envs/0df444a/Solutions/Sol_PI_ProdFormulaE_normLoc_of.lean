-- Prove2me | solution 1 for PI.ProdFormulaE.normLoc_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:28:58.476967+00:00
-- url     : https://prove2.me/submissions/e03d898d-b216-43c7-b545-3cdf44b73227

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProductFormulaHaar_ResCharIff
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProductFormulaHaar_ModFIotaFinitePlace
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProductFormulaHaar_NormIndex
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProductFormulaHaar_CardQuotientEqAbsNorm
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProductFormulaHaar_NormSt
import Theorems.Thm_PI_ProdFormulaE_modF_iota_finitePlace


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
theorem _root_.solution (hI : IndexFormula) (hC : CardStep) : St.NormLoc :=
  fun _F _ _ p _K _ _ _ _ ι hd hv z => modF_iota_finitePlace p ι hI hC hd hv z
end PI.ProdFormulaE
