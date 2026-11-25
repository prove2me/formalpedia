-- Prove2me | solution 1 for PI.ProdFormulaE.Assemble.prodFormulaE_of_haar
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T11:03:45.977905+00:00
-- url     : https://prove2.me/submissions/52aa533d-321b-4aef-99c8-0b03e774a421

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_ProdFormulaE
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProductFormulaHaar_ProdFormulaEOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProductFormulaHaar_NormSt
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProductFormulaHaar_SumLocalTrace
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProductFormulaHaar_NormTraceLeOne
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProductFormulaHaar_ResChar
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProductFormulaHaar_Assemble
import Theorems.Thm_PI_ProdFormulaE_ResCharP_eq_iff_mem_asIdeal
import Theorems.Thm_PI_ProdFormulaE_Top_prodFormulaE_of
import Theorems.Thm_PI_ProdFormulaE_TrIntP_norm_trace_le_one
import Theorems.Thm_PI_ProdFormulaE_Tr_sumLocalTrace
import Theorems.Thm_PI_ProdFormulaE_modulus_eq_finitePlace


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.ProdFormulaE PI.ProdFormulaE.Assemble
namespace PI.ProdFormulaE.Assemble
theorem _root_.solution (hH : St.HaarAlg) : PI.ProdFormulaE.ProdFormulaE :=
  Top.prodFormulaE_of hH modulus_eq_finitePlace Tr.sumLocalTrace TrIntP.norm_trace_le_one ResCharP.eq_iff_mem_asIdeal
end PI.ProdFormulaE.Assemble
