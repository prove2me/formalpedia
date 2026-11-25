-- Prove2me | solution 1 for PI.ProdFormulaE.TrIntP.norm_trace_le_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:14:14.009066+00:00
-- url     : https://prove2.me/submissions/cca0435b-e616-45ef-a08f-3e37518d9bed

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProductFormulaHaar_ResCharIff
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProductFormulaHaar_NormTraceLeOne
import Theorems.Thm_PI_ProdFormulaE_TrIntP_norm_le_one_of_isIntegral

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.ProdFormulaE PI.ProdFormulaE.TrIntP
namespace PI.ProdFormulaE.TrIntP
theorem _root_.solution : St.TrInt := by
  intro ℓ _ K _ _ _ w hw
  exact norm_le_one_of_isIntegral (Algebra.isIntegral_trace hw)
end PI.ProdFormulaE.TrIntP
