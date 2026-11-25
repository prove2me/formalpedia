-- Prove2me | solution 1 for PI.Dv.ProjGramW.dvProjGram_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T11:01:23.929396+00:00
-- url     : https://prove2.me/submissions/57494fca-81fb-47eb-bfaf-defca21df94a

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProjectionGramMatrices_AlgebraMapNeZeroOfNotMem
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProjectionGramMatrices_IdxDet
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProjectionGramMatrices_DvProjGramOf
import Theorems.Thm_P2M_PI_Dv_ProjGramW_dvProjGram_of__4fc85b4471e1
import Theorems.Thm_PI_Dv_ProjGramW_idxDet_of


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.Dv PI.Dv.ProjGramW
open NumberField IsDedekindDomain Formalism.BasicNotions
namespace PI.Dv.ProjGramW
theorem _root_.solution (hA : ProjA) (hI : IdxCalc) : gram_det_kernel_base_level :=
  dvProjGram_of' hA hI (idxDet_of hI)
end PI.Dv.ProjGramW
