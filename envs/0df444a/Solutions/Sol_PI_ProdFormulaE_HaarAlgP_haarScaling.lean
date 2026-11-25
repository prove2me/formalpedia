-- Prove2me | solution 1 for PI.ProdFormulaE.HaarAlgP.haarScaling
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:38:38.505634+00:00
-- url     : https://prove2.me/submissions/d609e5ee-4d66-41ba-9176-4dae19711cb7

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProductFormulaHaar_HaarMain
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProductFormulaHaar_HaarScale
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProductFormulaHaar_HaarTransv
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProductFormulaHaar_HaarAlg
import Theorems.Thm_PI_ProdFormulaE_HaarAlgP_haarAlg_of
import Theorems.Thm_PI_ProdFormulaE_HaarBox_scale_box
import Theorems.Thm_PI_ProdFormulaE_HaarBox_transvection_box


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.ProdFormulaE PI.ProdFormulaE.HaarAlgP
namespace PI.ProdFormulaE.HaarAlgP
theorem _root_.solution : St.HaarAlg := by
  refine haarAlg_of ?_ ?_
  · intro K _ _ _ _ E _ _ _ _ _ _ n b μ _ i a ha
    exact PI.ProdFormulaE.HaarBox.scale_box b μ i a ha
  · intro K _ _ _ _ E _ _ _ _ n b t
    exact PI.ProdFormulaE.HaarBox.transvection_box b t
end PI.ProdFormulaE.HaarAlgP
