-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Xi.xiExists_of_induction_steps
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:51:34.130816+00:00
-- url     : https://prove2.me/submissions/66f57552-1dbc-4dd1-abc7-21eddc36be66

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_InductiveHeisenbergInputs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_XiExists2
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_aAll_of
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_bAll_of
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_xiExists_of

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Xi
open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
namespace ReciprocityTheory.ChartRestriction.DS.Xi
theorem _root_.solution (hAb : AStepBase) (hAs : AStepSucc) (hBb : BStepBase) (hBs : BStepSucc)
    (hC : CoefStep) (hX : XiIntStep) : XiExists :=
  xiExists_of (aAll_of hAb hAs) (fun k r hk => bAll_of hBb hBs k r hk (1 / 2) (by norm_num) le_rfl) hC hX
end ReciprocityTheory.ChartRestriction.DS.Xi
