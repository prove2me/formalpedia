-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.coefOp_le_sqrt_hs
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:30:27.421287+00:00
-- url     : https://prove2.me/submissions/da322eae-035b-4ca9-9bcb-734a5f532fed

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_ExpInPPosDef
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_IntegrableOfDecayVG
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_InhabRep
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_FormalDegree_CoefOp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_coefOp_apply_le_frob
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_sqrt_hs_frobVG


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ}
namespace ReciprocityTheory.ChartRestriction.DS
theorem _root_.solution (A : Matrix (Fin n) (Fin n) ℂ) :
    ‖Matrix.toEuclideanCLM (𝕜 := ℂ) A‖ ≤ Real.sqrt (S7.hs A) := by
  refine ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _) fun v => ?_
  have h := coefOp_apply_le_frob A v
  rwa [← S7.sqrt_hs_frobVG A] at h
end ReciprocityTheory.ChartRestriction.DS
