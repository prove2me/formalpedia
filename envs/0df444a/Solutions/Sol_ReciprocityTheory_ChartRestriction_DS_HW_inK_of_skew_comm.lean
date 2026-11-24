-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.HW.inK_of_skew_comm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T13:57:24.264835+00:00
-- url     : https://prove2.me/submissions/85400a14-f972-4bc2-a47e-df2984fc2178

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_OpEqExp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_SingleMulJmComm

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
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.HW
open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7
variable {n : ℕ}
namespace ReciprocityTheory.ChartRestriction.DS.HW
theorem _root_.solution {ε : Fin n → Bool} {X : Matrix (Fin n) (Fin n) ℂ} (h1 : Xᴴ = -X)
    (h2 : X * Jm ε = Jm ε * X) : inK ε X := by
  unfold inK inG
  refine ⟨?_, h2⟩
  rw [h1, ← h2, neg_mul, neg_add_cancel]
end ReciprocityTheory.ChartRestriction.DS.HW
