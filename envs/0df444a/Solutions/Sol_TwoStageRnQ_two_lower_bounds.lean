-- Prove2me | solution 1 for TwoStageRnQ.two_lower_bounds
-- status  : ACCEPTED   (prove)
-- author  : @beatlesmania
-- created : 2026-11-17T00:30:58.030511+00:00
-- url     : https://prove2.me/submissions/31c84888-5ecd-4a4f-bbf7-e67bbb5dddaa

import Theorems.Thm_TwoStageRnQ_Ltwo_le_LBsp
import Theorems.Thm_TwoStageRnQ_LBsp_le_OPTsh

/-!
Proposition 2 from its two halves: `L_two ≤ LB^SP` (analytic,
`TwoStageRnQ.Ltwo_le_LBsp`) and `LB^SP ≤ OPT^sh`
(`TwoStageRnQ.LBsp_le_OPTsh`).
-/

namespace TwoStageRnQ

theorem _root_.solution (P : Params) :
    P.Ltwo ≤ P.LBsp ∧ ENNReal.ofReal P.LBsp ≤ OPTsh P :=
  ⟨TwoStageRnQ.Ltwo_le_LBsp P, TwoStageRnQ.LBsp_le_OPTsh P⟩

end TwoStageRnQ
