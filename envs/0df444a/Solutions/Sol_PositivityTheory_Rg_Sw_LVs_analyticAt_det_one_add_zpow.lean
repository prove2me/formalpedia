-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LVs.analyticAt_det_one_add_zpow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T11:47:34.361874+00:00
-- url     : https://prove2.me/submissions/99fff5cf-ed3f-4784-9637-405a1c0e5495

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_CayleyA
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_CayleyG
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_analyticAt_det

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
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
namespace PositivityTheory.Rg.Sw.LVs
theorem _root_.solution {ι : Type} [Fintype ι] [DecidableEq ι] (t : ℤ) :
    AnalyticAt ℂ (fun T : Matrix ι ι ℂ => (1 + T).det ^ t) 0 := by
  have h1 : AnalyticAt ℂ (fun T : Matrix ι ι ℂ => (1 + T).det) 0 :=
    (analyticAt_det (1 + 0)).comp (analyticAt_const.add analyticAt_id)
  exact h1.zpow (by simp)
end PositivityTheory.Rg.Sw.LVs
