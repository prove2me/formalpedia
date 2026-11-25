-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LVs.TC.rot_inG
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:06:44.01522+00:00
-- url     : https://prove2.me/submissions/8f39af07-b41e-4333-825e-dcb42d7fbf0d

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_TCMatC
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_StarExpNegI
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_TC_star_exp_I
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_TC_star_exp_negI
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_TC_rot_eq
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_TC_inG_conjDiag


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix ComplexConjugate
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs PositivityTheory.Rg.Sw.LVs.TC
open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs
variable {n : ℕ}
namespace PositivityTheory.Rg.Sw.LVs.TC
theorem _root_.solution (j : ℕ) (θ : ℝ) : InG (rot (n := n) j θ) := by
  rw [rot_eq]
  refine inG_conjDiag _ _ (fun a => ?_) (fun a => ?_)
  · unfold dA; split_ifs
    · exact star_exp_I θ
    · exact star_exp_negI θ
  · unfold dB; split_ifs
    · exact star_exp_negI θ
    · exact star_exp_I θ
end PositivityTheory.Rg.Sw.LVs.TC
