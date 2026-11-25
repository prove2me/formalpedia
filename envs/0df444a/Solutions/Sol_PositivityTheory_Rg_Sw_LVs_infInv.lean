-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LVs.infInv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:34:06.327278+00:00
-- url     : https://prove2.me/submissions/d431dcaa-84a5-48cc-9983-54ff2ef94431

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_InfInvA
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_IILeft
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_DetOneAddSmulSingleSame
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_FderivXZxSkew
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_InfInv
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_II_infInv_of
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_II_cDiff
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_II_lawDeriv
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_II_leftDeriv
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_II_ptId


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Matrix
open scoped ContDiff
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs
namespace PositivityTheory.Rg.Sw.LVs
theorem _root_.solution : InfInv := II.infInv_of II.leftDeriv II.lawDeriv II.ptId II.cDiff
end PositivityTheory.Rg.Sw.LVs
