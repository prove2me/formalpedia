-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.WR.D.continuous_evX
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T11:50:03.399688+00:00
-- url     : https://prove2.me/submissions/78e35370-4470-400f-aef6-1a8df74d67b0

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_DensDefs
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_ContinuousEvX

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR PositivityTheory.Rg.Sw.WR.D
open PositivityTheory.Rg.Sw
variable {m n : ℕ}
namespace PositivityTheory.Rg.Sw.WR.D
theorem _root_.solution (P : PX m n) : Continuous fun x : Fin m → Fin n → ℂ => evX P x := by
  refine (MvPolynomial.continuous_eval P).comp (continuous_pi fun k => ?_)
  split_ifs
  · exact continuous_star.comp ((continuous_apply _).comp (continuous_apply _))
  · exact (continuous_apply _).comp (continuous_apply _)
end PositivityTheory.Rg.Sw.WR.D
