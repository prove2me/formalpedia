-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.WR.D.cardAddB
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T11:54:37.034795+00:00
-- url     : https://prove2.me/submissions/f445a467-f84e-4bfe-ac97-b6cc811c7174

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_DensDefs
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_CardAddB

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology Metric
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR PositivityTheory.Rg.Sw.WR.D
open PositivityTheory.Rg.Sw
namespace PositivityTheory.Rg.Sw.WR.D
theorem _root_.solution {m : ℕ} (ε : Fin m → Bool) :
    (Finset.univ.filter fun a => ε a = true).card + (Finset.univ.filter fun a => ε a = false).card = m := by
  have := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin m))) (fun a => ε a = true)
  simpa using this
end PositivityTheory.Rg.Sw.WR.D
