-- Prove2me | solution 1 for P2M_Formalism_DworkPowerSeriesWeights_Transfer_map_substTwo__c224fe382ce6
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:37:08.0718+00:00
-- url     : https://prove2.me/submissions/078922ff-837e-4448-9acb-d460db0dfb53

import Definitions.Def_Formalism_GaussJetBounds_FrameJetEval
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_Transfer

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Formalism Formalism.DworkPowerSeriesWeights
open Formalism.IncomingBounds MvPowerSeries
open Formalism.DworkPowerSeriesWeights.Transfer
variable {F K : Type} [Field F] [Field K] (φ : F →+* K) {d : ℕ}
namespace Formalism.DworkPowerSeriesWeights.Transfer
theorem _root_.solution (s : ZMod d) : map φ (s2' (K := F) s) = s2' s := by
  unfold s2'
  split_ifs <;> simp
end Formalism.DworkPowerSeriesWeights.Transfer
