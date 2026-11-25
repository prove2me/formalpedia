-- Prove2me | solution 1 for P2M_Formalism_DworkPowerSeriesWeights_Transfer_map_substOne__fd74c6d8f087
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:37:07.164534+00:00
-- url     : https://prove2.me/submissions/29675594-c1a2-4599-95db-7f4f419fcbff

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
theorem _root_.solution (s : ZMod d) : map φ (s1' (K := F) s) = s1' s := by
  unfold s1'
  split_ifs <;> simp
end Formalism.DworkPowerSeriesWeights.Transfer
