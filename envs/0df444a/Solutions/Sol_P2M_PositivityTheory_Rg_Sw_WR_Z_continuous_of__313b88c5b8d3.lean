-- Prove2me | solution 1 for P2M_PositivityTheory_Rg_Sw_WR_Z_continuous_of__313b88c5b8d3
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T08:50:45.733065+00:00
-- url     : https://prove2.me/submissions/3fc0e5be-a5c1-4510-baa9-2792db4b5e8d

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_ClsGainSt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_ClsGainA

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
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR PositivityTheory.Rg.Sw.WR.Z
variable {n : ℕ}
namespace PositivityTheory.Rg.Sw.WR.Z
theorem _root_.solution : Continuous fun B : MC n => Matrix.of B :=
  continuous_matrix fun i j => continuous_apply_apply i j
end PositivityTheory.Rg.Sw.WR.Z
