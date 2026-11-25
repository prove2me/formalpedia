-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.WR.D.Moll.ip_sub_right
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T11:54:36.024894+00:00
-- url     : https://prove2.me/submissions/8fdef37e-de45-438f-9fde-73452acff501

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_MollIdA
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_MollId

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR PositivityTheory.Rg.Sw.WR.D PositivityTheory.Rg.Sw.WR.D.Moll
open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR PositivityTheory.Rg.Sw.WR.D
variable {n : ℕ}
namespace PositivityTheory.Rg.Sw.WR.D.Moll
theorem _root_.solution (y u w : E n) : ip y (u - w) = ip y u - ip y w := by
  simp only [ip, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]
end PositivityTheory.Rg.Sw.WR.D.Moll
