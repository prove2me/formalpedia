-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.WR.Z.ext
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:45:03.634844+00:00
-- url     : https://prove2.me/submissions/a18c8350-9093-44e4-b10e-f3654a31e97f

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_ClsGainSt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_ClsGainA
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_Z_isOpen_OmS
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_Z_herm_mem_OmS
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_Z_an_clsC
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_Z_clsC_herm

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
theorem _root_.solution : Ext := by
  intro n s hs
  refine ⟨isOpen_OmS s, herm_mem_OmS s hs, fun z p q R => ⟨fun B hB => an_clsC s z p q R B hB, clsC_herm s z p q R⟩⟩
end PositivityTheory.Rg.Sw.WR.Z
