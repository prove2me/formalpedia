-- Prove2me | solution 1 for P2M_PositivityTheory_Rg_Sw_WR_K_GB_Inv_two_le_top__23b5670f2749
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T08:50:23.987804+00:00
-- url     : https://prove2.me/submissions/d6ff9a6b-3d4e-4c27-b5df-2c873acab821

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_ClsGainBSt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_GBInvar

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Finset
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR PositivityTheory.Rg.Sw.WR.K PositivityTheory.Rg.Sw.WR.K.GB
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ}
open PositivityTheory.Rg.Sw.WR.K.GB.Inv
namespace PositivityTheory.Rg.Sw.WR.K.GB.Inv
theorem _root_.solution : (2 : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := by
  rw [show (2 : WithTop ℕ∞) = ((2 : ℕ∞) : WithTop ℕ∞) from rfl]
  exact WithTop.coe_le_coe.2 le_top
end PositivityTheory.Rg.Sw.WR.K.GB.Inv
