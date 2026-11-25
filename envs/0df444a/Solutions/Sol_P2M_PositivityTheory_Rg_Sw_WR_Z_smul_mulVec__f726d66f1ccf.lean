-- Prove2me | solution 1 for P2M_PositivityTheory_Rg_Sw_WR_Z_smul_mulVec__f726d66f1ccf
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T08:58:08.755908+00:00
-- url     : https://prove2.me/submissions/eae14f41-ba47-4a6a-a6f2-0f15daa8feda

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
theorem _root_.solution (c : ℂ) (M : Matrix (Fin n) (Fin n) ℂ) (v : Fin n → ℂ) : (c • M) *ᵥ v = c • (M *ᵥ v) := by
  ext i
  simp [mulVec, dotProduct, Finset.mul_sum, mul_assoc]
end PositivityTheory.Rg.Sw.WR.Z
