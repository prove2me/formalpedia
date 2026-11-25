-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.WR.B.posDef_one_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:12:31.503612+00:00
-- url     : https://prove2.me/submissions/5ef47c5a-90a9-4d98-98db-264f987239ba

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_ClsBoundAlt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_ClsBoundA
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_B_herm_conjTranspose

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
open scoped ComplexOrder
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR PositivityTheory.Rg.Sw.WR.B
open PositivityTheory.Rg.Sw
variable {n : ℕ}
namespace PositivityTheory.Rg.Sw.WR.B
theorem _root_.solution (y : E n) : (1 + herm y * herm y).PosDef := by
  have h := Matrix.posSemidef_conjTranspose_mul_self (herm y)
  rw [herm_conjTranspose] at h
  exact Matrix.PosDef.one.add_posSemidef h
end PositivityTheory.Rg.Sw.WR.B
