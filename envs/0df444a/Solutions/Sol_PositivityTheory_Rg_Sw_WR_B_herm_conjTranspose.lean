-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.WR.B.herm_conjTranspose
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T11:58:00.817054+00:00
-- url     : https://prove2.me/submissions/877dd8aa-d3d5-4c6e-89db-03b7b835d45e

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_ClsBoundAlt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_ClsBoundA
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_B_herm_apply

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
theorem _root_.solution (y : E n) : (herm y)ᴴ = herm y := by
  ext i j
  rw [conjTranspose_apply, herm_apply, herm_apply]
  apply Complex.ext <;> simp <;> ring
end PositivityTheory.Rg.Sw.WR.B
