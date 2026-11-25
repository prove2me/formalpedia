-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.WR.B.Am_mul_Bm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:07:23.825789+00:00
-- url     : https://prove2.me/submissions/7645ec88-675e-4fc9-b5b6-f8e22dcb0af9

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_ClsBoundAlt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_ClsBoundA
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_B_Is_sq

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
theorem _root_.solution {s : ℂ} (hs : s = 1 ∨ s = -1) (y : E n) : Am s y * Bm s y = 1 + herm y * herm y := by
  unfold Am Bm
  simp only [sub_mul, mul_add, one_mul, mul_one, smul_mul_smul_comm, Is_sq hs, neg_one_smul]
  abel
end PositivityTheory.Rg.Sw.WR.B
