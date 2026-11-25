-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.WR.B.Bm_conjTranspose
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:12:28.82271+00:00
-- url     : https://prove2.me/submissions/62d4bfb8-828b-4a8f-9488-3fccaa6f0205

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_ClsBoundAlt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_ClsBoundA
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_B_herm_conjTranspose
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_B_star_of_pm

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
theorem _root_.solution {s : ℂ} (hs : s = 1 ∨ s = -1) (y : E n) : (Bm s y)ᴴ = Am s y := by
  have hI : star Complex.I = -Complex.I := Complex.conj_I
  unfold Am Bm
  rw [conjTranspose_add, conjTranspose_one, conjTranspose_smul, herm_conjTranspose, star_mul', star_of_pm hs, hI,
    neg_mul, neg_smul, ← sub_eq_add_neg]
end PositivityTheory.Rg.Sw.WR.B
