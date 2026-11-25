-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.WR.B.Am_conjTranspose
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:12:25.957887+00:00
-- url     : https://prove2.me/submissions/620f36d9-9033-43ae-a2a8-31276cbdc62f

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
theorem _root_.solution {s : ℂ} (hs : s = 1 ∨ s = -1) (y : E n) : (Am s y)ᴴ = Bm s y := by
  have hI : star Complex.I = -Complex.I := Complex.conj_I
  unfold Am Bm
  rw [conjTranspose_sub, conjTranspose_one, conjTranspose_smul, herm_conjTranspose, star_mul', star_of_pm hs, hI,
    neg_mul, neg_smul, sub_neg_eq_add]
end PositivityTheory.Rg.Sw.WR.B
