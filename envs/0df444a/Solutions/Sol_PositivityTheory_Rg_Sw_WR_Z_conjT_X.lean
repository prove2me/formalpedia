-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.WR.Z.conjT_X
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:19:37.321897+00:00
-- url     : https://prove2.me/submissions/38d66735-b5a8-43c8-a349-10f08e6cfc5b

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_ClsGainSt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_ClsGainA
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_Z_herm_isHermitian

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
theorem _root_.solution (s : ℂ) (hs : s = 1 ∨ s = -1) (y : E n) :
    (1 - (Complex.I * s) • herm y)ᴴ = 1 + (Complex.I * s) • herm y := by
  have hst : star (Complex.I * s) = -(Complex.I * s) := by
    rcases hs with rfl | rfl <;> simp [Complex.conj_I]
  rw [conjTranspose_sub, conjTranspose_one, conjTranspose_smul, hst, herm_isHermitian y, neg_smul, sub_neg_eq_add]
end PositivityTheory.Rg.Sw.WR.Z
