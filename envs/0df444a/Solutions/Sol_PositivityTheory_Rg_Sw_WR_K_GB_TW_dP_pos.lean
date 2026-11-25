-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.WR.K.GB.TW.dP_pos
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:00:54.01788+00:00
-- url     : https://prove2.me/submissions/c74d23f3-8b46-4320-b7ff-4965ca368865

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_Lagr
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_GBTwist
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_K_GB_TW_herm_isHermitian

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
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR PositivityTheory.Rg.Sw.WR.K PositivityTheory.Rg.Sw.WR.K.GB
open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR
open PositivityTheory.Rg.Sw.WR.K.GB.TW
variable {n : ℕ}
namespace PositivityTheory.Rg.Sw.WR.K.GB.TW
theorem _root_.solution (y : E n) : 0 < dP y := by
  have hH := herm_isHermitian y
  have h1 : (1 + herm y * herm y).PosDef := by
    have := (Matrix.PosDef.one (n := Fin n) (R := ℂ)).add_posSemidef
      (posSemidef_conjTranspose_mul_self (herm y))
    rwa [hH.eq] at this
  exact (Complex.pos_iff.1 h1.det_pos).1
end PositivityTheory.Rg.Sw.WR.K.GB.TW
