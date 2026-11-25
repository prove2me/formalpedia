-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.WR.K.GB.TW.herm_isHermitian
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T11:52:31.650805+00:00
-- url     : https://prove2.me/submissions/22e4d469-8d6b-48a6-8998-b80d59d7a897

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_Lagr
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_GBTwist

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
theorem _root_.solution (y : E n) : (herm y).IsHermitian := by
  ext i j
  simp only [conjTranspose_apply, herm]
  apply Complex.ext <;> simp <;> ring
end PositivityTheory.Rg.Sw.WR.K.GB.TW
