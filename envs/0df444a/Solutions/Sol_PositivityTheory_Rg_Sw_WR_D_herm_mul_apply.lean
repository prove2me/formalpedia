-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.WR.D.herm_mul_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T11:52:34.158814+00:00
-- url     : https://prove2.me/submissions/d6f0c620-43f2-42f4-b474-faec5729c6af

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_DensDefs
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_ContinuousEvX

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR PositivityTheory.Rg.Sw.WR.D
open PositivityTheory.Rg.Sw
variable {m n : ℕ}
namespace PositivityTheory.Rg.Sw.WR.D
theorem _root_.solution (y y' : E n) (i j : Fin n) :
    herm y i j * herm y' j i =
      (((y i j * y' i j + y j i * y' j i) / 2 : ℝ) : ℂ) + Complex.I * (((y i j * y' j i - y j i * y' i j) / 2 : ℝ) : ℂ) := by
  apply Complex.ext <;> simp [herm] <;> ring
end PositivityTheory.Rg.Sw.WR.D
