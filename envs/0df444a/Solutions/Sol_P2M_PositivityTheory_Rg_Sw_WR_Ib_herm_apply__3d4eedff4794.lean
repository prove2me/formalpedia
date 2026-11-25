-- Prove2me | solution 1 for P2M_PositivityTheory_Rg_Sw_WR_Ib_herm_apply__3d4eedff4794
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T08:50:19.988706+00:00
-- url     : https://prove2.me/submissions/0bf8faf8-6078-4932-a31a-faef4de0a6f2

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_ClsBoundAlt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_IntegrableOfBound

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Matrix
open scoped ContDiff
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR PositivityTheory.Rg.Sw.WR.Ib
open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR
variable {n : ℕ}
namespace PositivityTheory.Rg.Sw.WR.Ib
theorem _root_.solution (x : E n) (i j : Fin n) :
    herm x i j = ((x i j + x j i : ℝ) : ℂ) / 2 + Complex.I * ((x i j - x j i : ℝ) : ℂ) / 2 := rfl
end PositivityTheory.Rg.Sw.WR.Ib
