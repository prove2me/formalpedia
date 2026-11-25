-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.WR.Ib.continuous_chr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T11:59:53.878593+00:00
-- url     : https://prove2.me/submissions/08bcc00e-a49f-4dcb-8b74-8776c3f937fd

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_ClsBoundAlt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_IntegrableOfBound
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_Ib_differentiable_chr

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
theorem _root_.solution (t : ℝ) (β : E n) : Continuous (chr t β) := (differentiable_chr t β).continuous
end PositivityTheory.Rg.Sw.WR.Ib
