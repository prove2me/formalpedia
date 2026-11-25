-- Prove2me | solution 1 for PositivityTheory.Rg.Rs.StrStepA.sd_norm_cpow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T11:38:46.874017+00:00
-- url     : https://prove2.me/submissions/6600f052-b1b9-4613-a856-3c41d63228dd

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ResidualSpectrum_SliceTensors_SdNormCpow

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Rs PositivityTheory.Rg.Rs.StrStepA
namespace PositivityTheory.Rg.Rs.StrStepA
theorem _root_.solution (q : ℕ) (hq : 1 < q) (x : ℝ) : ‖(q : ℂ) ^ (-(x : ℂ))‖ = (q : ℝ) ^ (-x) := by
  rw [Complex.norm_natCast_cpow_of_pos (by omega)]
  simp
end PositivityTheory.Rg.Rs.StrStepA
