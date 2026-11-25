-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.WR.K.GB.cauchyW
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:20:47.664639+00:00
-- url     : https://prove2.me/submissions/7830ce47-b98e-4b12-8cea-0ba679f68299

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_ClsGainBSt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_GBCauchy
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_K_GB_cauchy_gen

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Metric
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR PositivityTheory.Rg.Sw.WR.K PositivityTheory.Rg.Sw.WR.K.GB
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ}
namespace PositivityTheory.Rg.Sw.WR.K.GB
theorem _root_.solution : CauchyW := by
  intro n F U hU hF b₀ ρ hρ hP M hM L
  exact cauchy_gen hU hF M L b₀ ρ hρ hP hM
end PositivityTheory.Rg.Sw.WR.K.GB
