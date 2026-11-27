-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.SP.rcp_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T05:20:24.936804+00:00
-- url     : https://prove2.me/submissions/ffcf1ff2-4665-4f1e-897d-30dda48375d2

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MinorFormulas_CayDivOf
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MinorFormulas_CayDivA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.SP
variable {n : ℕ}
namespace PositivityTheory.Rg.Sw.SP
theorem _root_.solution (c : ℂ) {T : Fm n →ₗ[ℂ] Fm n} (hT : RCP T) : RCP (c • T) := fun R q => by
  simp only [LinearMap.smul_apply, hT R q, smul_mul_assoc]
end PositivityTheory.Rg.Sw.SP
