-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.SP.lcp_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T11:49:01.284809+00:00
-- url     : https://prove2.me/submissions/84b0c46a-0c97-4200-af40-127babea28a5

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
theorem _root_.solution {Q' : Fm n} (c : ℂ) {T : Fm n →ₗ[ℂ] Fm n} (hT : LCP Q' T) : LCP Q' (c • T) := fun R => by
  simp only [LinearMap.smul_apply, hT R, mul_smul_comm]
end PositivityTheory.Rg.Sw.SP
