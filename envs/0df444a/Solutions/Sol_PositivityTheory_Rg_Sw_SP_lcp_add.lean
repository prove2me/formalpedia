-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.SP.lcp_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T11:47:49.268122+00:00
-- url     : https://prove2.me/submissions/919d208b-e713-42cd-a216-3ae33d627e8e

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
theorem _root_.solution {Q' : Fm n} {T U : Fm n →ₗ[ℂ] Fm n} (hT : LCP Q' T) (hU : LCP Q' U) : LCP Q' (T + U) := fun R => by
  simp only [LinearMap.add_apply, hT R, hU R, mul_add]
end PositivityTheory.Rg.Sw.SP
