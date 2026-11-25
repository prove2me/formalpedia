-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.SP.lcp_comp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T11:47:51.636061+00:00
-- url     : https://prove2.me/submissions/56bc0495-d975-41b5-acad-6484503a1b94

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
theorem _root_.solution {Q' : Fm n} {T U : Fm n →ₗ[ℂ] Fm n} (hT : LCP Q' T) (hU : LCP Q' U) : LCP Q' (T ∘ₗ U) := fun R => by
  simp only [LinearMap.comp_apply, hU R, hT _]
end PositivityTheory.Rg.Sw.SP
