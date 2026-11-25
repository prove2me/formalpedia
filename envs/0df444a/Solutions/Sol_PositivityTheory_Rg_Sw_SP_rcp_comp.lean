-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.SP.rcp_comp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T11:50:44.951093+00:00
-- url     : https://prove2.me/submissions/716b8227-b19f-4247-9765-9fb8adc998ad

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
theorem _root_.solution {T U : Fm n →ₗ[ℂ] Fm n} (hT : RCP T) (hU : RCP U) : RCP (T ∘ₗ U) := fun R q => by
  simp only [LinearMap.comp_apply, hU R q, hT _ q]
end PositivityTheory.Rg.Sw.SP
