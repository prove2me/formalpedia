-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.HSt.iteratedDeriv_eq_of_eventuallyEq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T11:41:10.47356+00:00
-- url     : https://prove2.me/submissions/c6d11ca7-88cb-42b3-8778-54c98881b650

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_CayleyCosetSums_IteratedDerivEqOfEventuallyEq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Filter Topology Set
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.HSt
namespace PositivityTheory.Rg.Sw.HSt
theorem _root_.solution {f g : ℂ → ℂ} {s : ℂ} (h : f =ᶠ[𝓝 s] g) (k : ℕ) :
    iteratedDeriv k f s = iteratedDeriv k g s := by
  rw [← iteratedDerivWithin_univ, ← iteratedDerivWithin_univ]
  exact Filter.EventuallyEq.iteratedDerivWithin_eq (by simpa using h) h.eq_of_nhds
end PositivityTheory.Rg.Sw.HSt
