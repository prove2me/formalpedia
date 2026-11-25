-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LC.CoreA.PosH.re_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T11:46:01.966807+00:00
-- url     : https://prove2.me/submissions/dd0ac061-d406-455c-b1f5-3f134116ac97

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_CoreSt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_ZeroRight

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LC
open PositivityTheory.Rg.Sw.LC.CoreA
variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable {φ : V → V → ℂ}
open PositivityTheory.Rg.Sw.LC.CoreA.PosH
variable (h : PosH φ)
include h
namespace PositivityTheory.Rg.Sw.LC.CoreA.PosH
theorem _root_.solution (v : V) : 0 ≤ (φ v v).re := by
  by_cases hv : v = 0
  · subst hv; simp [h.zero_right]
  · exact (h.pos v hv).le
end PositivityTheory.Rg.Sw.LC.CoreA.PosH
