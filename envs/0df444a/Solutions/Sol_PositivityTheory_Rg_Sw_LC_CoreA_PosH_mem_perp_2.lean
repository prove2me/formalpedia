-- Prove2me | solution 2 for PositivityTheory.Rg.Sw.LC.CoreA.PosH.mem_perp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T05:23:50.663212+00:00
-- url     : https://prove2.me/submissions/691b1411-5da4-4a54-8fa3-b2e77e352856

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
theorem _root_.solution (W : Submodule ℂ V) (v : V) : v ∈ h.perp W ↔ ∀ w ∈ W, φ w v = 0 := Iff.rfl
end PositivityTheory.Rg.Sw.LC.CoreA.PosH
