-- Prove2me | solution 1 for PositivityTheory.RgJS.NewtonIdentitiesAlt.ev_card
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T11:56:13.982966+00:00
-- url     : https://prove2.me/submissions/4abe496d-1836-43e4-ac61-90d36eeb219f

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_JacquetShalikaBounds_AbsoluteRigidity_NewtonLow
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_JacquetShalikaBounds_AbsoluteRigidity_NewtonLowerBounds_NewtonIdentitiesLowDegree

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial Finset
open PositivityTheory PositivityTheory.RgJS PositivityTheory.RgJS.NewtonIdentitiesAlt
variable {A : Type} [Fintype A]
namespace PositivityTheory.RgJS.NewtonIdentitiesAlt
theorem _root_.solution (a : A → ℂ) : ev a (Fintype.card A) = ∏ i, a i := by
  rw [ev, ← Finset.card_univ, Finset.powersetCard_self, Finset.sum_singleton]
end PositivityTheory.RgJS.NewtonIdentitiesAlt
