-- Prove2me | solution 1 for PositivityTheory.RgJS.NewtonIdentitiesAlt.aeval_esymm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T11:54:28.817118+00:00
-- url     : https://prove2.me/submissions/57478087-095a-4cc0-99c3-708a7c9b72f6

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
theorem _root_.solution (a : A → ℂ) (j : ℕ) : aeval a (esymm A ℂ j) = ev a j := by
  simp [esymm, ev, map_sum, map_prod]
end PositivityTheory.RgJS.NewtonIdentitiesAlt
