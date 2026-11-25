-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_LaurentLoc_expToInt_injective_8d604979af59
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T04:01:23.30696+00:00
-- url     : https://prove2.me/submissions/86ec1dab-9892-4c2e-961e-11a00ce6c431

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsSerrePoly
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PSerrePolyLaurent

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman
open MvPolynomial
noncomputable section
universe u
open GroundTheory.Heights₂.Heights.Kleiman.LaurentLoc
variable (S : Type u) [CommRing S] (N : ℕ)
namespace GroundTheory.Heights₂.Heights.Kleiman.LaurentLoc
theorem _root_.solution : Function.Injective (expToInt N) := fun e f h =>
  Finsupp.ext fun j => by
    have := congrFun h j
    simpa [expToInt] using this
end GroundTheory.Heights₂.Heights.Kleiman.LaurentLoc
