-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_LaurentLoc_toL_injective_4902110fbee0
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T04:37:39.111177+00:00
-- url     : https://prove2.me/submissions/adc4d9c1-922e-4d86-bc5b-e872a160b24c

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsSerrePoly
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PSerrePolyLaurent
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_LaurentLoc_expToInt_injective_8d604979af59
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_LaurentLoc_coeff_toL_50d5c86175e2

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
theorem _root_.solution : Function.Injective (toL S N) := fun p q h => by
  have h' : polyToLaurent S N p = polyToLaurent S N q := by rw [← coeff_toL, ← coeff_toL, h]
  exact AddMonoidAlgebra.coeff_injective (Finsupp.mapDomain_injective (expToInt_injective N) h')
end GroundTheory.Heights₂.Heights.Kleiman.LaurentLoc
