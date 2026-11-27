-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_BaseChangeAvoid_proof_7cc393463f22
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T04:55:10.632103+00:00
-- url     : https://prove2.me/submissions/b7482006-301c-4223-a609-eb309367835a

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_ConeBall
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PBaseChangeAvoid
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_BaseChangeAvoid_comap_eq_of_mem_minimalPrimes_4b21b6da26c6

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial
namespace GroundTheory.Heights₂.Heights
namespace BaseChangeAvoid
theorem _root_.solution : BaseChangeAvoid.Statement := by
  intro K _ _ n I u σ hI hu W hW h
  have hW' : W ∈ relComps (I.map (MvPolynomial.map σ)) := by
    by_contra hn
    rw [Finsupp.mem_support_iff] at hW
    exact hW (by simp [fundCycle, Finsupp.onFinset_apply, hn])
  have := hI.isPrime
  have hc := BaseChangeAvoid.comap_eq_of_mem_minimalPrimes σ I hW'.1
  apply hu
  rw [← hc, Ideal.mem_comap]
  convert h using 1
  simp [linForm, map_sum]
end BaseChangeAvoid
end GroundTheory.Heights₂.Heights
