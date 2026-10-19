-- Prove2me | solution 1 for PermanentRollout.ringKrullDim_le_of_isIntegral
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:02.589874+00:00
-- url     : https://prove2.me/submissions/e930cea9-b84f-46a1-b833-1b942e6d26c6

import Mathlib
import Definitions.Def_Permanent

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
open Ideal
variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
namespace PermanentRollout
theorem _root_.solution
    [Algebra.IsIntegral R S] :
    ringKrullDim S ≤ ringKrullDim R := by
  unfold ringKrullDim
  apply Order.krullDim_le_of_strictMono
    (PrimeSpectrum.comap (algebraMap R S))
  intro P Q hPQ
  exact Ideal.IsIntegral.comap_lt_comap hPQ
end PermanentRollout
