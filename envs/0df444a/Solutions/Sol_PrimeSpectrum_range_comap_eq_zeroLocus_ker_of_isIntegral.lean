-- Prove2me | solution 1 for PrimeSpectrum.range_comap_eq_zeroLocus_ker_of_isIntegral
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/ed0c95f0-1c8d-5f03-8f77-334d7e2d4387

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_PrimeSpectrum_range_comap_eq_zeroLocus_ker_of_isIntegral

set_option autoImplicit false

universe u v

open PrimeSpectrum

theorem solution
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] (f : R →+* S) (hf : f.IsIntegral) :
    Set.range (PrimeSpectrum.comap f) = PrimeSpectrum.zeroLocus (RingHom.ker f) := by
  rw [← (PrimeSpectrum.isClosedMap_comap_of_isIntegral f hf).isClosed_range.closure_eq,
    PrimeSpectrum.closure_range_comap]

#print axioms solution

end S_PrimeSpectrum_range_comap_eq_zeroLocus_ker_of_isIntegral
end P2MW
export P2MW.S_PrimeSpectrum_range_comap_eq_zeroLocus_ker_of_isIntegral (solution)
