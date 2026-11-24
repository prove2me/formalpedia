-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_AuslanderBuchsbaumDepthLower_support_residueModule_5535d1c543f8
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:28:14.865457+00:00
-- url     : https://prove2.me/submissions/b5982b14-5a24-42c8-b9e3-b4128aea3200

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StAuslanderBuchsbaumDepthLower
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PAuslanderBuchsbaumDepthLower

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
open IsLocalRing CategoryTheory Limits Abelian RingTheory.Sequence
universe u
open GroundTheory.Heights₂.Heights.AuslanderBuchsbaumDepthLower
variable {R : Type u} [CommRing R] [IsLocalRing R]
namespace GroundTheory.Heights₂.Heights.AuslanderBuchsbaumDepthLower
theorem _root_.solution :
    Module.support R (residueModule R) = PrimeSpectrum.zeroLocus (maximalIdeal R) := by
  rw [(Shrink.linearEquiv R _).support_eq, Module.support_eq_zeroLocus, Ideal.annihilator_quotient]
end GroundTheory.Heights₂.Heights.AuslanderBuchsbaumDepthLower
