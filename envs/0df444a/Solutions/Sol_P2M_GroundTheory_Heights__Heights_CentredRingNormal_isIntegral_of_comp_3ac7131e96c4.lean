-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_CentredRingNormal_isIntegral_of_comp_3ac7131e96c4
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:59:35.303544+00:00
-- url     : https://prove2.me/submissions/f8c693b0-5487-4600-b3b5-64578087c04d

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_HeightCentredRingNormal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_PSubringPrimeMaximal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_PCentredRingNormal

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
open NumberField IsDedekindDomain
open GroundTheory.Heights₂.Heights.CentredRingNormal
variable {L : Type} [Field L] [NumberField L]
omit [NumberField L]
namespace GroundTheory.Heights₂.Heights.CentredRingNormal
theorem _root_.solution {R R' : Type*} [CommRing R] [CommRing R'] [Algebra R L] [Algebra R' L]
    (f : R →+* R') (hf : (algebraMap R' L).comp f = algebraMap R L) {x : L}
    (hx : IsIntegral R x) : IsIntegral R' x := by
  obtain ⟨p, hp, hpx⟩ := hx
  exact ⟨p.map f, hp.map f, by rw [Polynomial.eval₂_map, hf]; exact hpx⟩
end GroundTheory.Heights₂.Heights.CentredRingNormal
