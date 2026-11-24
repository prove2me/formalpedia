-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_comap_C_map_C_polynomial_5a2ce1497410
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:12:35.504865+00:00
-- url     : https://prove2.me/submissions/5efb9b89-a4ae-4207-8b95-9763cd10ebc3

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsBlowUpHorizontalMult
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PPolynomialLocalizedLength

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NumbersDVR
open IsLocalRing
universe u
namespace GroundTheory.Heights₂.Heights.NumbersDVR
theorem _root_.solution {R : Type*} [CommRing R] (p : Ideal R) :
    (p.map (Polynomial.C : R →+* Polynomial R)).comap (Polynomial.C : R →+* Polynomial R) = p := by
  ext r
  rw [Ideal.mem_comap, Ideal.mem_map_C_iff]
  constructor
  · intro h
    simpa using h 0
  · intro h n
    rw [Polynomial.coeff_C]
    split_ifs
    · exact h
    · exact p.zero_mem
end GroundTheory.Heights₂.Heights.NumbersDVR
