-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_OrdPolynomialLocalization_comap_C_map_C_664793546d1d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T04:45:50.257486+00:00
-- url     : https://prove2.me/submissions/cf8cde0e-70ab-42e0-905a-4ba4373fe005

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_POrdPolynomialLocalization

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
open MvPolynomial IsLocalRing
namespace GroundTheory.Heights₂.Heights
namespace OrdPolynomialLocalization
theorem _root_.solution {R : Type*} [CommRing R] (σ : Type*) (p : Ideal R) :
    Ideal.comap (C : R →+* MvPolynomial σ R) (Ideal.map (C : R →+* MvPolynomial σ R) p) = p := by
  classical
  ext r
  rw [Ideal.mem_comap, MvPolynomial.mem_map_C_iff]
  constructor
  · intro h
    simpa using h 0
  · intro h m
    rw [coeff_C]
    split_ifs
    · exact h
    · exact p.zero_mem
end OrdPolynomialLocalization
end GroundTheory.Heights₂.Heights
