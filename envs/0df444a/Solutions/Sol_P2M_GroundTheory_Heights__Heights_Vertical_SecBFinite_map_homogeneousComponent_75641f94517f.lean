-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Vertical_SecBFinite_map_homogeneousComponent_75641f94517f
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:48:49.265991+00:00
-- url     : https://prove2.me/submissions/6dcf1d37-3ea3-492a-9f8a-5993b1c94fb2

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_IntToFracInjective
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_PSecBFinite

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Vertical
open MvPolynomial NumberField IsDedekindDomain
noncomputable section
open GroundTheory.Heights₂.Heights.Vertical.SecBFinite
variable {σ R S : Type*} [CommRing R] [CommRing S]
namespace GroundTheory.Heights₂.Heights.Vertical.SecBFinite
theorem _root_.solution (f : R →+* S) (d : ℕ) (p : MvPolynomial σ R) :
    MvPolynomial.map f (homogeneousComponent d p) = homogeneousComponent d (MvPolynomial.map f p) := by
  ext m
  rw [coeff_map, coeff_homogeneousComponent, coeff_homogeneousComponent, coeff_map]
  split_ifs <;> simp
end GroundTheory.Heights₂.Heights.Vertical.SecBFinite
