-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Kleiman_coneMap_coeff_88bc714e5f8c
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T04:07:05.98448+00:00
-- url     : https://prove2.me/submissions/18c49b06-e3f7-49b4-b37c-2a76fb197a39

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_IsSemipositiveOn
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_Bundle
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_Objects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_CoordIdealIsMultiProjPrime
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Kleiman_coneMap_monomial_a001c687d6e0

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Kleiman
open MvPolynomial
noncomputable section
open ReciprocityTheory.ChartRestriction.G.Geo
variable {S : Type} [CommRing S] {σ : Type} {Ω : Type} [Field Ω] [Algebra S Ω]
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Kleiman
theorem _root_.solution (x : σ → Ω) (f : MvPolynomial σ S) (d : ℕ) :
    (coneMap S x f).coeff d = aeval x (homogeneousComponent d f) := by
  induction f using MvPolynomial.induction_on' with
  | monomial s a =>
    rw [coneMap_monomial, Polynomial.coeff_C_mul_X_pow,
      homogeneousComponent_of_mem (isHomogeneous_monomial (d := s) a (n := s.sum fun _ e => e) rfl)]
    by_cases h : d = s.sum fun _ e => e
    · rw [if_pos h, if_pos h, aeval_monomial]
    · rw [if_neg h, if_neg h, map_zero]
  | add p q hp hq =>
    rw [map_add, Polynomial.coeff_add, hp, hq, map_add, map_add]
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Kleiman
