-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Kleiman_coneMap_monomial_a001c687d6e0
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T03:28:14.889805+00:00
-- url     : https://prove2.me/submissions/3ef66d51-95cf-43fe-a937-17b6cbce4c4d

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_IsSemipositiveOn
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_Bundle
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_Objects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_CoordIdealIsMultiProjPrime

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
theorem _root_.solution (x : σ → Ω) (s : σ →₀ ℕ) (a : S) :
    coneMap S x (monomial s a) = Polynomial.C (algebraMap S Ω a * s.prod fun v e => x v ^ e) *
      Polynomial.X ^ (s.sum fun _ e => e) := by
  simp only [coneMap, aeval_monomial, Finsupp.prod, Finsupp.sum, mul_pow, Finset.prod_mul_distrib,
    Finset.prod_pow_eq_pow_sum, map_mul, map_prod, map_pow, Polynomial.algebraMap_apply]
  ring
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Kleiman
