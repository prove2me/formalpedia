-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_aeval_genericPt_77930e4eb734
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T04:02:30.024997+00:00
-- url     : https://prove2.me/submissions/c01d09df-efc5-47cc-abab-11ea11182c03

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_Objects
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_IsSemipositiveOn
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_Objects

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman
open MvPolynomial
noncomputable section
universe u v w
variable (k : Type u) [Field k] (N : ℕ)
namespace GroundTheory.Heights₂.Heights.Kleiman
theorem _root_.solution (f : Poly k N) :
    aeval (genericPt k N) f = algebraMap (Poly k N) (FractionRing (Poly k N)) f := by
  induction f using MvPolynomial.induction_on with
  | C a =>
    rw [aeval_C, IsScalarTower.algebraMap_apply k (Poly k N) (FractionRing (Poly k N))]
    rfl
  | add p q hp hq => rw [map_add, map_add, hp, hq]
  | mul_X p i hp => rw [map_mul, map_mul, hp, aeval_X, genericPt]
end GroundTheory.Heights₂.Heights.Kleiman
