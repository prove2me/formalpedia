-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FourB_ClosedPointOfGenericFibre_comap_ne_bot_of_isMaximal_2db500e960e1
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T01:30:13.96425+00:00
-- url     : https://prove2.me/submissions/889bd8cc-acc5-455c-8fae-2f403a87a633

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LocalDensities_StatementsClosedPointGenericFibre
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterDivSuppAB
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LocalDensities_PClosedPointOfGenericFibre
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FourB_ClosedPointOfGenericFibre_isMaximal_comap_of_isMaximal_b84c1c04496c

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FourB
open IsDedekindDomain NumberField
open GroundTheory.Heights₂.Heights.FourB.ClosedPointOfGenericFibre
namespace GroundTheory.Heights₂.Heights.FourB.ClosedPointOfGenericFibre
theorem _root_.solution (F : Type) [Field F] [NumberField F] (R : Type) [CommRing R]
    [Algebra (𝓞 F) R] [Algebra.FiniteType (𝓞 F) R] (M : Ideal R) (hM : M.IsMaximal) :
    M.comap (algebraMap (𝓞 F) R) ≠ ⊥ := by
  intro h
  have := isMaximal_comap_of_isMaximal F R M hM
  rw [h] at this
  exact RingOfIntegers.not_isField F (Ring.isField_iff_maximal_bot.mpr this)
end GroundTheory.Heights₂.Heights.FourB.ClosedPointOfGenericFibre
