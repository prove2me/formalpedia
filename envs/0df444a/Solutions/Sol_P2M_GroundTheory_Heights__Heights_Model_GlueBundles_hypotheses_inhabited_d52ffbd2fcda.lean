-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Model_GlueBundles_hypotheses_inhabited_d52ffbd2fcda
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T04:04:49.6298+00:00
-- url     : https://prove2.me/submissions/6d03a449-bea1-46dc-8dd2-f75946e47511

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_Objects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_BundleObjects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_Statements
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_isVectorBundle_structureModule_93a0cef3461d

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Model
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite
noncomputable section
open NumbersDVR ReciprocityTheory.ChartRestriction.G.Geo
namespace GroundTheory.Heights₂.Heights.Model
namespace GlueBundles
theorem _root_.solution :
    let S : Finset Nat.Primes := {⟨2, Nat.prime_two⟩}
    IsVectorBundle (structureModule (invOpen (𝟙 SpecZ) (primeProd S) : Scheme.{0})) ∧
      (∀ p : S, IsVectorBundle (structureModule (baseChange (𝟙 SpecZ) (ZLoc p)))) ∧
      ∀ p : S, Nonempty ((Scheme.Modules.pullback (ratToLoc (𝟙 SpecZ) p)).obj
        (structureModule (baseChange (𝟙 SpecZ) (ZLoc p))) ≅
        (Scheme.Modules.pullback (toInvOpen (𝟙 SpecZ) ℚ (primeProd S)
          (isUnit_intCast_rat _ (primeProd_ne_zero S)))).obj (structureModule _)) :=
  ⟨isVectorBundle_structureModule, fun _ => isVectorBundle_structureModule,
    fun _ => ⟨pullbackStructureIso _ ≪≫ (pullbackStructureIso _).symm⟩⟩
end GlueBundles
end GroundTheory.Heights₂.Heights.Model
