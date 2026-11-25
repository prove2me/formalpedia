-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_HilbertSamuel_localizedModule_map_coe_667f891edde9
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T03:57:35.494804+00:00
-- url     : https://prove2.me/submissions/49c22112-1ba6-453c-8794-47e98c9c6d5c

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsHilbert
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_ProjectiveSpaceIncrementHyp
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_WeightedHomogeneousSubmoduleBlockWeightIntEqRing
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_LengthLocalizedQuotientEqZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HilbertSamuel
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR
noncomputable section
universe u
variable {R : Type*} [CommRing R]
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HilbertSamuel
theorem _root_.solution (P : Submonoid R) {M₀ M₁ : Type*} [AddCommGroup M₀] [Module R M₀]
    [AddCommGroup M₁] [Module R M₁] (f : M₀ →ₗ[R] M₁) :
    ⇑(LocalizedModule.map P f) = ⇑(IsLocalizedModule.map P (LocalizedModule.mkLinearMap P M₀)
      (LocalizedModule.mkLinearMap P M₁) f) := by
  funext y
  induction y using LocalizedModule.induction_on with
  | h m s => rw [LocalizedModule.map_mk, IsLocalizedModule.map_LocalizedModules]
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HilbertSamuel
