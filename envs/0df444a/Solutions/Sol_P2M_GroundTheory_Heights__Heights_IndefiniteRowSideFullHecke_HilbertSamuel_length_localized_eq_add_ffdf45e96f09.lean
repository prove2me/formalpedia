-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_HilbertSamuel_length_localized_eq_add_ffdf45e96f09
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T04:33:32.04059+00:00
-- url     : https://prove2.me/submissions/3c447eae-17f3-4884-a461-c417d6c269f1

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsHilbert
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_ProjectiveSpaceIncrementHyp
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_WeightedHomogeneousSubmoduleBlockWeightIntEqRing
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_LengthLocalizedQuotientEqZero
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_HilbertSamuel_localizedModule_map_coe_667f891edde9

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
theorem _root_.solution (p : Ideal R) [p.IsPrime] {M₀ M₁ M₂ : Type*}
    [AddCommGroup M₀] [Module R M₀] [AddCommGroup M₁] [Module R M₁] [AddCommGroup M₂] [Module R M₂]
    (f : M₀ →ₗ[R] M₁) (g : M₁ →ₗ[R] M₂) (hf : Function.Injective f)
    (hg : Function.Surjective g) (h : Function.Exact f g) :
    Module.length (Localization.AtPrime p) (LocalizedModule p.primeCompl M₁) =
      Module.length (Localization.AtPrime p) (LocalizedModule p.primeCompl M₀) +
      Module.length (Localization.AtPrime p) (LocalizedModule p.primeCompl M₂) := by
  refine Module.length_eq_add_of_exact (LocalizedModule.map p.primeCompl f)
    (LocalizedModule.map p.primeCompl g) (LocalizedModule.map_injective _ f hf)
    (LocalizedModule.map_surjective _ g hg) ?_
  rw [localizedModule_map_coe, localizedModule_map_coe]
  exact LocalizedModule.map_exact p.primeCompl f g h
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HilbertSamuel
