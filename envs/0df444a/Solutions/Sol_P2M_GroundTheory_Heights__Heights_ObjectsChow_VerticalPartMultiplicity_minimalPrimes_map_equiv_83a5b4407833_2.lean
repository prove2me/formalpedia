-- Prove2me | solution 2 for P2M_GroundTheory_Heights__Heights_ObjectsChow_VerticalPartMultiplicity_minimalPrimes_map_equiv_83a5b4407833
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T05:07:26.773804+00:00
-- url     : https://prove2.me/submissions/631284bf-3d78-4d2b-ac8f-52630e168db8

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_ImportsAlt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LengthLocalizedModuleQuotient

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open GroundTheory.Heights₂.Heights.ObjectsChow
open GroundTheory.Heights₂.Heights.ObjectsChow.VerticalPartMultiplicity
open MvPolynomial NumberField
open ReciprocityTheory.ChartRestriction.G.Geo (MRing PBlk Xc)
variable {n : ℕ}
namespace GroundTheory.Heights₂.Heights.ObjectsChow.VerticalPartMultiplicity
theorem _root_.solution {A B : Type*} [CommRing A] [CommRing B] (Φ : A ≃+* B) (K : Ideal A) :
    (K.map (Φ : A →+* B)).minimalPrimes = Ideal.map (Φ : A →+* B) '' K.minimalPrimes := by
  have hk : RingHom.ker (Φ : A →+* B) = ⊥ := (RingHom.injective_iff_ker_eq_bot _).mp Φ.injective
  rw [Ideal.minimalPrimes_map_of_surjective Φ.surjective, hk, sup_bot_eq]
end GroundTheory.Heights₂.Heights.ObjectsChow.VerticalPartMultiplicity
