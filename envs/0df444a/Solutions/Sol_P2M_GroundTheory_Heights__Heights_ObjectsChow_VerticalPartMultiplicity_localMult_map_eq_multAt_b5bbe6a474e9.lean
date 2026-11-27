-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ObjectsChow_VerticalPartMultiplicity_localMult_map_eq_multAt_b5bbe6a474e9
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T05:07:24.828928+00:00
-- url     : https://prove2.me/submissions/972dfa97-d285-42d6-9c7e-d72d90d3981c

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_ImportsAlt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LengthLocalizedModuleQuotient
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ObjectsChow_VerticalPartMultiplicity_length_localizedModule_quotient_981ab8107018
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ObjectsChow_VerticalPartMultiplicity_localMult_map_equiv_39fad21a977d

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
theorem _root_.solution (K W : Ideal (MRing (PBlk n))) :
    localMult (K.map (Ψ n : MRing (PBlk n) →+* MvPolynomial (Fin n) (𝓞 ℚ)))
        (W.map (Ψ n : MRing (PBlk n) →+* MvPolynomial (Fin n) (𝓞 ℚ))) =
      ReciprocityTheory.ChartRestriction.G.Geo.multAt K W := by
  rw [localMult_map_equiv]
  unfold localMult ReciprocityTheory.ChartRestriction.G.Geo.multAt
  by_cases hW : W.IsPrime
  · rw [dif_pos hW, dif_pos hW]
    haveI := hW
    rw [length_localizedModule_quotient]
  · rw [dif_neg hW, dif_neg hW]
end GroundTheory.Heights₂.Heights.ObjectsChow.VerticalPartMultiplicity
