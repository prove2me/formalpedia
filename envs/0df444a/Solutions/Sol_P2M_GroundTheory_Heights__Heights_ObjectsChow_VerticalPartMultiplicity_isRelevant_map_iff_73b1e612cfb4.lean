-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ObjectsChow_VerticalPartMultiplicity_isRelevant_map_iff_73b1e612cfb4
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T05:07:21.338164+00:00
-- url     : https://prove2.me/submissions/118c304f-cb74-4ff2-a03e-338f34bb5a10

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_ImportsAlt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LengthLocalizedModuleQuotient
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ObjectsChow_VerticalPartMultiplicity___symm_X_7aa01944f7d0

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
theorem _root_.solution (W : Ideal (MRing (PBlk n))) :
    IsRelevant (W.map (Ψ n : MRing (PBlk n) →+* MvPolynomial (Fin n) (𝓞 ℚ))) ↔
      ReciprocityTheory.ChartRestriction.G.Geo.IsRelevant W := by
  simp only [IsRelevant, ReciprocityTheory.ChartRestriction.G.Geo.IsRelevant, Ideal.map_comap_of_equiv, Ideal.mem_comap,
    RingEquiv.coe_toRingHom, Ψ_symm_X]
  exact ⟨fun ⟨j, hj⟩ k => ⟨j, by cases k; exact hj⟩, fun h => h ()⟩
end GroundTheory.Heights₂.Heights.ObjectsChow.VerticalPartMultiplicity
