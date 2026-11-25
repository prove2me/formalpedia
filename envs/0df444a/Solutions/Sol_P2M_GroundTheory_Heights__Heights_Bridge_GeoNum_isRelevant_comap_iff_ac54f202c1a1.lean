-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Bridge_GeoNum_isRelevant_comap_iff_ac54f202c1a1
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T03:39:30.733724+00:00
-- url     : https://prove2.me/submissions/1bf0e6c1-2b6f-4a7a-a5e1-eb3f0d28af86

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_Assembly
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PIntNumPoint
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PSpecialMultAt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_IsMultiHomogIdealIff
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_GeoNum
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_coeff_coeffForm_479fc53ecb0b
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] P2M_GroundTheory_Heights__Heights_FieldNumbers_coeff_coeffForm_479fc53ecb0b



set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Bridge
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GroundTheory.Heights₂.Heights.FieldNumbers ReciprocityTheory.ChartRestriction.G
noncomputable section
open GroundTheory.Heights₂.Heights.Bridge.GeoNum
variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]
variable (p : ℕ) [Fact p.Prime]
namespace GroundTheory.Heights₂.Heights.Bridge.GeoNum
theorem _root_.solution (Q : Ideal (MRing ι (ZMod p))) :
    Geo.IsRelevant (R := ℤ) (Q.comap (red p)) ↔ IsRelevant Q := by
  simp only [Geo.IsRelevant, IsRelevant, Ideal.mem_comap, red, map_X]
end GroundTheory.Heights₂.Heights.Bridge.GeoNum
