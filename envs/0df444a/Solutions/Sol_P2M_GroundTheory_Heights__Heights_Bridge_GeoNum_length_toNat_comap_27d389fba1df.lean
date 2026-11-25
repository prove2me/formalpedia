-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Bridge_GeoNum_length_toNat_comap_27d389fba1df
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T04:09:53.962094+00:00
-- url     : https://prove2.me/submissions/c9ad47e6-0804-41cd-a181-8a8ec273100a

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_Assembly
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PIntNumPoint
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PSpecialMultAt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_IsMultiHomogIdealIff
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_GeoNum

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Bridge
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GroundTheory.Heights₂.Heights.FieldNumbers ReciprocityTheory.ChartRestriction.G
noncomputable section
open GroundTheory.Heights₂.Heights.Bridge.GeoNum
variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]
variable (p : ℕ) [Fact p.Prime]
namespace GroundTheory.Heights₂.Heights.Bridge.GeoNum
theorem _root_.solution (J' : Ideal (MRing ι (ZMod p))) :
    (Module.length ℤ (MRing ι ℤ ⧸ J'.comap (red p))).toNat =
      Module.finrank (ZMod p) (MRing ι (ZMod p) ⧸ J') := by
  have e1 : Module.length ℤ (MRing ι ℤ ⧸ J'.comap (red p)) =
      Module.length ℤ (MRing ι (ZMod p) ⧸ J') := by
    convert ((quotEquiv p J').toAddEquiv.toIntLinearEquiv).length_eq
  have e2 : Module.length ℤ (MRing ι (ZMod p) ⧸ J') =
      Module.length (ZMod p) (MRing ι (ZMod p) ⧸ J') := by
    convert Module.length_eq_of_surjective (R := ZMod p) (S := ℤ)
      (M := MRing ι (ZMod p) ⧸ J') ZMod.intCast_surjective
  rw [e1, e2, Module.length_eq_rank]
  rfl
end GroundTheory.Heights₂.Heights.Bridge.GeoNum
