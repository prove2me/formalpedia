-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Bridge_GeoNum_multAt_comap_fc3e2b0146c7
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T04:48:07.113201+00:00
-- url     : https://prove2.me/submissions/bd43759e-6923-4755-8abd-9ae1a8df3792

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_Assembly
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PIntNumPoint
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PSpecialMultAt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_IsMultiHomogIdealIff
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_GeoNum
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Bridge_GeoNum_quotEquiv_mk_72962265258b
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_length_localizedModule_eq_of_surjective_2c49ffad9549


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
theorem _root_.solution (J' W' : Ideal (MRing ι (ZMod p))) [W'.IsPrime] :
    NumbersDVR.multAt (J'.comap (red p)) (W'.comap (red p)) = NumbersDVR.multAt J' W' := by
  unfold NumbersDVR.multAt
  refine length_localizedModule_eq_of_surjective (red p) (red_surjective p) W' _ rfl _ _
    (quotEquiv p J').toAddEquiv fun s x => ?_
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
  change quotEquiv p J' (Ideal.Quotient.mk _ (s * y)) =
    Ideal.Quotient.mk J' (red p s) * quotEquiv p J' (Ideal.Quotient.mk _ y)
  rw [quotEquiv_mk, quotEquiv_mk, map_mul, map_mul]
end GroundTheory.Heights₂.Heights.Bridge.GeoNum
