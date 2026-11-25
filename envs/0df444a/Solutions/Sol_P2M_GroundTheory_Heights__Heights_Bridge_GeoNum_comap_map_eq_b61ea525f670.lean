-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Bridge_GeoNum_comap_map_eq_b61ea525f670
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T04:14:36.804796+00:00
-- url     : https://prove2.me/submissions/9f036f2e-b3c4-4e00-8d5e-f41d6b09845a

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
theorem _root_.solution {J : Ideal (MRing ι ℤ)} (hJ : RingHom.ker (red (ι := ι) p) ≤ J) :
    (J.map (red p)).comap (red p) = J := by
  rw [Ideal.comap_map_of_surjective _ (red_surjective p), ← RingHom.ker_eq_comap_bot,
    sup_eq_left.mpr hJ]
end GroundTheory.Heights₂.Heights.Bridge.GeoNum
