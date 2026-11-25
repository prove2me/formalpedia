-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Bridge_GeoNum_comap_sup_span_45ba483d0587
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T04:53:11.937484+00:00
-- url     : https://prove2.me/submissions/034a9a7a-dae1-413b-b1ac-33a37543c353

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_Assembly
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PIntNumPoint
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PSpecialMultAt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_IsMultiHomogIdealIff
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_GeoNum
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Bridge_GeoNum_ker_le_comap_33a2df692c1a
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Bridge_GeoNum_comap_map_eq_b61ea525f670

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
theorem _root_.solution (Q : Ideal (MRing ι (ZMod p))) (T : Set (MRing ι ℤ)) :
    Q.comap (red p) ⊔ Ideal.span T = (Q ⊔ Ideal.span (red p '' T)).comap (red p) := by
  have h : Q ⊔ Ideal.span (red p '' T) = (Q.comap (red p) ⊔ Ideal.span T).map (red p) := by
    rw [Ideal.map_sup, Ideal.map_comap_of_surjective _ (red_surjective p), Ideal.map_span]
  rw [h, comap_map_eq p ((ker_le_comap p Q).trans le_sup_left)]
end GroundTheory.Heights₂.Heights.Bridge.GeoNum
