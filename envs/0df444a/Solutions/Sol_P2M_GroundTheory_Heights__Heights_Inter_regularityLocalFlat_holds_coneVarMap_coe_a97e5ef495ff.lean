-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_regularityLocalFlat_holds_coneVarMap_coe_a97e5ef495ff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T03:59:26.840269+00:00
-- url     : https://prove2.me/submissions/d99bcd4b-2243-41da-b140-a6a26add1027

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_OneNotMemOfIsPrime
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_IsLocalizationConeVarMap

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo IsLocalRing
noncomputable section
open GroundTheory.Heights₂.Heights.Inter.regularityLocalFlat_holds
variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]
variable (P W : Ideal (MRing ι)) [P.IsPrime] [W.IsPrime]
namespace GroundTheory.Heights₂.Heights.Inter.regularityLocalFlat_holds
theorem _root_.solution (hPW : P ≤ W) (v : ∀ k, ι k) (G : MvPolynomial K (locRing P W)) :
    ((coneVarMap P W hPW v G : coneLocRing P W hPW) : FractionRing (MRing ι ⧸ P)) =
      ∑ e ∈ G.support, ((coeff e G : locRing P W) : FractionRing (MRing ι ⧸ P)) * fracHom P (varMono v e) := by
  rw [coneVarMap, aeval_def, eval₂_eq']
  change (coneLocRing P W hPW).val _ = _
  rw [map_sum]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [map_mul, map_prod, varMono, map_prod]
  simp only [map_pow]
  rfl
end GroundTheory.Heights₂.Heights.Inter.regularityLocalFlat_holds
