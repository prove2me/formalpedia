-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_regularityLocalFlat_holds_coneVarMap_mul_clear_a178b33dfc06
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T04:35:38.327284+00:00
-- url     : https://prove2.me/submissions/b3270514-5398-49fb-ab3b-7cb2b8b6d180

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_OneNotMemOfIsPrime
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_IsLocalizationConeVarMap
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_regularityLocalFlat_holds_coneVarMap_coe_a97e5ef495ff

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
variable {P W}
namespace GroundTheory.Heights₂.Heights.Inter.regularityLocalFlat_holds
theorem _root_.solution (hPW : P ≤ W) (v : ∀ k, ι k) (G : MvPolynomial K (locRing P W))
    {V : MRing ι} {b : K → ℕ} {N : (K →₀ ℕ) → MRing ι}
    (hN : ∀ e, IsMultiHomog (N e) b ∧
        ((coeff e G : locRing P W) : FractionRing (MRing ι ⧸ P)) * fracHom P V = fracHom P (N e)) :
    ((coneVarMap P W hPW v G : coneLocRing P W hPW) : FractionRing (MRing ι ⧸ P)) * fracHom P V =
      fracHom P (∑ e ∈ G.support, N e * varMono v e) := by
  rw [coneVarMap_coe, Finset.sum_mul, map_sum]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [map_mul, ← (hN e).2]
  ring
end GroundTheory.Heights₂.Heights.Inter.regularityLocalFlat_holds
