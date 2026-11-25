-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_regularityLocalFlat_holds_isUnit_coneVarMap_a467678d4c4b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T05:29:36.742882+00:00
-- url     : https://prove2.me/submissions/2fd19ebe-e0c0-488d-a3bb-2094ef35cfac

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_OneNotMemOfIsPrime
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_IsLocalizationConeVarMap
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_regularityLocalFlat_holds_exists_clear_677eeb8f0ddf
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_regularityLocalFlat_holds_coneVarMap_mul_clear_a178b33dfc06
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_regularityLocalFlat_holds_mem_of_clear_mem_f30bf8927550
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_regularityLocalFlat_holds_isUnit_algebraMap_cone_a38ac8eb988f

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
theorem _root_.solution (hPW : P ≤ W) (hWh : IsMultiHomogIdeal W) {v : ∀ k, ι k}
    (hv : ∀ k, (X ⟨k, v k⟩ : MRing ι) ∉ W) (G : MvPolynomial K (locRing P W)) {e : K →₀ ℕ}
    (he : IsUnit (coeff e G)) : IsUnit (coneVarMap P W hPW v G) := by
  obtain ⟨V, b, N, hV, hVW, hN⟩ := exists_clear hPW G
  have hNe : N e ∉ W := (isUnit_iff hPW (coeff e G) (hN e).1 hV hVW (hN e).2).mp he
  have hesupp : e ∈ G.support := mem_support_iff.mpr he.ne_zero
  have hNum : ∑ e ∈ G.support, N e * varMono v e ∉ W := fun h =>
    hNe (mem_of_clear_mem hWh hv G.support (fun e => (hN e).1) h e hesupp)
  have heq : coneVarMap P W hPW v G *
      algebraMap (MRing ι ⧸ P) (coneLocRing P W hPW) (Ideal.Quotient.mk P V) =
      algebraMap (MRing ι ⧸ P) (coneLocRing P W hPW)
        (Ideal.Quotient.mk P (∑ e ∈ G.support, N e * varMono v e)) :=
    Subtype.ext (coneVarMap_mul_clear hPW v G hN)
  exact isUnit_of_mul_isUnit_left (heq ▸ isUnit_algebraMap_cone hPW hNum)
end GroundTheory.Heights₂.Heights.Inter.regularityLocalFlat_holds
