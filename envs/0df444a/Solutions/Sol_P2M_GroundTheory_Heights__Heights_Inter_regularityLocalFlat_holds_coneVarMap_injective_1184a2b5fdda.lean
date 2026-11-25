-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_regularityLocalFlat_holds_coneVarMap_injective_1184a2b5fdda
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T05:29:35.935293+00:00
-- url     : https://prove2.me/submissions/6f3903be-deac-40de-bfaf-24fd4d304894

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_OneNotMemOfIsPrime
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_IsLocalizationConeVarMap
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_regularityLocalFlat_holds_exists_clear_677eeb8f0ddf
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_regularityLocalFlat_holds_coneVarMap_mul_clear_a178b33dfc06
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_regularityLocalFlat_holds_mem_of_clear_mem_f30bf8927550

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
theorem _root_.solution (hPW : P ≤ W) (hPh : IsMultiHomogIdeal P) {v : ∀ k, ι k}
    (hv : ∀ k, (X ⟨k, v k⟩ : MRing ι) ∉ W) : Function.Injective (coneVarMap P W hPW v) := by
  rw [injective_iff_map_eq_zero]
  intro G hG
  obtain ⟨V, b, N, -, hVW, hN⟩ := exists_clear hPW G
  have hV0 : fracHom P V ≠ 0 := by
    rw [Ne, fracHom_eq_zero_iff]
    exact fun h => hVW (hPW h)
  have hsum := coneVarMap_mul_clear hPW v G hN
  rw [hG] at hsum
  have hNum : ∑ e ∈ G.support, N e * varMono v e ∈ P := by
    rw [← fracHom_eq_zero_iff, ← hsum]
    simp
  have hvP : ∀ k, (X ⟨k, v k⟩ : MRing ι) ∉ P := fun k h => hv k (hPW h)
  have hNP : ∀ e ∈ G.support, N e ∈ P := mem_of_clear_mem hPh hvP G.support (fun e => (hN e).1) hNum
  refine MvPolynomial.ext _ _ fun e => ?_
  rw [coeff_zero]
  by_contra hne
  have he : e ∈ G.support := mem_support_iff.mpr hne
  have h1 := (hN e).2
  rw [fracHom_eq_zero_iff.mpr (hNP e he)] at h1
  have h2 : ((coeff e G : locRing P W) : FractionRing (MRing ι ⧸ P)) = 0 :=
    (mul_eq_zero.mp h1).resolve_right hV0
  exact hne (Subtype.ext h2)
end GroundTheory.Heights₂.Heights.Inter.regularityLocalFlat_holds
