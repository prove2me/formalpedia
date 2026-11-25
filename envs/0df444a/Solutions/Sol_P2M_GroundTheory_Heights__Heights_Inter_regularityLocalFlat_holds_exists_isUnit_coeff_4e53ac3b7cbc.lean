-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_regularityLocalFlat_holds_exists_isUnit_coeff_4e53ac3b7cbc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T05:20:46.032354+00:00
-- url     : https://prove2.me/submissions/b649dfbc-6200-4ba0-bf84-900216df21c5

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_OneNotMemOfIsPrime
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_IsLocalizationConeVarMap
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_regularityLocalFlat_holds_exists_clear_677eeb8f0ddf
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_regularityLocalFlat_holds_coneVarMap_mul_clear_a178b33dfc06

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
theorem _root_.solution (hPW : P ≤ W) {v : ∀ k, ι k} (G : MvPolynomial K (locRing P W))
    {g : MRing ι} (hg : g ∉ W)
    (hG : coneVarMap P W hPW v G =
      algebraMap (MRing ι ⧸ P) (coneLocRing P W hPW) (Ideal.Quotient.mk P g)) :
    ∃ e, IsUnit (coeff e G) := by
  by_contra hcon
  push Not at hcon
  obtain ⟨V, b, N, hV, hVW, hN⟩ := exists_clear hPW G
  have hNW : ∀ e, N e ∈ W := fun e => by
    by_contra h
    exact hcon e ((isUnit_iff hPW _ (hN e).1 hV hVW (hN e).2).mpr h)
  have hsum := coneVarMap_mul_clear hPW v G hN
  rw [hG] at hsum
  have h1 : fracHom P (∑ e ∈ G.support, N e * varMono v e - g * V) = 0 := by
    rw [map_sub, ← hsum, map_mul]
    exact sub_self _
  rw [fracHom_eq_zero_iff] at h1
  have h2 : g * V ∈ W := by
    have := W.sub_mem (W.sum_mem (t := G.support) fun e _ => W.mul_mem_right (varMono v e) (hNW e)) (hPW h1)
    simpa using this
  exact (Ideal.IsPrime.mem_or_mem ‹_› h2).elim hg hVW
end GroundTheory.Heights₂.Heights.Inter.regularityLocalFlat_holds
