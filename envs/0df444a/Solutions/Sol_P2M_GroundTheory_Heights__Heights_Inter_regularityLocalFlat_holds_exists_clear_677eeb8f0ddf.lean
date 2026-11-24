-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_regularityLocalFlat_holds_exists_clear_677eeb8f0ddf
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T01:00:46.412436+00:00
-- url     : https://prove2.me/submissions/d99bdc4d-87a7-4bd7-9855-1323cc98a7d5

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
variable {P W}
namespace GroundTheory.Heights₂.Heights.Inter.regularityLocalFlat_holds
theorem _root_.solution (hPW : P ≤ W) (G : MvPolynomial K (locRing P W)) :
    ∃ (V : MRing ι) (b : K → ℕ) (N : (K →₀ ℕ) → MRing ι), IsMultiHomog V b ∧ V ∉ W ∧
      ∀ e, IsMultiHomog (N e) b ∧
        ((coeff e G : locRing P W) : FractionRing (MRing ι ⧸ P)) * fracHom P V = fracHom P (N e) := by
  classical
  induction G using MvPolynomial.induction_on' with
  | monomial e c =>
    obtain ⟨u, w, a, hu, hw, hwW, hc⟩ := (mem_locRing_iff hPW).mp c.2
    refine ⟨w, a, fun e' => if e = e' then u else 0, hw, hwW, fun e' => ⟨?_, ?_⟩⟩
    · dsimp only
      split_ifs
      · exact hu
      · exact homog_zero a
    · rw [coeff_monomial]
      dsimp only
      split_ifs
      · exact hc
      · simp
  | add G1 G2 h1 h2 =>
    obtain ⟨V1, b1, N1, hV1, hV1W, hN1⟩ := h1
    obtain ⟨V2, b2, N2, hV2, hV2W, hN2⟩ := h2
    refine ⟨V1 * V2, b1 + b2, fun e => N1 e * V2 + N2 e * V1, homog_mul hV1 hV2,
      fun h => (Ideal.IsPrime.mem_or_mem ‹_› h).elim hV1W hV2W, fun e => ⟨?_, ?_⟩⟩
    · refine homog_add (homog_mul (hN1 e).1 hV2) ?_
      rw [add_comm b1 b2]
      exact homog_mul (hN2 e).1 hV1
    · rw [coeff_add]
      change (((coeff e G1 : locRing P W) : FractionRing (MRing ι ⧸ P)) + (coeff e G2 : locRing P W)) * _ = _
      simp only [map_add, map_mul]
      rw [← (hN1 e).2, ← (hN2 e).2]
      ring
end GroundTheory.Heights₂.Heights.Inter.regularityLocalFlat_holds
