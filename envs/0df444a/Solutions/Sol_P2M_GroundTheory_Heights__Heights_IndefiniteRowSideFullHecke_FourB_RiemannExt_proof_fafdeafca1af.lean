-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_FourB_RiemannExt_proof_fafdeafca1af
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T05:03:52.532047+00:00
-- url     : https://prove2.me/submissions/cf2c98e4-9428-497c-a0ae-e90c8f6f8cd0

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LocalDensities_LeviFormGbPotOne
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LocalDensities_StatementsKrullHeightOne
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LocalDensities_StatementsZariskiDense
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LocalDensities_PRiemannExtension
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_FourB_RiemannExt_exists_point_8a8753dbb0e0

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.FourB
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.FourB
namespace RiemannExt
theorem _root_.solution (hK : KrullHeightOne.Statement) (hZ : ZariskiDense.Statement) :
    RiemannExt.Statement := by
  classical
  intro A _ _ p q ⟨hft, hdom, hic, hq, hbdd⟩
  by_contra hne
  have hdvd : ¬ q ∣ p := fun ⟨r, hr⟩ => hne ⟨r, hr⟩
  have := hdom
  have := hft
  have : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing ℂ A
  have hp : p ≠ 0 := by rintro rfl; exact hdvd (dvd_zero q)
  obtain ⟨P, hP, -, c, hc, t, ht, hct⟩ := hK A p q ⟨hq, hdvd⟩
  obtain ⟨x, hxP, hxc⟩ := RiemannExt.exists_point P c hc
  obtain ⟨s, ε, hε, M, hM⟩ := hbdd x
  have hδ : 0 < ‖x c‖ := norm_pos_iff.2 hxc
  have hxt : x t = 0 := hxP t ht
  have hM1 : 0 < |M| + 1 := by positivity
  obtain ⟨y, hy, hyg⟩ := hZ A (p * q) ⟨hft, hdom, mul_ne_zero hp hq⟩ x (insert c (insert t s))
    (min ε (min (‖x c‖ / 2) (‖x c‖ / (2 * (|M| + 1))))) (by positivity)
  have hyp : y p ≠ 0 := fun h => hyg (by rw [map_mul, h, zero_mul])
  have hyq : y q ≠ 0 := fun h => hyg (by rw [map_mul, h, mul_zero])
  have h1 := hM y (fun a ha => (hy a (by simp [ha])).trans_le (min_le_left _ _)) hyq
  have hyc : ‖y c - x c‖ < ‖x c‖ / 2 :=
    (hy c (by simp)).trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hyt : ‖y t‖ < ‖x c‖ / (2 * (|M| + 1)) := by
    have := (hy t (by simp)).trans_le ((min_le_right _ _).trans (min_le_right _ _))
    rwa [hxt, sub_zero] at this
  have hrel : ‖y c‖ * ‖y q‖ = ‖y t‖ * ‖y p‖ := by
    rw [← norm_mul, ← norm_mul, ← map_mul, ← map_mul, hct]
  have hc' : ‖x c‖ / 2 < ‖y c‖ := by
    have := norm_sub_norm_le (x c) (y c)
    rw [norm_sub_rev] at this
    linarith
  have key : ‖y c‖ ≤ |M| * ‖y t‖ := by
    have hle : ‖y c‖ * ‖y q‖ ≤ (|M| * ‖y t‖) * ‖y q‖ := by
      rw [hrel]
      calc ‖y t‖ * ‖y p‖ ≤ ‖y t‖ * (M * ‖y q‖) := mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
        _ ≤ ‖y t‖ * (|M| * ‖y q‖) := mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right (le_abs_self M) (norm_nonneg _)) (norm_nonneg _)
        _ = (|M| * ‖y t‖) * ‖y q‖ := by ring
    exact le_of_mul_le_mul_right hle (norm_pos_iff.2 hyq)
  have hsmall : |M| * ‖y t‖ < ‖x c‖ / 2 := by
    calc |M| * ‖y t‖ ≤ (|M| + 1) * ‖y t‖ := by nlinarith [norm_nonneg (y t)]
      _ < (|M| + 1) * (‖x c‖ / (2 * (|M| + 1))) := mul_lt_mul_of_pos_left hyt hM1
      _ = ‖x c‖ / 2 := by field_simp
  linarith
end RiemannExt
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.FourB
