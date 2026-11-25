-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_norm_lt_of_monic_root_small_coeffs_98580c9f2175
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T04:09:21.696348+00:00
-- url     : https://prove2.me/submissions/becfca84-b2ca-4ec8-a133-62a39ed4c943

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StGermWeierstrassPreparation
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_WeierstrassRemainderUnique

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
open Topology Filter Polynomial
noncomputable section
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
theorem _root_.solution {d : ℕ} (b : Fin d → ℂ) {r η : ℝ} (hr0 : 0 < r) (hr1 : r ≤ 1)
    (hη : (d : ℝ) * η < r ^ d) (hb : ∀ j, ‖b j‖ ≤ η) (t : ℂ)
    (ht : t ^ d + ∑ j : Fin d, b j * t ^ (j : ℕ) = 0) : ‖t‖ < r := by
  by_contra h
  push Not at h
  have hT : 0 < ‖t‖ ^ d := pow_pos (lt_of_lt_of_le hr0 h) d
  have hR : 0 < r ^ d := pow_pos hr0 d
  have htd : t ^ d = -∑ j : Fin d, b j * t ^ (j : ℕ) := eq_neg_of_add_eq_zero_left ht
  have hsum : ‖t‖ ^ d ≤ ∑ _j : Fin d, η * (‖t‖ ^ d / r ^ d) := by
    calc ‖t‖ ^ d = ‖t ^ d‖ := (norm_pow _ _).symm
      _ = ‖∑ j : Fin d, b j * t ^ (j : ℕ)‖ := by rw [htd, norm_neg]
      _ ≤ ∑ j : Fin d, ‖b j * t ^ (j : ℕ)‖ := norm_sum_le _ _
      _ ≤ _ := Finset.sum_le_sum fun j _ => by
          rw [norm_mul, norm_pow]
          refine mul_le_mul (hb j) ?_ (by positivity) (le_trans (norm_nonneg _) (hb j))
          rw [le_div_iff₀ hR]
          calc ‖t‖ ^ (j : ℕ) * r ^ d ≤ ‖t‖ ^ (j : ℕ) * r ^ (d - j) :=
                mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hr0.le hr1 (Nat.sub_le d j)) (by positivity)
            _ ≤ ‖t‖ ^ (j : ℕ) * ‖t‖ ^ (d - j) := by gcongr
            _ = ‖t‖ ^ d := by rw [← pow_add, Nat.add_sub_cancel' j.2.le]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
  have hlt : (d : ℝ) * (η * (‖t‖ ^ d / r ^ d)) < ‖t‖ ^ d := by
    rw [show (d : ℝ) * (η * (‖t‖ ^ d / r ^ d)) = ((d : ℝ) * η / r ^ d) * ‖t‖ ^ d by ring]
    exact mul_lt_of_lt_one_left hT ((div_lt_one hR).2 hη)
  linarith
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
