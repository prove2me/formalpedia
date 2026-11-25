-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_monic_sub_eq_mul_sum_0b542fb0941c
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T04:46:25.597565+00:00
-- url     : https://prove2.me/submissions/553f931a-b6c1-43e9-99e9-c6c18da57798

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_MonicDifferenceQuotient
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_sub_pow_eq_mul_sum_fin_48c4d365a9ba

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
open Finset
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
theorem _root_.solution {d : ℕ} (C : Fin d → ℂ) (s t : ℂ) :
    (s ^ d + ∑ k : Fin d, C k * s ^ (k : ℕ)) - (t ^ d + ∑ k : Fin d, C k * t ^ (k : ℕ)) =
      (s - t) * ∑ j : Fin d, monicDifferenceCoeff C s j * t ^ (j : ℕ) := by
  have expand : ∑ j : Fin d, monicDifferenceCoeff C s j * t ^ (j : ℕ) =
      ∑ j : Fin d, (if (j : ℕ) < d then s ^ (d - 1 - (j : ℕ)) * t ^ (j : ℕ) else 0) +
        ∑ k : Fin d, C k * ∑ j : Fin d,
          (if (j : ℕ) < k then s ^ ((k : ℕ) - 1 - (j : ℕ)) * t ^ (j : ℕ) else 0) := by
    simp only [monicDifferenceCoeff, add_mul, Finset.sum_add_distrib, Finset.sum_filter, Finset.sum_mul]
    congr 1
    · exact Finset.sum_congr rfl fun j _ => by simp [j.isLt]
    · rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      split_ifs <;> ring
  have h2 : ∑ k : Fin d, (s - t) * (C k * ∑ j : Fin d,
      (if (j : ℕ) < k then s ^ ((k : ℕ) - 1 - (j : ℕ)) * t ^ (j : ℕ) else 0)) =
      ∑ k : Fin d, (C k * s ^ (k : ℕ) - C k * t ^ (k : ℕ)) :=
    Finset.sum_congr rfl fun k _ => by rw [mul_left_comm, sub_pow_eq_mul_sum_fin k.isLt.le, mul_sub]
  rw [expand, mul_add, sub_pow_eq_mul_sum_fin le_rfl, Finset.mul_sum, h2, Finset.sum_sub_distrib]
  ring
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
