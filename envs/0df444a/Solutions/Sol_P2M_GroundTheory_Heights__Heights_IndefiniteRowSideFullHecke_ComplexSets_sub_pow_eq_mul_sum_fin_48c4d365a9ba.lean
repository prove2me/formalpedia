-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_sub_pow_eq_mul_sum_fin_48c4d365a9ba
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T04:08:20.583212+00:00
-- url     : https://prove2.me/submissions/e6e5db91-74c5-4578-92e4-7c882de1c950

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_MonicDifferenceQuotient
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_sum_fin_ite_lt_6a0fe4d5d9a1

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
theorem _root_.solution {n m : ℕ} (hm : m ≤ n) (s t : ℂ) :
    (s - t) * ∑ j : Fin n, (if (j : ℕ) < m then s ^ (m - 1 - (j : ℕ)) * t ^ (j : ℕ) else 0) = s ^ m - t ^ m := by
  rw [sum_fin_ite_lt hm (fun j => s ^ (m - 1 - j) * t ^ j), mul_comm]
  have h := geom_sum₂_mul s t m
  rw [geom_sum₂_comm] at h
  rw [← h]
  congr 1
  exact Finset.sum_congr rfl fun j _ => mul_comm _ _
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
