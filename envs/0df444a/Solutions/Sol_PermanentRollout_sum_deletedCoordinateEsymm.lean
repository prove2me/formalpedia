-- Prove2me | solution 1 for PermanentRollout.sum_deletedCoordinateEsymm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:03.257302+00:00
-- url     : https://prove2.me/submissions/898a9a0f-e5f1-429d-847e-39f982d2b08e

import Mathlib
import Definitions.Def_Permanent
import Theorems.Thm_PermanentRollout_powersetCard_erase_eq_filter_not_mem

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
open scoped BigOperators
namespace PermanentRollout
theorem _root_.solution {t : ℕ}
    (u : Fin t → ℂ) (q : ℕ) :
    (∑ i : Fin t, deletedCoordinateEsymm u i q) =
      ((t - q : ℕ) : ℂ) * coordinateEsymm u q := by
  classical
  calc
    (∑ i : Fin t, deletedCoordinateEsymm u i q) =
        ∑ i : Fin t,
          ∑ rows ∈ ((Finset.univ : Finset (Fin t)).powersetCard q).filter
            (fun rows => i ∉ rows), ∏ j ∈ rows, u j := by
      simp_rw [deletedCoordinateEsymm, Finset.esymm_map_val,
        powersetCard_erase_eq_filter_not_mem]
    _ = ∑ i : Fin t, ∑ rows ∈
          (Finset.univ : Finset (Fin t)).powersetCard q,
            if i ∉ rows then ∏ j ∈ rows, u j else 0 := by
      simp_rw [Finset.sum_filter]
    _ = ∑ rows ∈ (Finset.univ : Finset (Fin t)).powersetCard q,
          ∑ i : Fin t, if i ∉ rows then ∏ j ∈ rows, u j else 0 := by
      rw [Finset.sum_comm]
    _ = ((t - q : ℕ) : ℂ) * coordinateEsymm u q := by
      rw [coordinateEsymm, Finset.esymm_map_val, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro rows hrows
      have hcard : rows.card = q := (Finset.mem_powersetCard.mp hrows).2
      calc
        (∑ i : Fin t, if i ∉ rows then ∏ j ∈ rows, u j else 0) =
            (∑ i : Fin t, if i ∉ rows then (1 : ℂ) else 0) *
              ∏ j ∈ rows, u j := by
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro i _
          split_ifs <;> simp
        _ = ((t - q : ℕ) : ℂ) * ∏ j ∈ rows, u j := by
          rw [Finset.sum_boole]
          congr 1
          simp [Finset.filter_notMem_eq_sdiff,
            Finset.card_sdiff_of_subset (Finset.subset_univ rows), hcard]
end PermanentRollout
