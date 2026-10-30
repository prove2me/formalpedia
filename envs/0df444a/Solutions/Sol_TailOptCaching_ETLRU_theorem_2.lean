-- Prove2me | solution 1 for TailOptCaching.ETLRU.theorem_2
-- status  : ACCEPTED   (prove)
-- author  : @rgmohan
-- created : 2026-10-29T06:00:23.071991+00:00
-- url     : https://prove2.me/submissions/ae7f2ac4-a148-4a61-8ec0-215841b11428

import Mathlib
import Definitions.Def_TailOptCaching_ETLRU_Model
import Theorems.Thm_TailOptCaching_ETLRU_value_etlru_eq_optValue
import Theorems.Thm_TailOptCaching_ETLRU_optValue_le_value

/-!
# Theorem 2: ET-LRU is an optimal online caching policy

ET-LRU attains the Bellman optimum (`value_etlru_eq_optValue`), and the Bellman optimum
lower-bounds every admissible policy (`optValue_le_value`).
-/

open scoped ENNReal

open TailOptCaching.ETLRU in
theorem solution (P : Params) (σ : Policy) (hσ : IsETLRU P σ)
    (π : Policy) (hπ : Admissible P π) (M : ℕ) (z : State) (hz : WellFormed P z) :
    value P σ M 0 z ≤ value P π M 0 z := by
  rw [value_etlru_eq_optValue P σ hσ M 0 z hz]
  exact optValue_le_value P π hπ M 0 z
