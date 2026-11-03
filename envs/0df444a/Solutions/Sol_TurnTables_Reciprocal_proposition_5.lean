-- Prove2me | solution 1 for TurnTables.Reciprocal.proposition_5
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-03T05:36:12.372771+00:00
-- url     : https://prove2.me/submissions/e4aec1e8-aa07-4c11-8211-6d0025cbda62

import Mathlib
import Definitions.Def_TurnTables_Reciprocal_Model
import Theorems.Thm_TurnTables_Reciprocal_optimal_strike
import Theorems.Thm_TurnTables_Reciprocal_proposition_5_part_1
import Theorems.Thm_TurnTables_Reciprocal_proposition_5_part_2

open TurnTables.Reciprocal in
theorem solution (P : Params) (hP : P.Standing) :
    (∀ R : Impl, ∀ B : ℝ, 0 ≤ B →
      offerorPriorPay P R B ≤ offerorPriorPay P R (strikeB P)) ∧
    (P.γ * P.V2 ≤ 2 * P.V1 →
      IsSymBNE P (strikeB P)
        (fun T => match T with | .part => 0 | .full => 1)) ∧
    (2 * P.V1 < P.γ * P.V2 →
      0 < offerProb P ∧ offerProb P < 1 ∧
        IsSymBNE P (strikeB P)
          (fun T => match T with | .part => 1 | .full => offerProb P)) :=
  ⟨optimal_strike P hP, proposition_5_part_1 P hP, proposition_5_part_2 P hP⟩
