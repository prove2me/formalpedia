-- Prove2me | solution 1 for PI.SwBig.BigCellGProof.bigCell_one_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:28:00.188695+00:00
-- url     : https://prove2.me/submissions/c3274a8a-8d53-41a0-8fdb-613806553f9d

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_LongWeylElementSquare
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_BigCellConjugation_Monomial

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open PI PI.SwBig PI.SwBig.BigCellGProof
open PI.SwBig
namespace PI.SwBig.BigCellGProof
theorem _root_.solution (k r : ℕ) (c : Fin r → ℂ) (i j : Fin (2 * r + k + 1)) :
    bigCell k r c 1 i j = if i = rhoB k r j then tv k r c j else 0 := by
  unfold bigCell rhoB tv esI
  rcases lt_or_ge j.val r with h1 | h1
  · have ho : j.val < r ∨ r + k < j.val := Or.inl h1
    rw [dif_pos h1, if_pos ho, dif_pos h1]
  · rcases le_or_gt j.val (r + k) with h2 | h2
    · have ho : ¬ (j.val < r ∨ r + k < j.val) := by omega
      rw [dif_neg (show ¬ (j.val < r) by omega), dif_pos h2, if_neg ho, dif_neg (show ¬ (j.val < r) by omega), dif_pos h2]
      by_cases hij : i = j
      · subst hij
        rw [dif_pos ⟨h1, h2⟩, if_pos rfl, Matrix.one_apply, if_pos rfl]
      · rw [if_neg hij]
        split_ifs with hi
        · rw [Matrix.one_apply, if_neg]
          intro h
          apply hij
          apply Fin.ext
          have := congrArg Fin.val h
          simp only at this
          omega
        · rfl
    · have ho : j.val < r ∨ r + k < j.val := Or.inr h2
      rw [dif_neg (show ¬ (j.val < r) by omega), dif_neg (show ¬ (j.val ≤ r + k) by omega), if_pos ho,
        dif_neg (show ¬ (j.val < r) by omega), dif_neg (show ¬ (j.val ≤ r + k) by omega)]
      by_cases hi : i.val = 2 * r + k - j.val
      · rw [if_pos hi, if_pos (Fin.ext hi)]
      · rw [if_neg hi, if_neg (fun h => hi (congrArg Fin.val h))]
end PI.SwBig.BigCellGProof
