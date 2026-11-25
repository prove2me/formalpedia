-- Prove2me | solution 1 for PI.SwBig.BigCellGProof.tv_Hpk_tv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:28:11.900509+00:00
-- url     : https://prove2.me/submissions/1087dc22-876f-4cbb-914b-d7dbe03e880a

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
theorem _root_.solution (k r : ℕ) (c : Fin r → ℂ) (hc : ∀ a, c a ≠ 0) (i j : Fin (2 * r + k + 1)) :
    star (tv k r c i) * Hpk k r i j * tv k r c j = Hpk k r i j := by
  by_cases hz : Hpk k r i j = 0
  · simp [hz]
  have key : (i.val < r ∧ i.val + j.val = 2 * r + k) ∨ (j.val < r ∧ i.val + j.val = 2 * r + k) ∨
      (r ≤ i.val ∧ i.val ≤ r + k ∧ i = j) := by
    unfold Hpk at hz
    split_ifs at hz <;> first | tauto | simp at hz
  rcases key with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2, rfl⟩
  · have hH : Hpk k r i j = 1 := by unfold Hpk; rw [if_pos ⟨h1, h2⟩]
    have hti : tv k r c i = c ⟨i.val, h1⟩ := by unfold tv; rw [dif_pos h1]
    have htj : tv k r c j = (star (c ⟨i.val, h1⟩))⁻¹ := by
      have e : (⟨2 * r + k - j.val, by omega⟩ : Fin r) = ⟨i.val, h1⟩ :=
        Fin.ext (show 2 * r + k - j.val = i.val by omega)
      unfold tv
      rw [dif_neg (show ¬ (j.val < r) by omega), dif_neg (show ¬ (j.val ≤ r + k) by omega), e]
    rw [hti, htj, hH, mul_one, mul_inv_cancel₀ (star_ne_zero.mpr (hc _))]
  · have hH : Hpk k r i j = 1 := by unfold Hpk; rw [if_neg (by omega), if_pos ⟨h1, h2⟩]
    have htj : tv k r c j = c ⟨j.val, h1⟩ := by unfold tv; rw [dif_pos h1]
    have hti : tv k r c i = (star (c ⟨j.val, h1⟩))⁻¹ := by
      have e : (⟨2 * r + k - i.val, by omega⟩ : Fin r) = ⟨j.val, h1⟩ :=
        Fin.ext (show 2 * r + k - i.val = j.val by omega)
      unfold tv
      rw [dif_neg (show ¬ (i.val < r) by omega), dif_neg (show ¬ (i.val ≤ r + k) by omega), e]
    rw [hti, htj, hH]
    simp [hc]
  · have hti : tv k r c i = 1 := by unfold tv; rw [dif_neg (by omega), dif_pos h2]
    rw [hti]
    simp
end PI.SwBig.BigCellGProof
