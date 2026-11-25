-- Prove2me | solution 2 for PI.SqfRootsInj.W.sq_mul_pow_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:34:37.769747+00:00
-- url     : https://prove2.me/submissions/ece2a394-24ea-4173-9d5c-72f8eb4fafea

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarefreeRootsInjective_CardLeSumOfCover
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarefreeRootsInjective_SumSqPowLeTwo
import Theorems.Thm_PI_SqfRootsInj_W_sq_le_four_pow

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
noncomputable section
open Classical
open PI PI.SqfRootsInj PI.SqfRootsInj.W
open PI.SqfLab
namespace PI.SqfRootsInj.W
theorem _root_.solution (t : ℝ) (ht0 : 0 ≤ t) (e : ℕ) (he : 1 ≤ e) :
    (e : ℝ) ^ 2 * t ^ e ≤ t * (4 * t) ^ (e - 1) := by
  have h1 : (e : ℝ) ^ 2 ≤ 4 ^ (e - 1) := by exact_mod_cast sq_le_four_pow e he
  obtain ⟨k, rfl⟩ : ∃ k, e = k + 1 := ⟨e - 1, by omega⟩
  rw [Nat.add_sub_cancel] at h1 ⊢
  calc ((k + 1 : ℕ) : ℝ) ^ 2 * t ^ (k + 1) ≤ 4 ^ k * t ^ (k + 1) := by gcongr
    _ = t * (4 * t) ^ k := by ring
end PI.SqfRootsInj.W
