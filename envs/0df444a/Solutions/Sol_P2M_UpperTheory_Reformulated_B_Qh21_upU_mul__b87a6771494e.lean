-- Prove2me | solution 1 for P2M_UpperTheory_Reformulated_B_Qh21_upU_mul__b87a6771494e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T09:00:09.170395+00:00
-- url     : https://prove2.me/submissions/98f10bb1-3736-4b12-86b3-6f57f7eceb88

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_UpUMul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

namespace UpperTheory.Reformulated.B.Qh21.upU_mul
theorem _root_.solution.{u_1} :
    ∀ {K : Type u_1} [inst : Field K] {N : ℕ} {A B : Matrix (Fin N) (Fin N) K},
      UpperTheory.Reformulated.B.Qh21.UpU A → UpperTheory.Reformulated.B.Qh21.UpU B → UpperTheory.Reformulated.B.Qh21.UpU (A * B) := by
  intro K _ N A B hA hB i j
  have hz : j ≤ i → ∀ k : Fin N, k ≠ i → A i k * B k j = 0 := by
    intro hji k hk
    rcases lt_or_gt_of_ne hk with h | h
    · rw [(hA i k).1 h, zero_mul]
    · rw [(hB k j).1 (lt_of_le_of_lt hji h), mul_zero]
  have hs : j ≤ i → (A * B) i j = B i j := by
    intro hji
    rw [Matrix.mul_apply, Finset.sum_eq_single i (fun k _ hk => hz hji k hk)
      (fun h => absurd (Finset.mem_univ i) h), (hA i i).2 rfl, one_mul]
  exact ⟨fun h => (hs h.le).trans ((hB i j).1 h), fun h => (hs h.ge).trans ((hB i j).2 h)⟩
end UpperTheory.Reformulated.B.Qh21.upU_mul
