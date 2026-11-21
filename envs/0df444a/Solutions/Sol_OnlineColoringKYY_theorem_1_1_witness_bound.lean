-- Prove2me | solution 1 for OnlineColoringKYY.theorem_1_1_witness_bound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-20T11:07:46.22731+00:00
-- url     : https://prove2.me/submissions/4da49f30-c969-428f-8e51-a77518f80999

import Mathlib
import Definitions.Def_OnlineColoringKYY_OnlineColoringAlg
import Definitions.Def_OnlineColoringKYY_prefixGraph
import Definitions.Def_OnlineColoringKYY_run
import Definitions.Def_OnlineColoringKYY_IsProper
import Definitions.Def_OnlineColoringKYY_numColors
import Theorems.Thm_OnlineColoringKYY_adversary_no_third_vertex
import Theorems.Thm_OnlineColoringKYY_adversary_correctness

section
set_option autoImplicit false

namespace OnlineColoringKYY.Dev.Code

def bitCode (ℓ : ℕ) : ℕ → Fin ℓ → Bool := fun v s => v.testBit s.val

theorem bitCode_injOn (ℓ n : ℕ) (h : n ≤ 2 ^ ℓ) : Set.InjOn (bitCode ℓ) (Set.Iio n) := by
  intro a ha b hb hab
  have ha' : a < 2 ^ ℓ := lt_of_lt_of_le ha h
  have hb' : b < 2 ^ ℓ := lt_of_lt_of_le hb h
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < ℓ
  · exact congrFun hab ⟨i, hi⟩
  · have h1 : a < 2 ^ i := lt_of_lt_of_le ha' (Nat.pow_le_pow_right (by norm_num) (by omega))
    have h2 : b < 2 ^ i := lt_of_lt_of_le hb' (Nat.pow_le_pow_right (by norm_num) (by omega))
    rw [Nat.testBit_lt_two_pow h1, Nat.testBit_lt_two_pow h2]

end OnlineColoringKYY.Dev.Code
end

section
set_option autoImplicit false

namespace OnlineColoringKYY
open OnlineColoringKYY.Dev.Code

theorem chk_theorem_1_1_witness_bound (n : ℕ) (hn : 2 ≤ n) (A : OnlineColoringAlg) (hA : IsProper A) :
    ∃ G : SimpleGraph (Fin n), G.Colorable (2 * Nat.clog 2 n) ∧ n ≤ 2 * numColors A G := by
  have hℓ : 1 ≤ Nat.clog 2 n := Nat.clog_pos (by norm_num) hn
  have hinj := bitCode_injOn (Nat.clog 2 n) n (Nat.le_pow_clog (by norm_num) n)
  refine ⟨advGraph A (bitCode (Nat.clog 2 n)) n,
    (OnlineColoringKYY.adversary_correctness _ n hℓ _ hinj A hA).1, ?_⟩
  have h := Finset.card_le_mul_card_image (Finset.univ : Finset (Fin n)) 2
    (f := run A (advGraph A (bitCode (Nat.clog 2 n)) n)) (by
      intro c _
      exact OnlineColoringKYY.adversary_no_third_vertex _ n _ hinj A hA c)
  simpa [numColors] using h

end OnlineColoringKYY
end

theorem solution : type_of% @OnlineColoringKYY.chk_theorem_1_1_witness_bound := @OnlineColoringKYY.chk_theorem_1_1_witness_bound
