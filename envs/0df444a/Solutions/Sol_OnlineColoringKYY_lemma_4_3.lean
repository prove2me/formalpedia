-- Prove2me | solution 1 for OnlineColoringKYY.lemma_4_3
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-20T11:07:46.161647+00:00
-- url     : https://prove2.me/submissions/06f03831-e363-4ab7-a57f-61f4b9e12be7

import Mathlib
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

theorem chk_lemma_4_3 (ℓ : ℕ) (hℓ : 1 ≤ ℓ) (A : OnlineColoringAlg) (hA : IsProper A) :
    ∃ G : SimpleGraph (Fin (2 ^ ℓ)), G.Colorable (2 * ℓ) ∧
      ∀ c : ℕ, (Finset.univ.filter (fun v => run A G v = c)).card ≤ 2 := by
  have hinj := bitCode_injOn ℓ (2 ^ ℓ) le_rfl
  exact ⟨advGraph A (bitCode ℓ) (2 ^ ℓ),
    (OnlineColoringKYY.adversary_correctness ℓ (2 ^ ℓ) hℓ (bitCode ℓ) hinj A hA).1,
    fun c => OnlineColoringKYY.adversary_no_third_vertex ℓ (2 ^ ℓ) (bitCode ℓ) hinj A hA c⟩

end OnlineColoringKYY
end

theorem solution : type_of% @OnlineColoringKYY.chk_lemma_4_3 := @OnlineColoringKYY.chk_lemma_4_3
