-- Prove2me | solution 1 for TernarySync.Alphabet.theorem_4_1
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T07:34:00.165911+00:00
-- url     : https://prove2.me/submissions/272cef81-b9d6-4c90-81ff-be6086da6dd5

import Mathlib
import Definitions.Def_TernarySync_Alphabet_RandomSource
import Theorems.Thm_TernarySync_Alphabet_thue_square_free
import Theorems.Thm_TernarySync_Alphabet_eq_17
import Theorems.Thm_TernarySync_Alphabet_lemma_2_2

section
set_option autoImplicit false

namespace TernarySync.Dev.T41
open TernarySync.Alphabet

theorem codeword_length : ∀ (a : Fin 3) (r : Fin 2), (codeword a r).length = 18 := by decide

theorem W_cons (a : Fin 3) (T : List (Fin 3)) (R : Fin (a :: T).length → Fin 2) :
    W (a :: T) R = codeword a (R 0) ++ W T (fun i => R i.succ) := by
  simp [W, List.ofFn_succ]

theorem W_length : ∀ (T : List (Fin 3)) (R : Fin T.length → Fin 2), (W T R).length = 18 * T.length
  | [], R => by simp [W]
  | a :: T, R => by
    rw [W_cons, List.length_append, codeword_length, W_length T]
    simp; ring

theorem factor_take (W : List (Fin 3)) (n i j : ℕ) (hj : j ≤ n) :
    factor (W.take n) i j = factor W i j := by
  unfold factor
  rw [List.drop_take, List.take_take]
  congr 1
  omega

end TernarySync.Dev.T41

namespace TernarySync.Alphabet
open TernarySync.Dev.T41 in
theorem chk_theorem_4_1 (n : ℕ) (hn : 1 ≤ n) :
    ∃ S : List (Fin 3), S.length = n ∧ IsSyncString ((2001 : ℝ) / 2002) S := by
  obtain ⟨T, hTl, hT⟩ := thue_square_free ((n + 17) / 18)
  obtain ⟨R, hR⟩ := eq_17 T hT
  have hlen : (W T R).length = 18 * T.length := W_length T R
  have hn' : n ≤ (W T R).length := by omega
  refine ⟨(W T R).take n, by simp [hn'], ?_⟩
  have key := lemma_2_2 ((W T R).take n) ((1 : ℝ) / 1000) (by norm_num) (by norm_num) (by
    intro t ℓ hℓ h2
    have hlt : ((W T R).take n).length = n := by simp [hn']
    rw [hlt] at h2
    rw [factor_take _ n _ _ (by omega), factor_take _ n _ _ (by omega)]
    have := hR t ℓ hℓ (by omega)
    simpa [blockX, blockY, show t + ℓ + ℓ = t + 2 * ℓ by ring] using this)
  have := key.1 ((2001 : ℝ) / 2002) (by norm_num) (by norm_num) (by norm_num)
  exact this
end TernarySync.Alphabet
end

theorem solution : type_of% @TernarySync.Alphabet.chk_theorem_4_1 := @TernarySync.Alphabet.chk_theorem_4_1
