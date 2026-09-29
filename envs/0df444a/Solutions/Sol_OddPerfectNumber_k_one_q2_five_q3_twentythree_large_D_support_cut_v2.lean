-- Prove2me | solution 1 for OddPerfectNumber.k_one_q2_five_q3_twentythree_large_D_support_cut_v2
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-14T23:34:44.671316+00:00
-- url     : https://prove2.me/submissions/03551f62-de9b-416a-b5af-9efbd6ceb789

import Mathlib
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_twentythree_large_D_candidates_v4

theorem solution (D p q4 : Nat)
    (hDlow : 111 ≤ D) (hDhigh : D ≤ 685)
    (hp : p.Prime) (hp4 : p % 4 = 1) (hp_eq : p = 2 * D - 1)
    (hq4 : q4.Prime) (hq4gt : 47 < q4) (hq4le : q4 ≤ 61)
    (hq4dvd : q4 ∣ D)
    (hDsupport : ∀ r, r.Prime → r ∣ D →
      r = 3 ∨ r = 5 ∨ r = 23 ∨ r = q4) :
    (D = 159 ∧ p = 317 ∧ q4 = 53) ∨
    (D = 177 ∧ p = 353 ∧ q4 = 59) ∨
    (D = 477 ∧ p = 953 ∧ q4 = 53) ∨
    (D = 531 ∧ p = 1061 ∧ q4 = 59) ∨
    (D = 549 ∧ p = 1097 ∧ q4 = 61) := by
  have hcases := OddPerfectNumber.k_one_q2_five_q3_twentythree_large_D_candidates_v4
    D p q4 hDlow hDhigh hp hp4 hp_eq hq4 hq4gt hq4le hq4dvd
  rcases hcases with h1 | h2 | h3 | h4 | h5 | h6 | h7
  · exact Or.inl h1
  · exact Or.inr (Or.inl h2)
  · rcases h3 with ⟨rfl, rfl, rfl⟩
    have h7dvd : 7 ∣ 427 := by norm_num
    have hs := hDsupport 7 (by norm_num) h7dvd
    norm_num at hs
  · exact Or.inr (Or.inr (Or.inl h4))
  · exact Or.inr (Or.inr (Or.inr (Or.inl h5)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr h6)))
  · rcases h7 with ⟨rfl, rfl, rfl⟩
    have h11dvd : 11 ∣ 649 := by norm_num
    have hs := hDsupport 11 (by norm_num) h11dvd
    norm_num at hs
