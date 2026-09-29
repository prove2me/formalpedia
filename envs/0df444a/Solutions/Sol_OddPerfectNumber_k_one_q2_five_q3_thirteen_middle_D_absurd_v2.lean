-- Prove2me | solution 1 for OddPerfectNumber.k_one_q2_five_q3_thirteen_middle_D_absurd_v2
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-15T02:07:05.503225+00:00
-- url     : https://prove2.me/submissions/337ae90f-5972-4d9a-87b3-53fc52171c8e

import Mathlib
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_thirteen_middle_abundance_cut_v2
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_thirteen_middle_residual_absurd_v2

theorem solution
    (m a b c e D p q4 sigma : Nat)
    (hfac : m ^ 2 = 3 ^ (2*a) * 5 ^ (2*b) * 13 ^ (2*c) * q4 ^ (2*e))
    (hsigma : sigma =
      (∑ i ∈ Finset.range (2*a + 1), 3 ^ i) *
      (∑ i ∈ Finset.range (2*b + 1), 5 ^ i) *
      (∑ i ∈ Finset.range (2*c + 1), 13 ^ i) *
      (∑ i ∈ Finset.range (2*e + 1), q4 ^ i))
    (hrel : D * sigma = p * m ^ 2)
    (hcases :
      (D = 51 ∧ p = 101 ∧ q4 = 17) ∨
      (D = 57 ∧ p = 113 ∧ q4 = 19) ∨
      (D = 69 ∧ p = 137 ∧ q4 = 23) ∨
      (D = 79 ∧ p = 157 ∧ q4 = 79) ∨
      (D = 87 ∧ p = 173 ∧ q4 = 29) ∨
      (D = 115 ∧ p = 229 ∧ q4 = 23) ∨
      (D = 129 ∧ p = 257 ∧ q4 = 43) ∨
      (D = 141 ∧ p = 281 ∧ q4 = 47) ∨
      (D = 159 ∧ p = 317 ∧ q4 = 53) ∨
      (D = 177 ∧ p = 353 ∧ q4 = 59) ∨
      (D = 187 ∧ p = 373 ∧ q4 = 17) ∨
      (D = 201 ∧ p = 401 ∧ q4 = 67) ∨
      (D = 205 ∧ p = 409 ∧ q4 = 41))
    (hq4prime : q4.Prime) (ha : 2 ≤ a) (hb : 8 ≤ b)
    (hc : 2 ≤ c) (he : 1 ≤ e) :
    False := by
  have habund :
        (D = 51 ∧ p = 101 ∧ q4 = 17) ∨
        (D = 57 ∧ p = 113 ∧ q4 = 19) ∨
        (D = 69 ∧ p = 137 ∧ q4 = 23) ∨
        (D = 87 ∧ p = 173 ∧ q4 = 29) ∨
        (D = 115 ∧ p = 229 ∧ q4 = 23) ∨
        (D = 129 ∧ p = 257 ∧ q4 = 43) ∨
        (D = 141 ∧ p = 281 ∧ q4 = 47) ∨
        (D = 187 ∧ p = 373 ∧ q4 = 17) ∨
        (D = 205 ∧ p = 409 ∧ q4 = 41) → False := by
    intro hsmall
    exact OddPerfectNumber.k_one_q2_five_q3_thirteen_middle_abundance_cut_v2
      m a b c e D p q4 sigma hfac hsigma hrel hsmall hq4prime (by omega) ha hb hc he
  have hresid :
        (D = 79 ∧ p = 157 ∧ q4 = 79) ∨
        (D = 159 ∧ p = 317 ∧ q4 = 53) ∨
        (D = 177 ∧ p = 353 ∧ q4 = 59) ∨
        (D = 201 ∧ p = 401 ∧ q4 = 67) → False := by
    intro hres
    exact OddPerfectNumber.k_one_q2_five_q3_thirteen_middle_residual_absurd_v2
      m a b c e D p q4 sigma hfac hsigma hrel hb hres
  rcases hcases with h1 | hrest
  · exact habund (Or.inl h1)
  rcases hrest with h2 | hrest
  · exact habund (Or.inr (Or.inl h2))
  rcases hrest with h3 | hrest
  · exact habund (Or.inr (Or.inr (Or.inl h3)))
  rcases hrest with h4 | hrest
  · exact hresid (Or.inl h4)
  rcases hrest with h5 | hrest
  · exact habund (Or.inr (Or.inr (Or.inr (Or.inl h5))))
  rcases hrest with h6 | hrest
  · exact habund (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h6)))))
  rcases hrest with h7 | hrest
  · exact habund (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h7))))))
  rcases hrest with h8 | hrest
  · exact habund (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h8)))))))
  rcases hrest with h9 | hrest
  · exact hresid (by aesop)
  rcases hrest with h10 | hrest
  · exact hresid (by aesop)
  rcases hrest with h11 | hrest
  · exact habund (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h11))))))))
  rcases hrest with h12 | h13
  · exact hresid (by aesop)
  · exact habund (by aesop)
