-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Bridge50.P44.otp_perfect
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-31T00:28:32.724744+00:00
-- url     : https://prove2.me/submissions/2e12b006-85ff-47ee-9831-69e8b9215bcc

import Definitions.Def_QAlgorithms_Papers_Independent_Bridge50_P44

set_option autoImplicit false
open QAlgorithms.Papers.Independent.Bridge50.P44
open scoped BigOperators

private lemma word_xor_cancel_right {n : ℕ} (x k : Fin n → Bool) :
    xorWord (xorWord x k) k = x := by
  funext i
  cases hx : x i <;> cases hk : k i <;> simp [xorWord, hx, hk]

private lemma word_xor_cancel_left {n : ℕ} (x k : Fin n → Bool) :
    xorWord x (xorWord x k) = k := by
  funext i
  cases hx : x i <;> cases hk : k i <;> simp [xorWord, hx, hk]

theorem solution (n : ℕ) (x : Fin n → Bool) :
    otpReal x = otpIdeal x ∧
    ∀ g : ((Fin n → Bool) × (Fin n → Bool)) → Set.Icc (0 : ℝ) 1,
      binaryTestSuccess (otpReal x) (otpIdeal x) g = 1 / 2 := by
  classical
  have heq : otpReal x = otpIdeal x := by
    funext out
    rcases out with ⟨y, c⟩
    simp only [otpReal, word_xor_cancel_right, otpIdeal, Prod.mk.injEq]
    by_cases hy : y = x
    · subst y
      simp only [true_and, if_true]
      rw [Finset.sum_eq_single (xorWord x c)]
      · simp [word_xor_cancel_left]
      · intro k hk hne
        have hck : c ≠ xorWord x k := by
          intro hc
          apply hne
          have he := congrArg (xorWord x) hc
          simpa [word_xor_cancel_left] using he.symm
        simp [hck]
      · simp
    · simp [hy]
  refine ⟨heq, ?_⟩
  intro g
  rw [heq]
  unfold binaryTestSuccess
  have hpoint : ∀ z, otpIdeal x z * (g z).val +
      otpIdeal x z * (1 - (g z).val) = otpIdeal x z := by
    intro z
    ring
  simp only [hpoint, tsum_fintype]
  have hcard : (Fintype.card (Fin n → Bool) : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  have hsum : (∑ z : (Fin n → Bool) × (Fin n → Bool), otpIdeal x z) = 1 := by
    rw [Fintype.sum_prod_type, Finset.sum_comm]
    simp only [otpIdeal]
    simp [hcard]
  rw [hsum]
  ring

#print axioms solution
