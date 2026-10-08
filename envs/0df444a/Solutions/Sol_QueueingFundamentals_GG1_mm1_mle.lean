-- Prove2me | solution 1 for QueueingFundamentals.GG1.mm1_mle
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-05T20:44:22.358215+00:00
-- url     : https://prove2.me/submissions/357d7d42-ab0f-47ba-b07a-73222e2120a0

import Mathlib
import Definitions.Def_QueueingFundamentals_GG1_Likelihood

set_option autoImplicit false

namespace QueueingFundamentals.GG1.MM1MleAux

lemma key_le (n c x : ℝ) (hn : 0 < n) (hc : 0 < c) (hx : 0 < x) :
    -x * c + n * Real.log x ≤ -(n / c) * c + n * Real.log (n / c) := by
  have hy : 0 < x * c / n := by positivity
  have hlog : Real.log x - Real.log (n / c) = Real.log (x * c / n) := by
    rw [← Real.log_div hx.ne' (by positivity)]
    congr 1; field_simp
  have h1 := Real.log_le_sub_one_of_pos hy
  have h2 : n * Real.log (x * c / n) ≤ n * (x * c / n - 1) :=
    mul_le_mul_of_nonneg_left h1 hn.le
  have h3 : n * (x * c / n - 1) = x * c - n := by field_simp
  have h4 : -(n / c) * c = -n := by field_simp
  nlinarith [hlog, h2, h3, h4]

lemma key_lt (n c x : ℝ) (hn : 0 < n) (hc : 0 < c) (hx : 0 < x) (hne : x ≠ n / c) :
    -x * c + n * Real.log x < -(n / c) * c + n * Real.log (n / c) := by
  have hy : 0 < x * c / n := by positivity
  have hy1 : x * c / n ≠ 1 := by
    intro h
    apply hne
    field_simp at h
    field_simp
    linarith
  have hlog : Real.log x - Real.log (n / c) = Real.log (x * c / n) := by
    rw [← Real.log_div hx.ne' (by positivity)]
    congr 1; field_simp
  have h1 := Real.log_lt_sub_one_of_pos hy hy1
  have h2 : n * Real.log (x * c / n) < n * (x * c / n - 1) :=
    mul_lt_mul_of_pos_left h1 hn
  have h3 : n * (x * c / n - 1) = x * c - n := by field_simp
  have h4 : -(n / c) * c = -n := by field_simp
  nlinarith [hlog, h2, h3, h4]

end QueueingFundamentals.GG1.MM1MleAux

open QueueingFundamentals.GG1 in
theorem solution (t tb : ℝ) (htb : 0 < tb) (htbt : tb ≤ t) (na nc : ℕ) (hna : 0 < na)
    (hnc : 0 < nc) :
    0 < (na : ℝ) / t ∧ 0 < (nc : ℝ) / tb ∧
    ∀ lam mu : ℝ, 0 < lam → 0 < mu → (lam, mu) ≠ ((na : ℝ) / t, (nc : ℝ) / tb) →
      mm1LogLik t tb na nc lam mu < mm1LogLik t tb na nc ((na : ℝ) / t) ((nc : ℝ) / tb) := by
  have ht : 0 < t := lt_of_lt_of_le htb htbt
  have hna' : (0 : ℝ) < na := by exact_mod_cast hna
  have hnc' : (0 : ℝ) < nc := by exact_mod_cast hnc
  refine ⟨by positivity, by positivity, ?_⟩
  intro lam mu hlam hmu hne
  unfold mm1LogLik
  by_cases h1 : lam = (na : ℝ) / t
  · have h2 : mu ≠ (nc : ℝ) / tb := by
      intro h2; exact hne (by rw [h1, h2])
    have a := QueueingFundamentals.GG1.MM1MleAux.key_le (na : ℝ) t lam hna' ht hlam
    have b := QueueingFundamentals.GG1.MM1MleAux.key_lt (nc : ℝ) tb mu hnc' htb hmu h2
    linarith
  · have a := QueueingFundamentals.GG1.MM1MleAux.key_lt (na : ℝ) t lam hna' ht hlam h1
    have b := QueueingFundamentals.GG1.MM1MleAux.key_le (nc : ℝ) tb mu hnc' htb hmu
    linarith
