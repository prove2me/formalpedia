-- Prove2me | solution 1 for PaleyWeil.quadraticChar_norm
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-11-24T17:30:44.112791+00:00
-- url     : https://prove2.me/submissions/eff9d7eb-87d1-4409-b2f6-150d9e76f336

import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

namespace PaleyWeil
end PaleyWeil

section


namespace PaleyWeil

private theorem quotient_mul_half {q r : ℕ} (hq : q % 2 = 1) (hr : r % 2 = 1)
    (hqr : q - 1 ∣ r - 1) :
    ((r - 1) / (q - 1)) * (q / 2) = r / 2 := by
  have hq2 : q = 2 * (q / 2) + 1 := by omega
  have hr2 : r = 2 * (r / 2) + 1 := by omega
  have hm : ((r - 1) / (q - 1)) * (q - 1) = r - 1 := Nat.div_mul_cancel hqr
  have hqsub : q - 1 = 2 * (q / 2) := by omega
  have hrsub : r - 1 = 2 * (r / 2) := by omega
  rw [hqsub, hrsub] at hm ⊢
  nlinarith





end PaleyWeil

end

open PaleyWeil

theorem solution {K L : Type*} [Field K] [Field L]
    [Fintype K] [Fintype L] [DecidableEq K] [DecidableEq L] [Algebra K L]
    (hK : ringChar K ≠ 2) (hL : ringChar L ≠ 2) (x : L) :
    quadraticChar K (Algebra.norm K x) = quadraticChar L x := by
  have hcard : Fintype.card L = Fintype.card K ^ Module.finrank K L :=
    Module.card_eq_pow_finrank
  have hdiv : Fintype.card K - 1 ∣ Fintype.card L - 1 := by
    rw [hcard]
    exact Nat.sub_one_dvd_pow_sub_one _ _
  have hexponent :
      ((Fintype.card L - 1) / (Fintype.card K - 1)) * (Fintype.card K / 2) =
        Fintype.card L / 2 :=
    quotient_mul_half (FiniteField.odd_card_of_char_ne_two hK)
      (FiniteField.odd_card_of_char_ne_two hL) hdiv
  apply (quadraticChar_isQuadratic K).eq_of_eq_coe
    (quadraticChar_isQuadratic L) hL
  calc
    (quadraticChar K (Algebra.norm K x) : L) =
        algebraMap K L (quadraticChar K (Algebra.norm K x) : K) := by simp
    _ = algebraMap K L ((Algebra.norm K x) ^ (Fintype.card K / 2)) := by
      rw [quadraticChar_eq_pow_of_char_ne_two' hK]
    _ = (algebraMap K L (Algebra.norm K x)) ^ (Fintype.card K / 2) := by rw [map_pow]
    _ = (x ^ ((Fintype.card L - 1) / (Fintype.card K - 1))) ^
        (Fintype.card K / 2) := by
      rw [FiniteField.algebraMap_norm_eq_pow]
      simp only [Nat.card_eq_fintype_card]
    _ = x ^ (Fintype.card L / 2) := by rw [← pow_mul, hexponent]
    _ = (quadraticChar L x : L) :=
      (quadraticChar_eq_pow_of_char_ne_two' hL x).symm
