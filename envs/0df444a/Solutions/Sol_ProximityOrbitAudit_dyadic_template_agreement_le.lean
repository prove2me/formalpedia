-- Prove2me | solution 1 for ProximityOrbitAudit.dyadic_template_agreement_le
-- status  : ACCEPTED   (prove)
-- author  : @yukon
-- created : 2026-10-04T12:14:10.714229+00:00
-- url     : https://prove2.me/submissions/eb1c6390-cb00-48b8-8e8f-698c100925da

import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Ring

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem solution (j t h c : ℕ) (hj : j ≤ 17)
    (hrow : c + 2^j * (t-h-3) ≤ 131071)
    (hcount : (262144 / 2^j) * (2130706433 : ℕ)^h *
      ((2130706433 : ℕ)^6 / 2^128) <
      Nat.choose (262144 / 2^j - 1) t) :
    2^j*t+c ≤ 139775 := by
  let p : ℕ := 2130706433
  let densityFloor : ℕ := p^6 / 2^128
  change (262144 / 2^j) * p^h * densityFloor <
    Nat.choose (262144 / 2^j - 1) t at hcount
  have agreement_cap (d t h c : ℕ)
      (hrow : c + d * (t - h - 3) ≤ 131071) :
      d * t + c ≤ 131071 + d * (h + 3) := by
    have ht : t ≤ t-h-3+h+3 := by omega
    calc
      d*t+c ≤ d*(t-h-3+h+3)+c := by gcongr
      _ = (c+d*(t-h-3))+d*(h+3) := by ring
      _ ≤ 131071+d*(h+3) := Nat.add_le_add_right hrow _

  have power_key_lower (k a b h : ℕ) (hh : 2*a+b ≤ h) :
      2^(k+61*a+30*b+57) ≤ 2^k * p^h * densityFloor := by
    have hp2 : (2 : ℕ)^61 ≤ p^2 := by decide +kernel
    have hp1 : (2 : ℕ)^30 ≤ p := by decide +kernel
    have hq : (2 : ℕ)^57 ≤ densityFloor := by decide +kernel
    calc
      2^(k+61*a+30*b+57) = 2^k * (2^61)^a * (2^30)^b * 2^57 := by
        simp only [pow_add, pow_mul]
      _ ≤ 2^k * (p^2)^a * p^b * densityFloor := by gcongr
      _ = 2^k * p^(2*a+b) * densityFloor := by rw [pow_add, pow_mul]; ring
      _ ≤ 2^k * p^h * densityFloor := by
        exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _
          (pow_le_pow_right' (by decide : 1 ≤ p) hh))

  have key_dominates_subsets (k a b h t : ℕ)
      (he : 2^k-1 ≤ k+61*a+30*b+57) (hh : 2*a+b ≤ h) :
      Nat.choose (2^k-1) t ≤ 2^k * p^h * densityFloor := by
    exact (Nat.choose_le_two_pow _ _).trans
      ((pow_le_pow_right' (by decide : 1 ≤ (2 : ℕ)) he).trans
        (power_key_lower k a b h hh))

  have central128 : Nat.choose 127 63 ≤ 128*p^2*densityFloor := by
    rw [Nat.choose_eq_fast_choose]
    decide +kernel

  have central256 : Nat.choose 255 127 ≤ 256*p^6*densityFloor := by
    rw [Nat.choose_eq_fast_choose]
    decide +kernel

  have key128_dominates (h t : ℕ) (hh : 2 ≤ h) :
      Nat.choose 127 t ≤ 128*p^h*densityFloor := by
    have hm : Nat.choose 127 t ≤ Nat.choose 127 63 := by
      simpa using Nat.choose_le_middle t 127
    exact (hm.trans central128).trans
      (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _
        (pow_le_pow_right' (by decide : 1 ≤ p) hh)))

  have key256_dominates (h t : ℕ) (hh : 6 ≤ h) :
      Nat.choose 255 t ≤ 256*p^h*densityFloor := by
    have hm : Nat.choose 255 t ≤ Nat.choose 255 127 := by
      simpa using Nat.choose_le_middle t 255
    exact (hm.trans central256).trans
      (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _
        (pow_le_pow_right' (by decide : 1 ≤ p) hh)))
  by_contra hbad
  have hagreement : 139776 ≤ 2^j*t+c := by omega
  have hcap := agreement_cap (2^j) t h c hrow
  interval_cases j <;>
    norm_num only [Nat.reducePow, Nat.reduceDiv, Nat.reduceSub] at hcap hagreement hcount
  · have hn := key_dominates_subsets 18 4351 0 h t (by decide +kernel) (by omega)
    norm_num only [Nat.reducePow, Nat.reduceSub] at hn
    exact (Nat.not_lt_of_ge hn) hcount
  · have hn := key_dominates_subsets 17 2175 0 h t (by decide +kernel) (by omega)
    norm_num only [Nat.reducePow, Nat.reduceSub] at hn
    exact (Nat.not_lt_of_ge hn) hcount
  · have hn := key_dominates_subsets 16 1087 0 h t (by decide +kernel) (by omega)
    norm_num only [Nat.reducePow, Nat.reduceSub] at hn
    exact (Nat.not_lt_of_ge hn) hcount
  · have hn := key_dominates_subsets 15 543 0 h t (by decide +kernel) (by omega)
    norm_num only [Nat.reducePow, Nat.reduceSub] at hn
    exact (Nat.not_lt_of_ge hn) hcount
  · have hn := key_dominates_subsets 14 271 0 h t (by decide +kernel) (by omega)
    norm_num only [Nat.reducePow, Nat.reduceSub] at hn
    exact (Nat.not_lt_of_ge hn) hcount
  · have hn := key_dominates_subsets 13 135 0 h t (by decide +kernel) (by omega)
    norm_num only [Nat.reducePow, Nat.reduceSub] at hn
    exact (Nat.not_lt_of_ge hn) hcount
  · have hn := key_dominates_subsets 12 67 0 h t (by decide +kernel) (by omega)
    norm_num only [Nat.reducePow, Nat.reduceSub] at hn
    exact (Nat.not_lt_of_ge hn) hcount
  · have hn := key_dominates_subsets 11 33 0 h t (by decide +kernel) (by omega)
    norm_num only [Nat.reducePow, Nat.reduceSub] at hn
    exact (Nat.not_lt_of_ge hn) hcount
  · have hn := key_dominates_subsets 10 16 0 h t (by decide +kernel) (by omega)
    norm_num only [Nat.reducePow, Nat.reduceSub] at hn
    exact (Nat.not_lt_of_ge hn) hcount
  · have hn := key_dominates_subsets 9 7 1 h t (by decide +kernel) (by omega)
    norm_num only [Nat.reducePow, Nat.reduceSub] at hn
    exact (Nat.not_lt_of_ge hn) hcount
  · have hn := key256_dominates h t (by omega)
    norm_num only [Nat.reducePow, Nat.reduceSub] at hn
    exact (Nat.not_lt_of_ge hn) hcount
  · have hn := key128_dominates h t (by omega)
    norm_num only [Nat.reducePow, Nat.reduceSub] at hn
    exact (Nat.not_lt_of_ge hn) hcount
  · have hn := key_dominates_subsets 6 0 0 h t (by decide +kernel) (by omega)
    norm_num only [Nat.reducePow, Nat.reduceSub] at hn
    exact (Nat.not_lt_of_ge hn) hcount
  · have hn := key_dominates_subsets 5 0 0 h t (by decide +kernel) (by omega)
    norm_num only [Nat.reducePow, Nat.reduceSub] at hn
    exact (Nat.not_lt_of_ge hn) hcount
  · have hn := key_dominates_subsets 4 0 0 h t (by decide +kernel) (by omega)
    norm_num only [Nat.reducePow, Nat.reduceSub] at hn
    exact (Nat.not_lt_of_ge hn) hcount
  · have hn := key_dominates_subsets 3 0 0 h t (by decide +kernel) (by omega)
    norm_num only [Nat.reducePow, Nat.reduceSub] at hn
    exact (Nat.not_lt_of_ge hn) hcount
  · have hn := key_dominates_subsets 2 0 0 h t (by decide +kernel) (by omega)
    norm_num only [Nat.reducePow, Nat.reduceSub] at hn
    exact (Nat.not_lt_of_ge hn) hcount
  · have hn := key_dominates_subsets 1 0 0 h t (by decide +kernel) (by omega)
    norm_num only [Nat.reducePow, Nat.reduceSub] at hn
    exact (Nat.not_lt_of_ge hn) hcount
