-- Prove2me | solution 1 for TaoFivePrimes.positive_zero_bin_count
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-27T21:48:16.15033+00:00
-- url     : https://prove2.me/submissions/f9829e6f-3f32-42ea-8475-d1c4d0e6b970

-- Uses the published zero-count increment theorem.
import Theorems.Thm_ExplicitPNT_DusartTable1_Modules_ZeroCountIncrement
import Mathlib.Tactic

set_option autoImplicit false
set_option maxHeartbeats 1000000
open DusartSmoothing

private lemma main_increment (H t c : ℝ) (hH : 0 < H) (hHt : H ≤ t) (hc : 0 < c) :
    t/c * (Real.log (t/c)-1) - H/c * (Real.log (H/c)-1) ≤
      (t-H)/c * Real.log (t/c) := by
  have ht : 0 < t := lt_of_lt_of_le hH hHt
  have hlog := Real.log_le_sub_one_of_pos (div_pos ht hH)
  have hmul : H * Real.log (t/H) ≤ t-H := by
    have hh := mul_le_mul_of_nonneg_left hlog hH.le
    have he : H * (t/H-1) = t-H := by field_simp
    linarith
  have hdiff : Real.log (t/c)-Real.log (H/c) = Real.log (t/H) := by
    rw [Real.log_div ht.ne' hc.ne', Real.log_div hH.ne' hc.ne',
      Real.log_div ht.ne' hH.ne']
    ring
  have hbound : H * (Real.log (t/c)-Real.log (H/c)) ≤ t-H := by
    rw [hdiff]
    exact hmul
  have hnum : t * (Real.log (t/c)-1) - H * (Real.log (H/c)-1) ≤
      (t-H) * Real.log (t/c) := by nlinarith only [hbound]
  have hleft : t/c * (Real.log (t/c)-1) - H/c * (Real.log (H/c)-1) =
      (t*(Real.log (t/c)-1)-H*(Real.log (H/c)-1))/c := by ring
  have hright : (t-H)/c * Real.log (t/c) = ((t-H)*Real.log (t/c))/c := by ring
  rw [hleft,hright]
  exact div_le_div_of_nonneg_right hnum hc.le

theorem solution (Z : Finset ℂ) (L U : ℝ) (hL : 4 ≤ L) (hLU : L ≤ U)
    (hZ : ∀ ρ ∈ Z, RvM.IsNontrivialZero ρ ∧ L < ρ.im ∧ ρ.im ≤ U) :
    (∑ ρ ∈ Z, (RvM.zeroMult ρ : ℝ)) ≤
      (U-L)/(2*Real.pi)*Real.log (U/(2*Real.pi)) + 18*Real.log (U+5) + 158 := by
  classical
  have hpositive : ∀ ρ ∈ Z, RvM.IsNontrivialZero ρ ∧ 0 < ρ.im := by
    intro ρ hρ
    exact ⟨(hZ ρ hρ).1, by linarith [(hZ ρ hρ).2.1]⟩
  have hlower : ∀ ρ ∈ Z, L < ρ.im := by
    intro ρ hρ
    exact (hZ ρ hρ).2.1
  have hcount := ExplicitPNT.DusartTable1.Modules.ZeroCountIncrement.2 Z hpositive L U hL hLU hlower
  have he : finiteZeroCount Z RvM.zeroMult Complex.im U =
      ∑ ρ ∈ Z, (RvM.zeroMult ρ : ℝ) := by
    unfold finiteZeroCount
    apply Finset.sum_congr rfl
    intro ρ hρ
    simp [primeStep, (hZ ρ hρ).2.2]
  rw [he] at hcount
  have hm := main_increment L U (2*Real.pi) (by linarith) hLU (by positivity)
  have hl : Real.log (L+5) ≤ Real.log (U+5) :=
    Real.log_le_log (by linarith) (by linarith)
  dsimp [RvM.countingMain] at hcount
  linarith
