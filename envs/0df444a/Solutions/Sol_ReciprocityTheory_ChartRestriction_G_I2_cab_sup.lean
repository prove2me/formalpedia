-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.I2.cab_sup
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T13:26:38.315482+00:00
-- url     : https://prove2.me/submissions/9faab34f-e342-4c1c-a87a-bbebd6468a7e

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_PropAA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GaussianTailBound
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_ColAbelB
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_sqrt_pi_mul_firstMinimum_ge

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.I2
open MeasureTheory
noncomputable section
variable {ι : Type} [Fintype ι]
namespace ReciprocityTheory.ChartRestriction.G.I2
theorem _root_.solution (hS : GSupStatement) (Y : GT ι) (q c : ℕ) (hq : 2 ≤ q) (R0 : ℝ) (hR0 : 0 < R0)
    (hlat : ∀ γ ∈ lat Y.b, γ ≠ 0 → R0 ≤ Real.sqrt (q * Real.pi) * ‖γ‖)
    (h90 : 90 * (Fintype.card ι : ℝ) ≤ R0 ^ 2) (β : EuclideanSpace ℂ ι → ℂ) (hβ : β ∈ Y.Sec q)
    (hl2 : Y.l2 q β ≤ 6 * (c.factorial * (2 / (q * Real.pi)) ^ c * (2 / q) ^ Fintype.card ι))
    (w : EuclideanSpace ℂ ι) :
    Y.ptN2 q β w ≤ 12 * (5.12 : ℝ) ^ Fintype.card ι * c.factorial * (2 / (q * Real.pi)) ^ c := by
  have hq1 : 1 ≤ q := by omega
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (by omega : 0 < q)
  have h := hS ι Y q hq1 β hβ w
  set G := Fintype.card ι with hG
  set A := 4 * Real.sqrt (2 * G) / (Real.sqrt (q * Real.pi) * Y.la1) with hA
  have hA2 : (1 + A) ^ 2 ≤ 2.56 := by
    rcases Nat.eq_zero_or_pos G with h0 | h0
    · rw [hA, h0]; simp; norm_num
    · have hne : Nonempty ι := Fintype.card_pos_iff.mp h0
      have hla := sqrt_pi_mul_firstMinimum_ge Y q R0 hq1 hne hlat
      have hlap : 0 < Real.sqrt (q * Real.pi) * Y.la1 := lt_of_lt_of_le hR0 hla
      have hA0 : 0 ≤ A := by rw [hA]; positivity
      have hAle : A ≤ 4 * Real.sqrt (2 * G) / R0 := by
        rw [hA]; exact div_le_div_of_nonneg_left (by positivity) hR0 hla
      have hsq : (4 * Real.sqrt (2 * G) / R0) ^ 2 ≤ 0.36 := by
        rw [div_pow, mul_pow, Real.sq_sqrt (by positivity), div_le_iff₀ (by positivity)]
        nlinarith
      have : A ≤ 0.6 := by
        have h1 : A ^ 2 ≤ 0.36 := le_trans (pow_le_pow_left₀ hA0 hAle 2) hsq
        nlinarith
      nlinarith
  have hpow : (1 + A) ^ (2 * G) ≤ 2.56 ^ G := by
    rw [pow_mul]; exact pow_le_pow_left₀ (by positivity) hA2 G
  have hl0 : 0 ≤ Y.l2 q β := by
    unfold GT.l2
    rw [MeasureTheory.setAverage_eq]
    exact smul_nonneg (inv_nonneg.2 MeasureTheory.measureReal_nonneg)
      (MeasureTheory.integral_nonneg fun v => mul_nonneg (sq_nonneg _) (Real.exp_pos _).le)
  have hqG : (0 : ℝ) ≤ 2 * (q : ℝ) ^ G := by positivity
  calc Y.ptN2 q β w ≤ 2 * (q : ℝ) ^ G * (1 + A) ^ (2 * G) * Y.l2 q β := h
    _ ≤ 2 * (q : ℝ) ^ G * 2.56 ^ G * (6 * (c.factorial * (2 / (q * Real.pi)) ^ c * (2 / q) ^ G)) := by
        gcongr
    _ = 12 * ((q : ℝ) * (2 / q) * 2.56) ^ G * c.factorial * (2 / (q * Real.pi)) ^ c := by
        rw [mul_pow, mul_pow]; ring
    _ = 12 * (5.12 : ℝ) ^ G * c.factorial * (2 / (q * Real.pi)) ^ c := by
        congr 3; field_simp; norm_num
end ReciprocityTheory.ChartRestriction.G.I2
