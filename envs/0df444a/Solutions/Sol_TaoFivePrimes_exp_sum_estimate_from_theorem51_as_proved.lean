-- Prove2me | solution 1 for TaoFivePrimes.exp_sum_estimate_from_theorem51_as_proved
-- status  : ACCEPTED   (prove)
-- author  : @Hartmann_Psi
-- created : 2026-09-14T18:07:12.672413+00:00
-- url     : https://prove2.me/submissions/b0061c99-3d5f-4c21-a6e9-8412f8618894

import Mathlib
import Definitions.Def_TaoFivePrimes_SmoothedExpSum
import Definitions.Def_TaoFivePrimes_RepresentationCount
import Theorems.Thm_TaoFivePrimes_smoothedExpSum_modulus_change

open Finset

section PartS6H
open Finset


namespace TaoS6

/-- The purely numerical inequality behind the Section 6 collapse. -/
theorem master (A B Y ll : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B) (hY : 0 ≤ Y) (hll : 9 ≤ ll) :
    2 * A * (ll ^ 2 + ll)
      + 1.78 * (Y / 100 + 0.25 * B) * (8 + 5 * ll) * (0.694 + 5 * ll)
      + (0.1 * A + 0.39 * B) * ((4.664 + ll) * (5 * ll))
      + 5.2178 * Y * (2.332 + 3 * ll)
      + 0.0028 * Y * ll
    ≤ (0.14 * A + 0.64 * B + 0.15 * Y) * (5 * ll) * (5 * ll + 11.3) := by
  have hpA : (0:ℝ) ≤ ll ^ 2 + 3.578 * ll := by nlinarith
  have hpB : (0:ℝ) ≤ 2.925 * ll ^ 2 + 7.72105 * ll - 2.47064 := by nlinarith
  have hpY : (0:ℝ) ≤ 3.305 * ll ^ 2 - 7.954966 * ll - 12.2667352 := by nlinarith
  nlinarith [mul_nonneg hA hpA, mul_nonneg hB hpB, mul_nonneg hY hpY]

/-- `η₀` is bounded by `2.7726`. -/
theorem eta0_abs_le (t : ℝ) : |TaoFivePrimes.eta0 t| ≤ 2.7726 := by
  have hl2 : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
  have hl2' : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  unfold TaoFivePrimes.eta0
  split_ifs with h
  · have h1 : 0 ≤ max 0 (Real.log 2 - |Real.log (2 * t)|) := le_max_left _ _
    have h2 : max 0 (Real.log 2 - |Real.log (2 * t)|) ≤ Real.log 2 := by
      apply max_le hl2'.le
      have := abs_nonneg (Real.log (2 * t))
      linarith
    rw [abs_of_nonneg (by linarith)]
    linarith
  · simp only [abs_zero]; norm_num

/-- `η₀` vanishes above `1`. -/
theorem eta0_supp (t : ℝ) (ht : 1 < t) : TaoFivePrimes.eta0 t = 0 := by
  have ht0 : 0 < t := lt_trans one_pos ht
  have h2t : (1:ℝ) < 2 * t := by linarith
  have hlog : 0 < Real.log (2 * t) := Real.log_pos h2t
  have : Real.log 2 < Real.log (2 * t) := by
    apply Real.log_lt_log (by norm_num)
    linarith
  unfold TaoFivePrimes.eta0
  rw [if_pos ht0, abs_of_pos hlog]
  rw [max_eq_left (by linarith)]
  ring

end TaoS6

namespace TaoS6
open scoped ArithmeticFunction.vonMangoldt

theorem omega_le (x : ℝ) (q₀ : ℕ)
    (hq₀ : ∀ p ∈ q₀.primeFactors, (p : ℝ) ≤ Real.sqrt x) :
    (q₀.primeFactors.card : ℝ) ≤ Real.sqrt x + 1 := by
  have hsub : q₀.primeFactors ⊆ Finset.range (⌊Real.sqrt x⌋₊ + 1) := by
    intro p hp
    simp only [Finset.mem_range]
    have h1 : p ≤ ⌊Real.sqrt x⌋₊ := Nat.le_floor (hq₀ p hp)
    omega
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_range] at hcard
  have h2 : (⌊Real.sqrt x⌋₊ : ℝ) ≤ Real.sqrt x := Nat.floor_le (Real.sqrt_nonneg x)
  have h3 : (q₀.primeFactors.card : ℝ) ≤ ((⌊Real.sqrt x⌋₊ : ℕ) : ℝ) + 1 := by
    exact_mod_cast hcard
  linarith

theorem smoothedExpSum_zero_modulus (eta : ℝ → ℝ) (x α : ℝ) :
    TaoFivePrimes.smoothedExpSum eta 0 x α = 0 := by
  have h : ∀ n : ℕ,
      (if Nat.Coprime n 0 then
          (Λ n : ℂ) * TaoFivePrimes.expCircle (α * n) * ((eta ((n : ℝ) / x) : ℝ) : ℂ)
        else 0) = 0 := by
    intro n
    split_ifs with hc
    · rw [Nat.coprime_zero_right] at hc
      subst hc
      simp
    · rfl
  unfold TaoFivePrimes.smoothedExpSum
  simp only [h, tsum_zero]

theorem modulus_step (x α : ℝ) (hx : 1 ≤ x) (q₀ : ℕ)
    (hq₀ : ∀ p ∈ q₀.primeFactors, (p : ℝ) ≤ Real.sqrt x) :
    ‖TaoFivePrimes.smoothedExpSum TaoFivePrimes.eta0 q₀ x α‖
      ≤ ‖TaoFivePrimes.smoothedExpSum TaoFivePrimes.eta0 2 x α‖
        + (Real.sqrt x + 2) * 2.7726 * Real.log x := by
  have hlog : 0 ≤ Real.log x := Real.log_nonneg hx
  have hsq : 0 ≤ Real.sqrt x := Real.sqrt_nonneg x
  rcases Nat.eq_zero_or_pos q₀ with h0 | hpos
  · subst h0
    rw [smoothedExpSum_zero_modulus]
    have : (0:ℝ) ≤ (Real.sqrt x + 2) * 2.7726 * Real.log x := by positivity
    simp only [norm_zero]
    have := norm_nonneg (TaoFivePrimes.smoothedExpSum TaoFivePrimes.eta0 2 x α)
    linarith
  · set Sq := TaoFivePrimes.smoothedExpSum TaoFivePrimes.eta0 q₀ x α with hSq
    set S1 := TaoFivePrimes.smoothedExpSum TaoFivePrimes.eta0 1 x α with hS1
    set S2 := TaoFivePrimes.smoothedExpSum TaoFivePrimes.eta0 2 x α with hS2
    have h1 := TaoFivePrimes.smoothedExpSum_modulus_change TaoFivePrimes.eta0 2.7726 q₀ x α
      hpos hx eta0_abs_le eta0_supp
    have h2 := TaoFivePrimes.smoothedExpSum_modulus_change TaoFivePrimes.eta0 2.7726 2 x α
      (by norm_num) hx eta0_abs_le eta0_supp
    have hc2 : ((Nat.primeFactors 2).card : ℝ) = 1 := by
      rw [Nat.Prime.primeFactors Nat.prime_two]
      simp
    have hcq : (q₀.primeFactors.card : ℝ) ≤ Real.sqrt x + 1 := omega_le x q₀ hq₀
    rw [hc2] at h2
    have htri : ‖Sq‖ ≤ ‖S2‖ + ‖Sq - S1‖ + ‖S1 - S2‖ := by
      calc ‖Sq‖ = ‖S2 + (Sq - S1) + (S1 - S2)‖ := by ring_nf
        _ ≤ ‖S2 + (Sq - S1)‖ + ‖S1 - S2‖ := norm_add_le _ _
        _ ≤ ‖S2‖ + ‖Sq - S1‖ + ‖S1 - S2‖ := by
            gcongr
            exact norm_add_le _ _
    have hrev : ‖S1 - S2‖ = ‖S2 - S1‖ := norm_sub_rev _ _
    rw [hrev] at htri
    have hb1 : ‖Sq - S1‖ ≤ (Real.sqrt x + 1) * 2.7726 * Real.log x := by
      refine h1.trans ?_
      gcongr
    nlinarith [hb1, h2, htri, hlog]

end TaoS6

namespace TaoS6


theorem mul2_le {a b a' b' : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (ha' : a ≤ a') (hb' : b ≤ b') :
    a * b ≤ a' * b' := mul_le_mul ha' hb' hb (ha.trans ha')

theorem mul3_le {a b c a' b' c' : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (ha' : a ≤ a') (hb' : b ≤ b') (hc' : c ≤ c') : a * b * c ≤ a' * b' * c' :=
  mul2_le (mul_nonneg ha hb) hc (mul2_le ha hb ha' hb') hc'

theorem mul4_le {a b c d a' b' c' d' : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d)
    (ha' : a ≤ a') (hb' : b ≤ b') (hc' : c ≤ c') (hd' : d ≤ d') :
    a * b * c * d ≤ a' * b' * c' * d' :=
  mul2_le (mul_nonneg (mul_nonneg ha hb) hc) hd (mul3_le ha hb hc ha' hb' hc') hd'

set_option maxHeartbeats 4000000 in
theorem main_core (x α : ℝ) (q : ℕ)
    (hx : (10 : ℝ) ^ 20 ≤ x)
    (hq : 100 ≤ q) (hqx : (q : ℝ) ≤ x / 100)
    (hminor : ∀ U V : ℝ, 1 < U → 1 < V → U < x → V < x → U * V ≤ x / 4 → x ≤ U * V ^ 2 →
        40 ≤ U → 40 ≤ V →
        ‖TaoFivePrimes.smoothedExpSum TaoFivePrimes.eta0 2 x α‖ ≤
          (x / q) * Real.log x * (Real.log (2 * U * V / q + 4) + 4)
            + 1.78 * (U * V + (5 / 2) * q) * (8 + Real.log q) * Real.log (2 * x)
          + (0.1 * x / Real.sqrt q + 0.39 * x / Real.sqrt (x / q))
              * Real.log (x / (U * V)) * Real.log (V * x / U)
          + (0.55 * x / Real.sqrt U + 1.1 * x / Real.sqrt V) * Real.log (x / U)) :
    ‖TaoFivePrimes.smoothedExpSum TaoFivePrimes.eta0 2 x α‖
      ≤ (0.14 * x / Real.sqrt q + 0.64 * x / Real.sqrt (x / q) + 0.15 * x ^ (4 / 5 : ℝ))
          * Real.log x * (Real.log x + 11.3)
        - 0.0028 * x ^ (4 / 5 : ℝ) * (Real.log x / 5) := by
  have hx0 : (0:ℝ) < x := by nlinarith
  obtain ⟨y, hy0, hy5⟩ : ∃ y : ℝ, 0 < y ∧ y ^ 5 = x := by
    refine ⟨x ^ (1/5:ℝ), Real.rpow_pos_of_pos hx0 _, ?_⟩
    rw [← Real.rpow_natCast (x ^ (1/5:ℝ)) 5, ← Real.rpow_mul hx0.le]; norm_num
  have hy4x : x ^ (4/5 : ℝ) = y ^ 4 := by
    rw [← hy5, ← Real.rpow_natCast y 5, ← Real.rpow_mul hy0.le]; norm_num
  have hy4 : (10000:ℝ) ≤ y := by
    have h : ((10000:ℝ))^5 ≤ y^5 := by rw [hy5]; nlinarith
    exact le_of_pow_le_pow_left₀ (by norm_num) hy0.le h
  have hlogx : Real.log x = 5 * Real.log y := by
    rw [← hy5, Real.log_pow]; push_cast; ring
  have hll : 9 ≤ Real.log y := by
    have h2 : Real.exp 9 = (Real.exp 1)^(9:ℕ) := by rw [Real.exp_one_pow]; norm_num
    have h3 : (Real.exp 1)^(9:ℕ) ≤ (2.7182818286:ℝ)^(9:ℕ) :=
      pow_le_pow_left₀ (Real.exp_nonneg 1) Real.exp_one_lt_d9.le _
    have h4 : (2.7182818286:ℝ)^(9:ℕ) ≤ 10000 := by norm_num
    have he : Real.exp 9 ≤ y := by rw [h2]; linarith
    exact (Real.le_log_iff_exp_le hy0).mpr he
  ---- powers of y
  have hyp2 : (0:ℝ) ≤ y^2 := by positivity
  have hyp4 : (0:ℝ) ≤ y^4 := by positivity
  have hyp5 : (0:ℝ) ≤ y^5 := by positivity
  have hbig2 : (10:ℝ)^8 ≤ y^2 := by
    have h := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 10000) hy4 2
    norm_num at h ⊢; linarith
  have hbig4 : (10:ℝ)^16 ≤ y^4 := by
    have h := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 10000) hy4 4
    norm_num at h ⊢; linarith
  have h5ge : 10000 * y^4 ≤ y^5 := by
    nlinarith [mul_nonneg hyp4 (by linarith : (0:ℝ) ≤ y - 10000)]
  have h6ge : 10000 * y^5 ≤ y^6 := by
    nlinarith [mul_nonneg hyp5 (by linarith : (0:ℝ) ≤ y - 10000)]
  have h25 : y^2 ≤ y^5 := by
    nlinarith [mul_nonneg hyp2 (by nlinarith : (0:ℝ) ≤ y^3 - 1)]
  ---- facts about q
  have hq' : (100:ℝ) ≤ (q:ℝ) := by exact_mod_cast hq
  have hqpos : (0:ℝ) < (q:ℝ) := by linarith
  have hxq100 : (100:ℝ) ≤ x / q := by rw [le_div_iff₀ hqpos]; linarith
  have hsq10 : (10:ℝ) ≤ Real.sqrt (q:ℝ) := by
    have h := Real.sqrt_le_sqrt hq'
    rwa [show (100:ℝ) = 10^2 by norm_num, Real.sqrt_sq (by norm_num)] at h
  have hsqq : Real.sqrt (q:ℝ) * Real.sqrt (q:ℝ) = (q:ℝ) := Real.mul_self_sqrt hqpos.le
  have hs10 : (10:ℝ) ≤ Real.sqrt (x / (q:ℝ)) := by
    have h := Real.sqrt_le_sqrt hxq100
    rwa [show (100:ℝ) = 10^2 by norm_num, Real.sqrt_sq (by norm_num)] at h
  have hss : Real.sqrt (x/(q:ℝ)) * Real.sqrt (x/(q:ℝ)) = x/(q:ℝ) :=
    Real.mul_self_sqrt (by positivity)
  have hAle : x / (q:ℝ) ≤ (x / Real.sqrt (q:ℝ)) / 10 := by
    have hs0 : (0:ℝ) < Real.sqrt (q:ℝ) := by linarith
    rw [div_div, div_le_div_iff₀ hqpos (by positivity)]
    nlinarith [mul_nonneg hx0.le (mul_nonneg hs0.le (by linarith : (0:ℝ) ≤ Real.sqrt (q:ℝ) - 10))]
  have hBle : (q:ℝ) ≤ (x / Real.sqrt (x/(q:ℝ))) / 10 := by
    have hs0 : (0:ℝ) < Real.sqrt (x/(q:ℝ)) := by linarith
    rw [le_div_iff₀ (by norm_num : (0:ℝ) < 10), le_div_iff₀ hs0]
    have hxeq : Real.sqrt (x/(q:ℝ)) * Real.sqrt (x/(q:ℝ)) * q = x := by
      rw [hss]; field_simp
    nlinarith [mul_nonneg (mul_nonneg hqpos.le hs0.le)
      (by linarith : (0:ℝ) ≤ Real.sqrt (x/(q:ℝ)) - 10)]
  have hAnn : (0:ℝ) ≤ x / Real.sqrt (q:ℝ) := by positivity
  have hBnn : (0:ℝ) ≤ x / Real.sqrt (x/(q:ℝ)) := by positivity
  ---- log bounds
  have hl2 : Real.log 2 ≤ 0.694 := le_of_lt (lt_trans Real.log_two_lt_d9 (by norm_num))
  have hl2pos : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hllnn : (0:ℝ) ≤ Real.log y := by linarith
  have hlog2x : Real.log (2*x) ≤ 0.694 + 5 * Real.log y := by
    rw [Real.log_mul (by norm_num) (ne_of_gt hx0), hlogx]; linarith
  have hlog2xnn : (0:ℝ) ≤ Real.log (2*x) := Real.log_nonneg (by linarith)
  have hlog8y : Real.log (8*y) ≤ 2.082 + Real.log y := by
    rw [Real.log_mul (by norm_num) (ne_of_gt hy0)]
    have h8 : Real.log 8 = 3 * Real.log 2 := by
      rw [show (8:ℝ) = 2^3 by norm_num, Real.log_pow]; push_cast; ring
    rw [h8]; linarith
  have hlog8ynn : (0:ℝ) ≤ Real.log (8*y) := Real.log_nonneg (by linarith)
  have hlog4y3 : Real.log (4*y^3) ≤ 1.388 + 3 * Real.log y := by
    rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]
    have h4l : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4:ℝ) = 2^2 by norm_num, Real.log_pow]; push_cast; ring
    rw [h4l]; push_cast; linarith
  have hlog4y3nn : (0:ℝ) ≤ Real.log (4*y^3) := Real.log_nonneg (by nlinarith)
  have hlogq : Real.log (q:ℝ) ≤ 5 * Real.log y := by
    rw [← hlogx]; exact Real.log_le_log hqpos (by linarith)
  have hlogqnn : (0:ℝ) ≤ Real.log (q:ℝ) := Real.log_nonneg (by linarith)
  have hT1arg : Real.log (y^4/(4*(q:ℝ)) + 4) ≤ 4 * Real.log y := by
    have hb : y^4/(4*(q:ℝ)) + 4 ≤ y^4 := by
      have h1 : y^4/(4*(q:ℝ)) ≤ y^4/400 := by gcongr; linarith
      linarith
    calc Real.log (y^4/(4*(q:ℝ)) + 4) ≤ Real.log (y^4) := Real.log_le_log (by positivity) hb
      _ = 4 * Real.log y := by rw [Real.log_pow]; push_cast; ring
  have hT1argnn : (0:ℝ) ≤ Real.log (y^4/(4*(q:ℝ)) + 4) := by
    apply Real.log_nonneg
    have : (0:ℝ) ≤ y^4/(4*(q:ℝ)) := by positivity
    linarith
  ---- admissibility of U = V = y^2/10
  have hU1 : (1:ℝ) < y^2/10 := by nlinarith
  have hUx : y^2/10 < x := by rw [← hy5]; nlinarith
  have hUV : (y^2/10) * (y^2/10) ≤ x/4 := by
    rw [← hy5]
    have he : (y^2/10) * (y^2/10) = y^4/100 := by ring
    rw [he]; linarith
  have hUV2 : x ≤ (y^2/10) * (y^2/10)^2 := by
    rw [← hy5]
    have he : (y^2/10) * (y^2/10)^2 = y^6/1000 := by ring
    rw [he]; linarith
  have h40U : (40:ℝ) ≤ y^2/10 := by nlinarith
  have hmin := hminor (y^2/10) (y^2/10) hU1 hU1 hUx hUx hUV hUV2 h40U h40U
  have hyne : y ≠ 0 := ne_of_gt hy0
  have hlogxnn : (0:ℝ) ≤ Real.log x := by rw [hlogx]; linarith
  have hlog10 : Real.log 10 ≤ 2.332 := by
    have h8 : Real.log 10 = 3 * Real.log 2 + Real.log (10/8) := by
      rw [show (10:ℝ) = 2^3 * (10/8) by norm_num, Real.log_mul (by norm_num) (by norm_num),
        Real.log_pow]
      push_cast; ring
    have h9 : Real.log (10/8 : ℝ) ≤ (10/8 : ℝ) - 1 := Real.log_le_sub_one_of_pos (by norm_num)
    rw [h8]; linarith
  have hs10 : Real.sqrt 10 ≤ 3.162278 := by
    rw [show (3.162278:ℝ) = Real.sqrt (3.162278^2) from (Real.sqrt_sq (by norm_num)).symm]
    exact Real.sqrt_le_sqrt (by norm_num)
  ---- term 1
  have hb1 : (x / (q:ℝ)) * Real.log x * (Real.log (2 * (y^2/10) * (y^2/10) / (q:ℝ) + 4) + 4)
      ≤ 2 * (x / Real.sqrt (q:ℝ)) * (Real.log y ^ 2 + Real.log y) := by
    have harg1 : 2 * (y^2/10) * (y^2/10) / (q:ℝ) + 4 = y^4/(50*(q:ℝ)) + 4 := by ring
    have hT1arg : Real.log (y^4/(50*(q:ℝ)) + 4) ≤ 4 * Real.log y := by
      have hb : y^4/(50*(q:ℝ)) + 4 ≤ y^4 := by
        have h1 : y^4/(50*(q:ℝ)) ≤ y^4/5000 := by gcongr; linarith
        linarith
      calc Real.log (y^4/(50*(q:ℝ)) + 4) ≤ Real.log (y^4) := Real.log_le_log (by positivity) hb
        _ = 4 * Real.log y := by rw [Real.log_pow]; push_cast; ring
    have hT1argnn : (0:ℝ) ≤ Real.log (y^4/(50*(q:ℝ)) + 4) := by
      apply Real.log_nonneg
      have : (0:ℝ) ≤ y^4/(50*(q:ℝ)) := by positivity
      linarith
    rw [harg1]
    calc (x/(q:ℝ)) * Real.log x * (Real.log (y^4/(50*(q:ℝ)) + 4) + 4)
        ≤ ((x / Real.sqrt (q:ℝ))/10) * (5 * Real.log y) * (4 * Real.log y + 4) :=
          mul3_le (by positivity) hlogxnn (by linarith) hAle (le_of_eq hlogx) (by linarith)
      _ = 2 * (x / Real.sqrt (q:ℝ)) * (Real.log y ^ 2 + Real.log y) := by ring
  ---- term 2
  have hb2 : 1.78 * ((y^2/10) * (y^2/10) + (5/2)*(q:ℝ)) * (8 + Real.log (q:ℝ)) * Real.log (2*x)
      ≤ 1.78 * (y^4/100 + 0.25 * (x / Real.sqrt (x/(q:ℝ)))) * (8 + 5 * Real.log y)
          * (0.694 + 5 * Real.log y) := by
    refine mul4_le (by norm_num) (by positivity) (by linarith) hlog2xnn (le_refl _) ?_
      (by linarith) hlog2x
    nlinarith [hBle]
  ---- term 3
  have hargUV : x / ((y^2/10) * (y^2/10)) = 100 * y := by
    rw [← hy5]; field_simp; ring
  have hargVU : (y^2/10) * x / (y^2/10) = x := by
    field_simp
  have hlog100y : Real.log (100 * y) ≤ 4.664 + Real.log y := by
    rw [Real.log_mul (by norm_num) (ne_of_gt hy0)]
    have h100 : Real.log 100 = 2 * Real.log 10 := by
      rw [show (100:ℝ) = 10^2 by norm_num, Real.log_pow]; push_cast; ring
    rw [h100]; linarith
  have hlog100ynn : (0:ℝ) ≤ Real.log (100 * y) := Real.log_nonneg (by linarith)
  have hb3 : (0.1 * x / Real.sqrt (q:ℝ) + 0.39 * x / Real.sqrt (x/(q:ℝ)))
        * Real.log (x / ((y^2/10) * (y^2/10))) * Real.log ((y^2/10) * x / (y^2/10))
      ≤ (0.1 * (x / Real.sqrt (q:ℝ)) + 0.39 * (x / Real.sqrt (x/(q:ℝ))))
          * (4.664 + Real.log y) * (5 * Real.log y) := by
    rw [hargUV, hargVU]
    refine mul3_le (by positivity) hlog100ynn hlogxnn ?_ hlog100y (le_of_eq hlogx)
    apply le_of_eq; ring
  ---- term 4
  have hsqU : Real.sqrt (y^2/10) = y / Real.sqrt 10 := by
    rw [show y^2/10 = (y/Real.sqrt 10)^2 by
      rw [div_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 10)]]
    exact Real.sqrt_sq (by positivity)
  have hargU : x / (y^2/10) = 10*y^3 := by rw [← hy5]; field_simp
  have hlog10y3 : Real.log (10*y^3) ≤ 2.332 + 3 * Real.log y := by
    rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]
    push_cast; linarith
  have hyp3big : (10:ℝ)^12 ≤ y^3 := by
    have h := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 10000) hy4 3
    norm_num at h ⊢; linarith
  have hlog10y3nn : (0:ℝ) ≤ Real.log (10*y^3) := Real.log_nonneg (by linarith)
  have hb4 : (0.55 * x / Real.sqrt (y^2/10) + 1.1 * x / Real.sqrt (y^2/10))
        * Real.log (x / (y^2/10))
      ≤ 5.2178 * y^4 * (2.332 + 3 * Real.log y) := by
    rw [hsqU, hargU]
    refine mul2_le ?_ hlog10y3nn ?_ hlog10y3
    · have h1 : (0:ℝ) ≤ 0.55 * x / (y/Real.sqrt 10) := by positivity
      have h2 : (0:ℝ) ≤ 1.1 * x / (y/Real.sqrt 10) := by positivity
      linarith
    · rw [← hy5]
      have hne : Real.sqrt 10 ≠ 0 := by positivity
      have e1 : 0.55*y^5/(y/Real.sqrt 10) = 0.55*Real.sqrt 10*y^4 := by field_simp
      have e2 : 1.1*y^5/(y/Real.sqrt 10) = 1.1*Real.sqrt 10*y^4 := by field_simp
      rw [e1, e2]
      have hkey : 1.65 * Real.sqrt 10 ≤ 5.2178 := by linarith
      have hmul := mul_le_mul_of_nonneg_right hkey hyp4
      linarith only [hmul]
  ---- assemble
  have hmaster := master (x / Real.sqrt (q:ℝ)) (x / Real.sqrt (x/(q:ℝ))) (y^4) (Real.log y)
    hAnn hBnn hyp4 hll
  rw [hy4x, hlogx]
  have hgoal : (0.14 * x / Real.sqrt (q:ℝ) + 0.64 * x / Real.sqrt (x/(q:ℝ)) + 0.15 * y^4)
        * (5 * Real.log y) * (5 * Real.log y + 11.3) - 0.0028 * y^4 * (5 * Real.log y / 5)
      = (0.14 * (x / Real.sqrt (q:ℝ)) + 0.64 * (x / Real.sqrt (x/(q:ℝ))) + 0.15 * y^4)
        * (5 * Real.log y) * (5 * Real.log y + 11.3) - 0.0028 * y^4 * Real.log y := by ring
  rw [hgoal]
  linarith only [hmin, hb1, hb2, hb3, hb4, hmaster]


set_option maxHeartbeats 1000000 in
theorem error_bound (x : ℝ) (hx : (10:ℝ)^20 ≤ x) :
    (Real.sqrt x + 2) * 2.7726 * Real.log x
      ≤ 0.0028 * x ^ (4/5 : ℝ) * (Real.log x / 5) := by
  have hx0 : (0:ℝ) < x := by nlinarith
  obtain ⟨y, hy0, hy5⟩ : ∃ y : ℝ, 0 < y ∧ y ^ 5 = x := by
    refine ⟨x ^ (1/5:ℝ), Real.rpow_pos_of_pos hx0 _, ?_⟩
    rw [← Real.rpow_natCast (x ^ (1/5:ℝ)) 5, ← Real.rpow_mul hx0.le]; norm_num
  have hy4x : x ^ (4/5 : ℝ) = y ^ 4 := by
    rw [← hy5, ← Real.rpow_natCast y 5, ← Real.rpow_mul hy0.le]; norm_num
  have hy4 : (10000:ℝ) ≤ y := by
    have h : ((10000:ℝ))^5 ≤ y^5 := by rw [hy5]; nlinarith
    exact le_of_pow_le_pow_left₀ (by norm_num) hy0.le h
  have hlogx : Real.log x = 5 * Real.log y := by
    rw [← hy5, Real.log_pow]; push_cast; ring
  have hll : 9 ≤ Real.log y := by
    have h2 : Real.exp 9 = (Real.exp 1)^(9:ℕ) := by rw [Real.exp_one_pow]; norm_num
    have h3 : (Real.exp 1)^(9:ℕ) ≤ (2.7182818286:ℝ)^(9:ℕ) :=
      pow_le_pow_left₀ (Real.exp_nonneg 1) Real.exp_one_lt_d9.le _
    have h4 : (2.7182818286:ℝ)^(9:ℕ) ≤ 10000 := by norm_num
    have he : Real.exp 9 ≤ y := by rw [h2]; linarith
    exact (Real.le_log_iff_exp_le hy0).mpr he
  have hyp3 : (0:ℝ) ≤ y^3 := by positivity
  have hyp5 : (0:ℝ) ≤ y^5 := by positivity
  have hbig3 : (10:ℝ)^12 ≤ y^3 := by
    have h := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 10000) hy4 3
    norm_num at h ⊢; linarith
  have hy43 : 10000 * y^3 ≤ y^4 := by
    nlinarith [mul_nonneg hyp3 (by linarith : (0:ℝ) ≤ y - 10000)]
  have h6ge : 10000 * y^5 ≤ y^6 := by
    nlinarith [mul_nonneg hyp5 (by linarith : (0:ℝ) ≤ y - 10000)]
  have hsqx : Real.sqrt x ≤ y^3 := by
    rw [← hy5]
    calc Real.sqrt (y^5) ≤ Real.sqrt ((y^3)^2) := Real.sqrt_le_sqrt (by nlinarith)
      _ = y^3 := Real.sqrt_sq (by positivity)
  have hkey : 13.863 * (Real.sqrt x + 2) ≤ 0.0028 * y^4 := by nlinarith
  rw [hy4x, hlogx]
  nlinarith [mul_le_mul_of_nonneg_right hkey (by linarith : (0:ℝ) ≤ Real.log y)]

set_option maxHeartbeats 1000000 in
theorem section6 (x α β : ℝ) (a : ℤ) (q q₀ : ℕ)
    (hx : (10 : ℝ) ^ 20 ≤ x)
    (hq : 100 ≤ q) (hqx : (q : ℝ) ≤ x / 100)
    (haq : Nat.Coprime a.natAbs q)
    (hα : 4 * α = (a : ℝ) / q + β)
    (hβ : |β| ≤ 1 / (q : ℝ) ^ 2)
    (hq₀ : ∀ p ∈ q₀.primeFactors, (p : ℝ) ≤ Real.sqrt x)
    (hminor : ∀ U V : ℝ, 1 < U → 1 < V → U < x → V < x → U * V ≤ x / 4 → x ≤ U * V ^ 2 →
        40 ≤ U → 40 ≤ V →
        ‖TaoFivePrimes.smoothedExpSum TaoFivePrimes.eta0 2 x α‖ ≤
          (x / q) * Real.log x * (Real.log (2 * U * V / q + 4) + 4)
            + 1.78 * (U * V + (5 / 2) * q) * (8 + Real.log q) * Real.log (2 * x)
          + (0.1 * x / Real.sqrt q + 0.39 * x / Real.sqrt (x / q))
              * Real.log (x / (U * V)) * Real.log (V * x / U)
          + (0.55 * x / Real.sqrt U + 1.1 * x / Real.sqrt V) * Real.log (x / U)) :
    ‖TaoFivePrimes.smoothedExpSum TaoFivePrimes.eta0 q₀ x α‖ ≤
      (0.14 * x / Real.sqrt q + 0.64 * x / Real.sqrt (x / q) + 0.15 * x ^ (4 / 5 : ℝ))
        * Real.log x * (Real.log x + 11.3) := by
  have hx1 : (1:ℝ) ≤ x := by nlinarith
  have hcore := main_core x α q hx hq hqx hminor
  have hmod := modulus_step x α hx1 q₀ hq₀
  have herr := error_bound x hx
  linarith only [hcore, hmod, herr]

end TaoS6

end PartS6H

theorem solution (x α β : ℝ) (a : ℤ) (q q₀ : ℕ)
    (hx : (10 : ℝ) ^ 20 ≤ x)
    (hq : 100 ≤ q) (hqx : (q : ℝ) ≤ x / 100)
    (haq : Nat.Coprime a.natAbs q)
    (hα : 4 * α = (a : ℝ) / q + β)
    (hβ : |β| ≤ 1 / (q : ℝ) ^ 2)
    (hq₀ : ∀ p ∈ q₀.primeFactors, (p : ℝ) ≤ Real.sqrt x)
    (hminor : ∀ U V : ℝ, 1 < U → 1 < V → U < x → V < x → U * V ≤ x / 4 → x ≤ U * V ^ 2 →
        40 ≤ U → 40 ≤ V →
        ‖TaoFivePrimes.smoothedExpSum TaoFivePrimes.eta0 2 x α‖ ≤
          (x / q) * Real.log x * (Real.log (2 * U * V / q + 4) + 4)
            + 1.78 * (U * V + (5 / 2) * q) * (8 + Real.log q) * Real.log (2 * x)
          + (0.1 * x / Real.sqrt q + 0.39 * x / Real.sqrt (x / q))
              * Real.log (x / (U * V)) * Real.log (V * x / U)
          + (0.55 * x / Real.sqrt U + 1.1 * x / Real.sqrt V) * Real.log (x / U)) :
    ‖TaoFivePrimes.smoothedExpSum TaoFivePrimes.eta0 q₀ x α‖ ≤
      (0.14 * x / Real.sqrt q + 0.64 * x / Real.sqrt (x / q) + 0.15 * x ^ (4 / 5 : ℝ))
        * Real.log x * (Real.log x + 11.3) :=
  TaoS6.section6 x α β a q q₀ hx hq hqx haq hα hβ hq₀ hminor
