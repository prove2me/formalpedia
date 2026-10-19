-- Prove2me | solution 1 for RamanujanNotebooks.entry_24_2
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T03:25:02.061996+00:00
-- url     : https://prove2.me/submissions/78f1b814-59ec-4e25-b9c9-fa2d1e0a926c

import Mathlib
import Theorems.Thm_ArtinPrimitiveRoots_siegel_walfisz
import Definitions.Def_RamanujanNotebooks_ch24_ch24PrimeCount
import Definitions.Def_RamanujanNotebooks_ch24_ch24PrimePi

namespace RPAux

noncomputable def f (L : ℝ) : ℝ := 1/L + 1/L^2 + 2/L^3 + 6/L^4 + 24/L^5

lemma main_poly (L : ℝ) (hL : 10 ≤ L) : f L ^ 2 - f (L-1) / L ≤ -1/(2*L^6) := by
  have h0 : 0 < L := by linarith
  have h1 : 0 < L - 1 := by linarith
  have key : f L ^ 2 - f (L-1) / L + 1/(2*L^6) =
      ((-1152) + 5184*L - 8904*L^2 + 6936*L^3 - 2049*L^4 + 85*L^5 - 444*L^6 + 560*L^7
        - 263*L^8 - L^9) / (2 * L^10 * (L-1)^5) := by
    unfold f; field_simp; ring
  have hP : (-1152) + 5184*L - 8904*L^2 + 6936*L^3 - 2049*L^4 + 85*L^5 - 444*L^6 + 560*L^7
        - 263*L^8 - L^9 ≤ 0 := by
    obtain ⟨s, hs, rfl⟩ : ∃ s, 0 ≤ s ∧ L = 10 + s := ⟨L - 10, by linarith, by ring⟩
    have := pow_nonneg hs 2; have := pow_nonneg hs 3; have := pow_nonneg hs 4
    have := pow_nonneg hs 5; have := pow_nonneg hs 6; have := pow_nonneg hs 7
    have := pow_nonneg hs 8; have := pow_nonneg hs 9
    ring_nf; linarith
  have : ((-1152) + 5184*L - 8904*L^2 + 6936*L^3 - 2049*L^4 + 85*L^5 - 444*L^6 + 560*L^7
        - 263*L^8 - L^9) / (2 * L^10 * (L-1)^5) ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg hP (by positivity)
  have e : -1/(2*L^6) = - (1/(2*L^6)) := by ring
  linarith

lemma f_nonneg (L : ℝ) (hL : 0 < L) : 0 ≤ f L := by unfold f; positivity

lemma f_le (L : ℝ) (hL : 10 ≤ L) : f L ≤ 2 / L := by
  have h0 : 0 < L := by linarith
  unfold f
  rw [div_add_div _ _ (by positivity) (by positivity), div_add_div _ _ (by positivity) (by positivity),
    div_add_div _ _ (by positivity) (by positivity), div_add_div _ _ (by positivity) (by positivity),
    div_le_div_iff₀ (by positivity) h0]
  obtain ⟨s, hs, rfl⟩ : ∃ s, 0 ≤ s ∧ L = 10 + s := ⟨L - 10, by linarith, by ring⟩
  have := pow_nonneg hs 2; have := pow_nonneg hs 3; have := pow_nonneg hs 4
  have := pow_nonneg hs 5; have := pow_nonneg hs 6; have := pow_nonneg hs 7
  have := pow_nonneg hs 8; have := pow_nonneg hs 9; have := pow_nonneg hs 10
  have := pow_nonneg hs 11; have := pow_nonneg hs 12; have := pow_nonneg hs 13
  have := pow_nonneg hs 14; have := pow_nonneg hs 15; have := pow_nonneg hs 16
  ring_nf; nlinarith

/-- the final algebraic step -/
lemma alg (K : ℝ) (hK : 0 ≤ K) : ∃ L0 : ℝ, ∀ L, L0 ≤ L → ∀ x : ℝ, 0 < x → ∀ a b : ℝ,
    |a - x * f L| ≤ K * x / L^6 → |b - x / Real.exp 1 * f (L-1)| ≤ K * (x / Real.exp 1) / (L-1)^6 →
    a^2 < Real.exp 1 * x / L * b := by
  refine ⟨10 + 2 * (K^2 + 68*K), fun L hL x hx a b ha hb => ?_⟩
  have hL10 : 10 ≤ L := by nlinarith
  have h0 : 0 < L := by linarith
  have he : 0 < Real.exp 1 := Real.exp_pos 1
  -- normalise
  set α := a / x with hα
  set β := b * Real.exp 1 / x with hβ
  have ha' : |α - f L| ≤ K / L^6 := by
    have : α - f L = (a - x * f L) / x := by rw [hα]; field_simp
    rw [this, abs_div, abs_of_pos hx, div_le_iff₀ hx]; calc _ ≤ K * x / L^6 := ha
      _ = _ := by ring
  have hb' : |β - f (L-1)| ≤ K / (L-1)^6 := by
    have : β - f (L-1) = (b - x / Real.exp 1 * f (L-1)) * (Real.exp 1 / x) := by
      rw [hβ]; field_simp
    rw [this, abs_mul, abs_of_pos (by positivity : 0 < Real.exp 1 / x)]
    calc _ ≤ K * (x / Real.exp 1) / (L-1)^6 * (Real.exp 1 / x) := by gcongr
      _ = _ := by field_simp
  suffices hs : α^2 < β / L by
    have e1 : a = α * x := by rw [hα]; field_simp
    have e2 : b = β * x / Real.exp 1 := by rw [hβ]; field_simp
    rw [e1, e2]
    have : Real.exp 1 * x / L * (β * x / Real.exp 1) = β / L * x^2 := by field_simp
    rw [this, mul_pow]; exact mul_lt_mul_of_pos_right hs (by positivity)
  have hM := main_poly L hL10
  have hf0 := f_nonneg L h0
  have hf2 := f_le L hL10
  obtain ⟨ha1, ha2⟩ := abs_le.mp ha'
  obtain ⟨hb1, hb2⟩ := abs_le.mp hb'
  have hL1 : L / 2 ≤ L - 1 := by linarith
  have hinv : K / (L-1)^6 ≤ 64 * K / L^6 := by
    rw [div_le_div_iff₀ (pow_pos (by linarith) 6) (by positivity)]
    have : L^6 ≤ 64 * (L-1)^6 := by
      have := pow_le_pow_left₀ (by positivity) hL1 6
      nlinarith
    nlinarith
  -- α^2 ≤ (f + ε)^2 with |ε| ≤ K/L^6
  set ε := K / L^6 with hε
  have hε0 : 0 ≤ ε := by positivity
  have hα2 : α^2 ≤ f L ^ 2 + 2 * (2 / L) * ε + ε^2 := by
    have hαabs : |α| ≤ f L + ε := by
      calc |α| = |f L + (α - f L)| := by ring_nf
        _ ≤ |f L| + |α - f L| := abs_add_le _ _
        _ ≤ f L + ε := by rw [abs_of_nonneg hf0]; linarith
    have : α^2 ≤ (f L + ε)^2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hαabs 2
    nlinarith
  have hβL : f (L-1) / L - 64 * ε / L ≤ β / L := by
    have e64 : 64 * K / L^6 = 64 * ε := by rw [hε]; ring
    rw [← sub_div]; apply div_le_div_of_nonneg_right _ h0.le; linarith
  -- ε ≤ ... and ε^2 ≤ K^2 / L^12 ≤ K^2/L^7
  have hεL : ε * L^6 = K := by rw [hε]; field_simp
  -- multiply everything by L^7
  have key : (f L ^ 2 + 2 * (2 / L) * ε + ε^2) - (f (L-1) / L - 64 * ε / L) < 0 := by
    have e : (f L ^ 2 + 2 * (2 / L) * ε + ε^2) - (f (L-1) / L - 64 * ε / L)
        = (f L ^ 2 - f (L-1) / L) + (68 * K + K^2 / L^5) / L^7 := by
      rw [hε]; field_simp; ring
    rw [e]
    have hK5 : K^2 / L^5 ≤ K^2 := div_le_self (by positivity) (one_le_pow₀ (by linarith))
    have : (68 * K + K^2 / L^5) / L^7 ≤ (68 * K + K^2) / L^7 := by gcongr
    have h2 : (68 * K + K^2) / L^7 < 1 / (2 * L^6) := by
      rw [div_lt_div_iff₀ (by positivity) (by positivity)]
      have : (68 * K + K^2) * 2 < L := by nlinarith
      have hL6 : 0 < L^6 := by positivity
      calc (68 * K + K ^ 2) * (2 * L ^ 6) = ((68 * K + K^2) * 2) * L^6 := by ring
        _ < L * L^6 := by gcongr
        _ = 1 * L^7 := by ring
    have e2 : -1/(2*L^6) = - (1/(2*L^6)) := by ring
    linarith
  linarith

end RPAux

namespace RPAux
open Real Filter

lemma hasDeriv_g (t : ℝ) (ht : 1 < t) :
    HasDerivAt (fun t => t * f (log t)) (1 / log t - 120 / (log t)^6) t := by
  have t0 : t ≠ 0 := by positivity
  have hl : 0 < log t := log_pos ht
  have h1 : HasDerivAt log t⁻¹ t := hasDerivAt_log t0
  have h2 : HasDerivAt (fun t => (log t)⁻¹) (-(t⁻¹) / (log t)^2) t := h1.inv hl.ne'
  have hf : ∀ s, 0 < s → f s = s⁻¹ + s⁻¹^2 + 2 * s⁻¹^3 + 6 * s⁻¹^4 + 24 * s⁻¹^5 := by
    intro s hs; unfold f; field_simp
  have h3 := (((h2.add (h2.pow 2)).add ((h2.pow 3).const_mul 2)).add ((h2.pow 4).const_mul 6)).add
    ((h2.pow 5).const_mul 24)
  have h4 := (hasDerivAt_id t).mul h3
  refine (h4.congr_of_eventuallyEq ?_).congr_deriv ?_
  · filter_upwards [lt_mem_nhds ht] with y hy
    rw [hf _ (log_pos hy)]; simp
  simp only [Pi.add_apply, Pi.pow_apply, Pi.mul_apply, id]; norm_num
  field_simp
  ring

lemma cont_pow (n : ℕ) (a b : ℝ) (ha : 1 < a) (hab : a ≤ b) :
    ContinuousOn (fun t => 1 / (log t)^n) (Set.uIcc a b) := by
  rw [Set.uIcc_of_le hab]
  apply ContinuousOn.div continuousOn_const
  · apply ContinuousOn.pow
    exact continuousOn_log.mono (fun t ht => by simp; linarith [ht.1])
  · intro t ht; exact pow_ne_zero _ (log_pos (by linarith [ht.1])).ne'

lemma li_eq (x : ℝ) (hx : 2 ≤ x) :
    (∫ t in (2:ℝ)..x, 1 / log t) = x * f (log x) - 2 * f (log 2) + 120 * ∫ t in (2:ℝ)..x, 1 / (log t)^6 := by
  have h1 := (cont_pow 1 2 x (by norm_num) hx).intervalIntegrable (μ := MeasureTheory.volume)
  have h6 := (cont_pow 6 2 x (by norm_num) hx).intervalIntegrable (μ := MeasureTheory.volume)
  have hd : ∀ t ∈ Set.uIcc 2 x, HasDerivAt (fun t => t * f (log t)) (1 / log t - 120 / (log t)^6) t := by
    intro t ht; rw [Set.uIcc_of_le hx] at ht; exact hasDeriv_g t (by linarith [ht.1])
  have hi : IntervalIntegrable (fun t => 1 / log t - 120 / (log t)^6) MeasureTheory.volume 2 x := by
    have := h1.sub (h6.const_mul 120); simp only [pow_one] at this
    refine this.congr ?_; intro t _; simp [div_eq_mul_inv]
  have := intervalIntegral.integral_eq_sub_of_hasDerivAt hd hi
  have e : (fun t => 1 / log t - 120 / (log t)^6) = fun t => 1 / log t - 120 * (1 / (log t)^6) := by
    ext t; ring
  rw [e, intervalIntegral.integral_sub (by simpa using h1) (h6.const_mul 120),
    intervalIntegral.integral_const_mul] at this
  linarith

lemma ev_small (c d : ℝ) (hc : 0 ≤ c) (hd : 0 ≤ d) :
    ∀ᶠ x in atTop, c + d * √x ≤ x / (log x)^6 := by
  have hb := (isLittleO_pow_log_id_atTop (n := 6)).bound (c := 1 / (64 * (c + d + 1))) (by positivity)
  have h2 := tendsto_sqrt_atTop.eventually hb
  filter_upwards [h2, eventually_ge_atTop 4] with x hx hx4
  have hy : 2 ≤ √x := by rw [show (2:ℝ) = √4 by rw [show (4:ℝ) = 2^2 by norm_num, sqrt_sq (by norm_num)]]; exact sqrt_le_sqrt hx4
  have hly : 0 < log √x := log_pos (by linarith)
  have hlx : log x = 2 * log √x := by rw [log_sqrt (by linarith)]; ring
  simp only [norm_pow, Real.norm_eq_abs, id, abs_of_pos hly, abs_of_pos (by linarith : (0:ℝ) < √x)] at hx
  have hsq : x = √x * √x := (mul_self_sqrt (by linarith)).symm
  have hL6 : (log x)^6 ≤ √x / (c + d + 1) := by
    rw [hlx, mul_pow]
    calc (2:ℝ)^6 * log √x ^ 6 ≤ 2^6 * (1 / (64 * (c + d + 1)) * √x) := by gcongr
      _ = _ := by field_simp; norm_num
  have hpos : 0 < (log x)^6 := by rw [hlx]; positivity
  calc c + d * √x ≤ (c + d + 1) * √x := by nlinarith
    _ = x / (√x / (c + d + 1)) := by
        have hs0 : 0 < √x := by linarith
        rw [div_div_eq_mul_div, eq_div_iff hs0.ne', mul_assoc, ← hsq]; ring
    _ ≤ x / (log x)^6 := by gcongr

lemma li_bound : ∃ K : ℝ, 0 ≤ K ∧ ∀ᶠ x in atTop,
    |(∫ t in (2:ℝ)..x, 1 / log t) - x * f (log x)| ≤ K * x / (log x)^6 := by
  have hf2 : 0 ≤ f (log 2) := f_nonneg _ (log_pos (by norm_num))
  have hl2 : 0 < log 2 := log_pos (by norm_num)
  refine ⟨1 + 120 * 64, by norm_num, ?_⟩
  filter_upwards [ev_small (2 * f (log 2)) (120 / (log 2)^6) (by positivity) (by positivity),
    eventually_ge_atTop 4] with x hx hx4
  have hsx : 2 ≤ √x := by rw [show (2:ℝ) = √4 by rw [show (4:ℝ) = 2^2 by norm_num, sqrt_sq (by norm_num)]]; exact sqrt_le_sqrt hx4
  have hsxx : √x ≤ x := by
    nlinarith [mul_self_sqrt (by linarith : (0:ℝ) ≤ x)]
  have hlx : 0 < log x := log_pos (by linarith)
  rw [li_eq x (by linarith)]
  have hI0 : 0 ≤ ∫ t in (2:ℝ)..x, 1 / (log t)^6 :=
    intervalIntegral.integral_nonneg (by linarith) (fun t ht => by
      have := log_pos (by linarith [ht.1] : (1:ℝ) < t); positivity)
  have hsplit := intervalIntegral.integral_add_adjacent_intervals
    ((cont_pow 6 2 √x (by norm_num) hsx).intervalIntegrable (μ := MeasureTheory.volume)) ((cont_pow 6 √x x (by linarith) hsxx).intervalIntegrable (μ := MeasureTheory.volume))
  have hA : (∫ t in (2:ℝ)..√x, 1 / (log t)^6) ≤ ∫ t in (2:ℝ)..√x, 1 / (log 2)^6 := by
    apply intervalIntegral.integral_mono_on hsx ((cont_pow 6 2 √x (by norm_num) hsx).intervalIntegrable (μ := MeasureTheory.volume))
      intervalIntegrable_const
    intro t ht
    have := log_le_log (by norm_num) ht.1
    gcongr
  have hB : (∫ t in √x..x, 1 / (log t)^6) ≤ ∫ t in √x..x, 64 / (log x)^6 := by
    apply intervalIntegral.integral_mono_on hsxx ((cont_pow 6 √x x (by linarith) hsxx).intervalIntegrable (μ := MeasureTheory.volume))
      intervalIntegrable_const
    intro t ht
    have h1 : log x / 2 ≤ log t := by
      rw [← log_sqrt (by linarith)]; exact log_le_log (by linarith) ht.1
    have h2 : 0 < log x / 2 := by positivity
    rw [div_le_div_iff₀ (pow_pos (by linarith) 6) (by positivity)]
    have := pow_le_pow_left₀ h2.le h1 6
    nlinarith
  rw [intervalIntegral.integral_const, smul_eq_mul] at hA hB
  have hB' : (x - √x) * (64 / (log x)^6) ≤ 64 * x / (log x)^6 := by
    rw [show (x - √x) * (64 / (log x)^6) = 64 * (x - √x) / (log x)^6 by ring]
    apply div_le_div_of_nonneg_right _ (by positivity); nlinarith [sqrt_nonneg x]
  have hA' : (√x - 2) * (1 / (log 2)^6) ≤ √x * (1 / (log 2)^6) := by gcongr; linarith
  rw [abs_le]; constructor
  · have : 0 ≤ x / (log x)^6 := by positivity
    have h120 : 0 ≤ 120 / (log 2)^6 * √x := by positivity
    have e : (1 + 120 * 64) * x / (log x)^6 = x / (log x)^6 + 7680 * (x / (log x)^6) := by ring
    rw [e]; nlinarith
  · have e : (1 + 120 * 64) * x / (log x)^6 = x / (log x)^6 + 120 * (64 * x / (log x)^6) := by ring
    rw [e]
    have : 120 / (log 2)^6 * √x = 120 * (√x * (1 / (log 2)^6)) := by ring
    nlinarith

end RPAux

namespace RPAux
open Real Filter

lemma pi_eq (Y : ℝ) : (ArtinPrimitiveRoots.primeCountingAP Y 1 0 : ℝ) = RamanujanNotebooks.ch24PrimePi Y := by
  unfold ArtinPrimitiveRoots.primeCountingAP RamanujanNotebooks.ch24PrimePi RamanujanNotebooks.ch24PrimeCount
  congr 2
  apply Finset.filter_congr
  intro p _; simp [Nat.modEq_one]

lemma pi_bound : ∃ K : ℝ, 0 ≤ K ∧ ∀ᶠ Y in atTop,
    |(RamanujanNotebooks.ch24PrimePi Y : ℝ) - Y * f (log Y)| ≤ K * Y / (log Y)^6 := by
  obtain ⟨C, hC⟩ := ArtinPrimitiveRoots.siegel_walfisz 6 1 (by norm_num) (by norm_num)
  obtain ⟨K, hK0, hK⟩ := li_bound
  refine ⟨|C| + K, by positivity, ?_⟩
  filter_upwards [hK, eventually_ge_atTop (exp 1), eventually_ge_atTop 3] with Y hY hYe hY3
  have hl1 : 1 ≤ log Y := by rw [← log_exp 1]; exact log_le_log (exp_pos 1) hYe
  have h := hC Y (by linarith) 1 le_rfl (by rw [rpow_one]; simpa using hl1) 0 (by simp)
  rw [pi_eq] at h
  simp only [Nat.totient_one, Nat.cast_one, div_one] at h
  have hr : log Y ^ (-6:ℝ) = 1 / (log Y)^6 := by
    rw [show (-6:ℝ) = -((6:ℕ):ℝ) by norm_num, rpow_neg (by linarith), rpow_natCast, one_div]
  rw [hr] at h
  have hC' : C * (Y * (1 / log Y ^ 6)) ≤ |C| * Y / (log Y)^6 := by
    rw [show |C| * Y / (log Y)^6 = |C| * (Y * (1 / log Y ^ 6)) by ring]
    exact mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity)
  unfold ArtinPrimitiveRoots.logIntegral at h
  calc _ ≤ |(RamanujanNotebooks.ch24PrimePi Y : ℝ) - ∫ t in (2:ℝ)..Y, 1 / log t|
        + |(∫ t in (2:ℝ)..Y, 1 / log t) - Y * f (log Y)| := abs_sub_le _ _ _
    _ ≤ |C| * Y / (log Y)^6 + K * Y / (log Y)^6 := add_le_add (h.trans hC') hY
    _ = _ := by ring

end RPAux

open Real Filter RPAux RamanujanNotebooks

theorem solution :
    ∃ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x →
      (ch24PrimePi x : ℝ) ^ 2 < Real.exp 1 * x / Real.log x * (ch24PrimePi (x / Real.exp 1) : ℝ) := by
  obtain ⟨K, hK0, hK⟩ := pi_bound
  obtain ⟨L0, hL0⟩ := alg K hK0
  have h2 := (tendsto_id.atTop_div_const (exp_pos 1)).eventually hK
  have h3 := tendsto_log_atTop.eventually (eventually_ge_atTop L0)
  have hev : ∀ᶠ x in atTop, (ch24PrimePi x : ℝ) ^ 2 <
      Real.exp 1 * x / Real.log x * (ch24PrimePi (x / Real.exp 1) : ℝ) := by
    filter_upwards [hK, h2, h3, eventually_gt_atTop 0] with x hx hx2 hx3 hx0
    have hl : log (id x / exp 1) = log x - 1 := by
      simp only [id]; rw [log_div hx0.ne' (exp_pos 1).ne', log_exp]
    simp only [hl] at hx2
    exact hL0 (log x) hx3 x hx0 _ _ hx (by simpa using hx2)
  obtain ⟨x0, hx0⟩ := eventually_atTop.mp hev
  exact ⟨x0, hx0⟩


