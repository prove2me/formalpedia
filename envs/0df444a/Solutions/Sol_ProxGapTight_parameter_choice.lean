-- Prove2me | solution 1 for ProxGapTight.parameter_choice
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T05:23:08.519937+00:00
-- url     : https://prove2.me/submissions/e2adfd87-31f1-461e-b96f-3fbe632d71a8

import Mathlib
import Definitions.Def_ProxGapTight_J32
import Definitions.Def_ProxGapTight_Gam
import Definitions.Def_ProxGapTight_Phi
import Definitions.Def_ProxGapTight_nm
import Definitions.Def_ProxGapTight_em
import Definitions.Def_ProxGapTight_Lm

section
set_option autoImplicit false

namespace ProxGapTight

theorem chk_thresholds_ordered (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    J32 δ < Gam δ ∧ Gam δ < δ := by
  have ha0 : 0 < 1 - δ := by linarith
  have ha1 : 1 - δ < 1 := by linarith
  constructor
  · unfold J32 Gam
    have := Real.rpow_lt_rpow_of_exponent_gt ha0 ha1 (show (1:ℝ)/3 < 4/9 by norm_num)
    linarith
  · unfold Gam
    have := Real.rpow_lt_rpow_of_exponent_gt ha0 ha1 (show (4:ℝ)/9 < 1 by norm_num)
    rw [Real.rpow_one] at this
    linarith

end ProxGapTight
end

section
set_option autoImplicit false

open Filter Topology

namespace ProxGapTight.Dev.ParamChoice

/-- `y⁻¹ log (1 - k y) → -k` as `y → 0+`. -/
lemma slope_lim (k : ℝ) :
    Tendsto (fun y : ℝ => y⁻¹ * Real.log (1 - k * y)) (𝓝[>] 0) (𝓝 (-k)) := by
  have h1 : HasDerivAt (fun y : ℝ => 1 - k * y) (-k) 0 := by
    have := ((hasDerivAt_id (0:ℝ)).const_mul k).const_sub 1
    simpa using this
  have h2 : HasDerivAt (fun y : ℝ => Real.log (1 - k * y)) (-k / (1 - k * 0)) 0 :=
    h1.log (by simp)
  have h3 := h2.tendsto_slope_zero_right
  simpa using h3

lemma log_ratio (x : ℝ) :
    Tendsto (fun y : ℝ => Real.log (1 - x * y) / Real.log (1 - 3 * y)) (𝓝[>] 0) (𝓝 (x / 3)) := by
  have h := (slope_lim x).div (slope_lim 3) (by norm_num)
  have h' : Tendsto (fun y : ℝ => Real.log (1 - x * y) / Real.log (1 - 3 * y)) (𝓝[>] 0)
      (𝓝 (-x / -3)) := by
    refine h.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with y hy
    have : y ≠ 0 := ne_of_gt hy
    simp only [Pi.div_apply]
    rw [mul_div_mul_left _ _ (inv_ne_zero this)]
  simpa [neg_div_neg_eq] using h'

noncomputable def sQ (Q : ℕ) : ℝ := ((Q : ℝ) ^ 2)⁻¹

lemma sQ_tendsto : Tendsto sQ atTop (𝓝[>] 0) := by
  rw [tendsto_nhdsWithin_iff]
  refine ⟨?_, ?_⟩
  · unfold sQ
    exact tendsto_inv_atTop_zero.comp
      ((tendsto_pow_atTop (two_ne_zero)).comp tendsto_natCast_atTop_atTop)
  · filter_upwards [eventually_gt_atTop 0] with Q h
    simp only [Set.mem_Ioi, sQ]
    have : (0:ℝ) < Q := by exact_mod_cast h
    positivity

noncomputable def tQ (b : ℝ) (Q : ℕ) : ℕ := ⌈Real.log b / Real.log (1 - 3 * sQ Q)⌉₊

lemma pow_tendsto (b x : ℝ) (hb0 : 0 < b) (hb1 : b < 1) :
    Tendsto (fun Q : ℕ => (1 - x * sQ Q) ^ tQ b Q) atTop (𝓝 (b ^ (x / 3))) := by
  have hs := sQ_tendsto
  have hs0 : Tendsto sQ atTop (𝓝 0) := hs.mono_right nhdsWithin_le_nhds
  have hr : Tendsto (fun Q => Real.log (1 - x * sQ Q) / Real.log (1 - 3 * sQ Q)) atTop
      (𝓝 (x / 3)) := (log_ratio x).comp hs
  have hg : Tendsto (fun Q => Real.log (1 - x * sQ Q)) atTop (𝓝 0) := by
    have : Tendsto (fun Q => 1 - x * sQ Q) atTop (𝓝 1) := by
      simpa using (hs0.const_mul x).const_sub 1
    simpa using this.log (by norm_num)
  -- eventually s is small
  have hsmall : ∀ᶠ Q in atTop, sQ Q < 1 / (3 * (|x| + 1)) := by
    exact hs0.eventually (gt_mem_nhds (by positivity))
  have hpos : ∀ᶠ Q in atTop, 0 < sQ Q := by
    filter_upwards [hs.eventually (eventually_mem_nhdsWithin)] with Q hQ using hQ
  have hlogb : Real.log b < 0 := Real.log_neg hb0 hb1
  -- main product
  have hmain : Tendsto (fun Q => (tQ b Q : ℝ) * Real.log (1 - x * sQ Q)) atTop
      (𝓝 (Real.log b * (x / 3))) := by
    have h1 : Tendsto (fun Q => Real.log b * (Real.log (1 - x * sQ Q) / Real.log (1 - 3 * sQ Q)))
        atTop (𝓝 (Real.log b * (x / 3))) := hr.const_mul _
    have h2 : Tendsto (fun Q => ((tQ b Q : ℝ) - Real.log b / Real.log (1 - 3 * sQ Q)) *
        Real.log (1 - x * sQ Q)) atTop (𝓝 0) := by
      refine squeeze_zero_norm' ?_ (by simpa using hg.norm)
      filter_upwards [hpos, hsmall] with Q hQ hQ2
      have hQ3 : 3 * sQ Q < 1 := by
        have : 3 * sQ Q < 3 * (1 / (3 * (|x| + 1))) := by linarith
        have h4 : 3 * (1 / (3 * (|x| + 1))) ≤ 1 := by
          rw [mul_one_div, div_le_one (by positivity)]
          nlinarith [abs_nonneg x]
        linarith
      have hh : Real.log (1 - 3 * sQ Q) < 0 := Real.log_neg (by linarith) (by linarith)
      have hr0 : 0 ≤ Real.log b / Real.log (1 - 3 * sQ Q) := div_nonneg_of_nonpos hlogb.le hh.le
      have hc1 := Nat.le_ceil (Real.log b / Real.log (1 - 3 * sQ Q))
      have hc2 := Nat.ceil_lt_add_one hr0
      have hd : ‖(tQ b Q : ℝ) - Real.log b / Real.log (1 - 3 * sQ Q)‖ ≤ 1 := by
        rw [Real.norm_eq_abs, abs_le]
        unfold tQ
        constructor <;> linarith
      rw [norm_mul]
      calc _ ≤ 1 * ‖Real.log (1 - x * sQ Q)‖ :=
            mul_le_mul_of_nonneg_right hd (norm_nonneg _)
        _ = _ := one_mul _
    have h3 := h1.add h2
    refine (by simpa using h3 : Tendsto _ atTop _).congr' ?_
    filter_upwards [hpos, hsmall] with Q hQ hQ2
    have hQ3 : 3 * sQ Q < 1 := by
      have : 3 * sQ Q < 3 * (1 / (3 * (|x| + 1))) := by linarith
      have h4 : 3 * (1 / (3 * (|x| + 1))) ≤ 1 := by
        rw [mul_one_div, div_le_one (by positivity)]
        nlinarith [abs_nonneg x]
      linarith
    have hh : Real.log (1 - 3 * sQ Q) < 0 := Real.log_neg (by linarith) (by linarith)
    field_simp
    ring
  have hexp := (Real.continuous_exp.tendsto _).comp hmain
  rw [← Real.rpow_def_of_pos hb0] at hexp
  refine hexp.congr' ?_
  filter_upwards [hpos, hsmall] with Q hQ hQ2
  have hxs : 0 < 1 - x * sQ Q := by
    have : |x| * sQ Q < 1 / 3 := by
      calc |x| * sQ Q ≤ (|x| + 1) * sQ Q := by nlinarith
        _ < (|x| + 1) * (1 / (3 * (|x| + 1))) := by
          apply mul_lt_mul_of_pos_left hQ2 (by positivity)
        _ = 1 / 3 := by field_simp
    have := neg_abs_le x
    nlinarith [abs_nonneg x, le_abs_self x]
  simp only [Function.comp]
  rw [← Real.rpow_natCast, Real.rpow_def_of_pos hxs, mul_comm]


/-! ### Limits in `m` -/

lemma nm_cast (Q k : ℕ) (hQ : 2 ≤ Q) :
    (nm Q (k + 4) : ℝ) * ((Q : ℝ) - 1) = (Q : ℝ) ^ (k + 4) - 1 := by
  have hd : Q - 1 ∣ Q ^ (k + 4) - 1 := by
    exact Nat.sub_one_dvd_pow_sub_one Q (k + 4)
  have h1 : 1 ≤ Q ^ (k + 4) := Nat.one_le_pow _ _ (by omega)
  have : (nm Q (k + 4)) * (Q - 1) = Q ^ (k + 4) - 1 := Nat.div_mul_cancel hd
  have h2 : ((nm Q (k + 4) * (Q - 1) : ℕ) : ℝ) = ((Q ^ (k + 4) - 1 : ℕ) : ℝ) := by rw [this]
  rw [Nat.cast_mul, Nat.cast_sub (by omega), Nat.cast_sub h1] at h2
  simpa using h2

lemma em_cast (Q k : ℕ) (hQ : 2 ≤ Q) :
    (em Q (k + 4) : ℝ) * ((Q : ℝ) - 1) = (Q : ℝ) ^ (k + 2) - 1 := by
  have hd : Q - 1 ∣ Q ^ (k + 2) - 1 := by
    exact Nat.sub_one_dvd_pow_sub_one Q (k + 2)
  have h1 : 1 ≤ Q ^ (k + 2) := Nat.one_le_pow _ _ (by omega)
  have : (em Q (k + 4)) * (Q - 1) = Q ^ (k + 2) - 1 := by
    have := Nat.div_mul_cancel hd
    simpa [em] using this
  have h2 : ((em Q (k + 4) * (Q - 1) : ℕ) : ℝ) = ((Q ^ (k + 2) - 1 : ℕ) : ℝ) := by rw [this]
  rw [Nat.cast_mul, Nat.cast_sub (by omega), Nat.cast_sub h1] at h2
  simpa using h2

lemma Lm_cast (Q k : ℕ) (hQ : 2 ≤ Q) :
    (Lm Q (k + 4) : ℝ) = 3 * (Q : ℝ) ^ (k + 1) - 3 * (Q : ℝ) ^ k - 1 := by
  have e1 : k + 4 - 3 = k + 1 := by omega
  have e2 : k + 4 - 4 = k := by omega
  have hk : 1 ≤ Q ^ k := Nat.one_le_pow _ _ (by omega)
  have hle : 3 * Q ^ k + 3 ≤ 3 * Q ^ (k + 1) := by
    have : Q ^ (k + 1) = Q ^ k * Q := pow_succ _ _
    nlinarith
  unfold Lm
  rw [e1, e2, Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
  push_cast
  ring

lemma ratios (Q k : ℕ) (hQ : 2 ≤ Q) :
    (em Q (k + 4) : ℝ) / (nm Q (k + 4) : ℝ) =
      ((Q : ℝ) ^ 2 - ((Q : ℝ)⁻¹) ^ k) / ((Q : ℝ) ^ 4 - ((Q : ℝ)⁻¹) ^ k) ∧
    (Lm Q (k + 4) : ℝ) / (nm Q (k + 4) : ℝ) =
      ((3 * (Q : ℝ) - 3 - ((Q : ℝ)⁻¹) ^ k) * ((Q : ℝ) - 1)) /
        ((Q : ℝ) ^ 4 - ((Q : ℝ)⁻¹) ^ k) := by
  have hQ0 : (0 : ℝ) < Q := by exact_mod_cast (by omega : 0 < Q)
  have hQ1 : (1 : ℝ) < Q := by exact_mod_cast (by omega : 1 < Q)
  have hn := nm_cast Q k hQ
  have he := em_cast Q k hQ
  have hL := Lm_cast Q k hQ
  have hw : (Q : ℝ) ^ k * ((Q : ℝ)⁻¹) ^ k = 1 := by
    rw [← mul_pow, mul_inv_cancel₀ hQ0.ne', one_pow]
  have hk : (Q : ℝ) ^ k ≠ 0 := by positivity
  have hD : (Q : ℝ) ^ (k + 4) - 1 = (Q : ℝ) ^ k * ((Q : ℝ) ^ 4 - ((Q : ℝ)⁻¹) ^ k) := by
    rw [mul_sub, pow_add]; nlinarith [hw]
  have hE : (Q : ℝ) ^ (k + 2) - 1 = (Q : ℝ) ^ k * ((Q : ℝ) ^ 2 - ((Q : ℝ)⁻¹) ^ k) := by
    rw [mul_sub, pow_add]; nlinarith [hw]
  have hDpos : 0 < (Q : ℝ) ^ 4 - ((Q : ℝ)⁻¹) ^ k := by
    have h1 : ((Q : ℝ)⁻¹) ^ k ≤ 1 := pow_le_one₀ (by positivity) (inv_le_one_of_one_le₀ hQ1.le)
    have h2 : (1 : ℝ) < (Q : ℝ) ^ 4 := one_lt_pow₀ hQ1 (by norm_num)
    linarith
  have hnpos : (nm Q (k + 4) : ℝ) ≠ 0 := by
    intro h
    rw [h, zero_mul] at hn
    rw [hD] at hn
    have := mul_pos (pow_pos hQ0 k) hDpos
    linarith
  have hQm : (Q : ℝ) - 1 ≠ 0 := by linarith
  constructor
  · rw [div_eq_div_iff hnpos hDpos.ne']
    have : (em Q (k + 4) : ℝ) * ((Q : ℝ) ^ k * ((Q : ℝ) ^ 4 - ((Q : ℝ)⁻¹) ^ k)) =
        (nm Q (k + 4) : ℝ) * ((Q : ℝ) ^ k * ((Q : ℝ) ^ 2 - ((Q : ℝ)⁻¹) ^ k)) := by
      apply mul_right_cancel₀ hQm
      calc _ = (em Q (k + 4) : ℝ) * ((Q : ℝ) - 1) * ((Q : ℝ) ^ k * ((Q : ℝ) ^ 4 - ((Q : ℝ)⁻¹) ^ k)) := by ring
        _ = (nm Q (k + 4) : ℝ) * ((Q : ℝ) - 1) * ((Q : ℝ) ^ k * ((Q : ℝ) ^ 2 - ((Q : ℝ)⁻¹) ^ k)) := by
          rw [he, hn, hD, hE]; ring
        _ = _ := by ring
    have := mul_left_cancel₀ hk (by linarith : (Q : ℝ) ^ k * ((em Q (k + 4) : ℝ) * ((Q : ℝ) ^ 4 - ((Q : ℝ)⁻¹) ^ k)) = (Q : ℝ) ^ k * ((nm Q (k + 4) : ℝ) * ((Q : ℝ) ^ 2 - ((Q : ℝ)⁻¹) ^ k)))
    linarith
  · rw [div_eq_div_iff hnpos hDpos.ne']
    have hLk : (Lm Q (k + 4) : ℝ) = (Q : ℝ) ^ k * (3 * (Q : ℝ) - 3 - ((Q : ℝ)⁻¹) ^ k) := by
      rw [hL, pow_succ]; nlinarith [hw]
    apply mul_right_cancel₀ hQm
    apply mul_left_cancel₀ hk
    calc (Q : ℝ) ^ k * ((Lm Q (k + 4) : ℝ) * ((Q : ℝ) ^ 4 - ((Q : ℝ)⁻¹) ^ k) * ((Q : ℝ) - 1))
        = (Lm Q (k + 4) : ℝ) * (Q : ℝ) ^ k * ((Q : ℝ) ^ 4 - ((Q : ℝ)⁻¹) ^ k) * ((Q : ℝ) - 1) := by ring
      _ = (Lm Q (k + 4) : ℝ) * ((Q : ℝ) ^ (k + 4) - 1) * ((Q : ℝ) - 1) := by rw [hD]; ring
      _ = (Lm Q (k + 4) : ℝ) * ((nm Q (k + 4) : ℝ) * ((Q : ℝ) - 1)) * ((Q : ℝ) - 1) := by rw [hn]
      _ = _ := by rw [hLk]; ring

lemma em_nm_tendsto (Q : ℕ) (hQ : 2 ≤ Q) :
    Tendsto (fun m : ℕ => (em Q m : ℝ) / (nm Q m : ℝ)) atTop (𝓝 (sQ Q)) := by
  have hQ0 : (0 : ℝ) < Q := by exact_mod_cast (by omega : 0 < Q)
  have hQ1 : (1 : ℝ) < Q := by exact_mod_cast (by omega : 1 < Q)
  rw [← tendsto_add_atTop_iff_nat 4]
  have hw : Tendsto (fun k : ℕ => ((Q : ℝ)⁻¹) ^ k) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity) (inv_lt_one_of_one_lt₀ hQ1)
  have h : Tendsto (fun k : ℕ => ((Q : ℝ) ^ 2 - ((Q : ℝ)⁻¹) ^ k) / ((Q : ℝ) ^ 4 - ((Q : ℝ)⁻¹) ^ k))
      atTop (𝓝 (((Q : ℝ) ^ 2 - 0) / ((Q : ℝ) ^ 4 - 0))) :=
    (tendsto_const_nhds.sub hw).div (tendsto_const_nhds.sub hw) (by simp; positivity)
  have e : ((Q : ℝ) ^ 2 - 0) / ((Q : ℝ) ^ 4 - 0) = sQ Q := by
    unfold sQ; field_simp; ring
  rw [e] at h
  refine h.congr fun k => ?_
  exact (ratios Q k hQ).1.symm

lemma Lm_nm_tendsto (Q : ℕ) (hQ : 2 ≤ Q) :
    Tendsto (fun m : ℕ => (Lm Q m : ℝ) / (nm Q m : ℝ)) atTop
      (𝓝 (3 * sQ Q * (1 - (Q : ℝ)⁻¹) ^ 2)) := by
  have hQ0 : (0 : ℝ) < Q := by exact_mod_cast (by omega : 0 < Q)
  have hQ1 : (1 : ℝ) < Q := by exact_mod_cast (by omega : 1 < Q)
  rw [← tendsto_add_atTop_iff_nat 4]
  have hw : Tendsto (fun k : ℕ => ((Q : ℝ)⁻¹) ^ k) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity) (inv_lt_one_of_one_lt₀ hQ1)
  have h : Tendsto (fun k : ℕ => ((3 * (Q : ℝ) - 3 - ((Q : ℝ)⁻¹) ^ k) * ((Q : ℝ) - 1)) /
      ((Q : ℝ) ^ 4 - ((Q : ℝ)⁻¹) ^ k)) atTop
      (𝓝 (((3 * (Q : ℝ) - 3 - 0) * ((Q : ℝ) - 1)) / ((Q : ℝ) ^ 4 - 0))) :=
    (((tendsto_const_nhds.sub hw)).mul_const _).div (tendsto_const_nhds.sub hw)
      (by simp; positivity)
  have e : ((3 * (Q : ℝ) - 3 - 0) * ((Q : ℝ) - 1)) / ((Q : ℝ) ^ 4 - 0) =
      3 * sQ Q * (1 - (Q : ℝ)⁻¹) ^ 2 := by
    unfold sQ; field_simp; ring
  rw [e] at h
  refine h.congr fun k => ?_
  exact (ratios Q k hQ).2.symm


lemma cube_root (x : ℝ) (hx : 0 ≤ x) : (x ^ ((1 : ℝ) / 3)) ^ 3 = x := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hx]; norm_num

end ProxGapTight.Dev.ParamChoice

namespace ProxGapTight

open ProxGapTight.Dev.ParamChoice

set_option maxHeartbeats 1000000 in
theorem chk_parameter_choice (δ ρ η : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1) (hJ : J32 δ < ρ)
    (hΓ : ρ < Gam δ) (hη : 0 < η) :
    ∃ Q₀ : ℕ, ∀ Q : ℕ, Q₀ ≤ Q → ∃ t : ℕ, 1 ≤ t ∧ ∃ ξ : ℝ, 0 < ξ ∧ ∃ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m →
      Phi t ((em Q m : ℝ) / (nm Q m : ℝ)) + 3 * ξ < ρ ∧
      Gam δ < Phi t (4 * (em Q m : ℝ) / (3 * (nm Q m : ℝ))) - 3 * ξ ∧
      ∀ u ∈ Set.Icc ((Lm Q m : ℝ) / (nm Q m : ℝ)) (3 * (em Q m : ℝ) / (nm Q m : ℝ)),
        |Phi t u - δ| < min η ((δ - Gam δ) / 4) / 2 := by
  obtain ⟨hord1, hord2⟩ := chk_thresholds_ordered δ hδ0 hδ1
  set a : ℝ := 1 - δ with ha
  have ha0 : 0 < a := by rw [ha]; linarith
  have ha1 : a < 1 := by rw [ha]; linarith
  set c : ℝ := 1 - ρ with hc
  have hg : 1 - Gam δ = a ^ ((4 : ℝ) / 9) := by unfold Gam; ring
  have hj : 1 - J32 δ = a ^ ((1 : ℝ) / 3) := by unfold J32; ring
  have hc0 : 0 < c := by rw [hc]; linarith
  have hca : c < a ^ ((1 : ℝ) / 3) := by rw [hc]; linarith
  have hc3 : c ^ 3 < a := by
    calc c ^ 3 < (a ^ ((1 : ℝ) / 3)) ^ 3 := pow_lt_pow_left₀ hca hc0.le (by norm_num)
      _ = a := cube_root a ha0.le
  set E : ℝ := min η ((δ - Gam δ) / 4) / 2 with hE
  have hE0 : 0 < E := by
    rw [hE]; have : 0 < (δ - Gam δ) / 4 := by linarith
    have := lt_min hη this
    linarith
  -- the target value b
  set b : ℝ := (a + max (c ^ 3) (a - E)) / 2 with hb
  have hmax : max (c ^ 3) (a - E) < a := max_lt hc3 (by linarith)
  have hb0 : 0 < b := by
    have := le_max_left (c ^ 3) (a - E)
    have : 0 < c ^ 3 := by positivity
    rw [hb]; linarith
  have hba : b < a := by rw [hb]; linarith
  have hb1 : b < 1 := by linarith
  have hbc : c ^ 3 < b := by
    have := le_max_left (c ^ 3) (a - E); rw [hb]; linarith
  have hbE : a - E < b := by
    have := le_max_right (c ^ 3) (a - E); rw [hb]; linarith
  have hb13 : c < b ^ ((1 : ℝ) / 3) := by
    by_contra hcon
    push_neg at hcon
    have := pow_le_pow_left₀ (Real.rpow_nonneg hb0.le _) hcon 3
    rw [cube_root b hb0.le] at this
    linarith
  -- the exponent p
  have hlogb : Real.log b < 0 := Real.log_neg hb0 hb1
  have hloga : Real.log a < 0 := Real.log_neg ha0 ha1
  have hlab : Real.log b < Real.log a := Real.log_lt_log hb0 hba
  set r : ℝ := Real.log a / Real.log b with hr
  have hr0 : 0 < r := div_pos_of_neg_of_neg hloga hlogb
  have hr1 : r < 1 := (div_lt_one_of_neg hlogb).2 hlab
  set p : ℝ := (1 + r) / 2 with hp
  have hp0 : 0 < p := by rw [hp]; linarith
  have hp1 : p < 1 := by rw [hp]; linarith
  have hrp : r < p := by rw [hp]; linarith
  have hbp : b ^ p < a := by
    have h1 : b ^ p < b ^ r := Real.rpow_lt_rpow_of_exponent_gt hb0 hb1 hrp
    have h2 : b ^ r = a := by
      rw [Real.rpow_def_of_pos hb0, hr]
      rw [mul_div_cancel₀ _ hlogb.ne, Real.exp_log ha0]
    linarith
  -- limits in Q
  have T1 := pow_tendsto b 1 hb0 hb1
  have T2 := pow_tendsto b (4 / 3) hb0 hb1
  have T3 := pow_tendsto b 3 hb0 hb1
  have T4 := pow_tendsto b (3 * p) hb0 hb1
  have e1 : b ^ ((1 : ℝ) / 3) = b ^ ((1 : ℝ) / 3) := rfl
  have e2 : (4 / 3 : ℝ) / 3 = 4 / 9 := by norm_num
  have e3 : b ^ ((3 : ℝ) / 3) = b := by norm_num
  have e4 : (3 * p) / 3 = p := by ring
  rw [e2] at T2
  rw [e3] at T3
  rw [e4] at T4
  have EA : ∀ᶠ Q : ℕ in atTop, c < (1 - 1 * sQ Q) ^ tQ b Q :=
    T1.eventually (lt_mem_nhds hb13)
  have EB : ∀ᶠ Q : ℕ in atTop, (1 - 4 / 3 * sQ Q) ^ tQ b Q < a ^ ((4 : ℝ) / 9) :=
    T2.eventually (gt_mem_nhds (Real.rpow_lt_rpow hb0.le hba (by norm_num)))
  have EC : ∀ᶠ Q : ℕ in atTop, a - E < (1 - 3 * sQ Q) ^ tQ b Q :=
    T3.eventually (lt_mem_nhds hbE)
  have ED : ∀ᶠ Q : ℕ in atTop, (1 - 3 * p * sQ Q) ^ tQ b Q < a :=
    T4.eventually (gt_mem_nhds hbp)
  have hinv : Tendsto (fun Q : ℕ => (1 - ((Q : ℝ)⁻¹)) ^ 2) atTop (𝓝 1) := by
    have : Tendsto (fun Q : ℕ => ((Q : ℝ)⁻¹)) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
    simpa using ((tendsto_const_nhds (x := (1 : ℝ))).sub this).pow 2
  have EE : ∀ᶠ Q : ℕ in atTop, p < (1 - ((Q : ℝ)⁻¹)) ^ 2 :=
    hinv.eventually (lt_mem_nhds hp1)
  have EF : ∀ᶠ Q : ℕ in atTop, 2 ≤ Q := eventually_ge_atTop 2
  obtain ⟨Q₀, hQ₀⟩ := eventually_atTop.1 (EA.and (EB.and (EC.and (ED.and (EE.and EF)))))
  refine ⟨Q₀, fun Q hQ => ?_⟩
  obtain ⟨hA, hB, hC, hD, hEE, hF⟩ := hQ₀ Q hQ
  set s : ℝ := sQ Q with hs
  set t : ℕ := tQ b Q with ht
  have hQ0 : (0 : ℝ) < Q := by exact_mod_cast (by omega : 0 < Q)
  have hQ4 : (4 : ℝ) ≤ (Q : ℝ) ^ 2 := by
    have : (2 : ℝ) ≤ Q := by exact_mod_cast hF
    nlinarith
  have hs0 : 0 < s := by rw [hs]; unfold sQ; positivity
  have hs4 : s ≤ 1 / 4 := by
    rw [hs]; unfold sQ
    rw [inv_eq_one_div]; exact one_div_le_one_div_of_le (by norm_num) hQ4
  have ht1 : 1 ≤ t := by
    have : 0 < Real.log b / Real.log (1 - 3 * s) :=
      div_pos_of_neg_of_neg hlogb (Real.log_neg (by linarith) (by linarith))
    exact Nat.ceil_pos.2 this
  -- slack
  set ξ : ℝ := min (((1 - 1 * s) ^ t - c) / 6) ((a ^ ((4 : ℝ) / 9) - (1 - 4 / 3 * s) ^ t) / 6)
    with hξ
  have hξ0 : 0 < ξ := by
    have h1 : 0 < ((1 - 1 * s) ^ t - c) / 6 := by linarith
    have h2 : 0 < (a ^ ((4 : ℝ) / 9) - (1 - 4 / 3 * s) ^ t) / 6 := by linarith
    exact lt_min h1 h2
  have hξ1 : ξ ≤ ((1 - 1 * s) ^ t - c) / 6 := min_le_left _ _
  have hξ2 : ξ ≤ (a ^ ((4 : ℝ) / 9) - (1 - 4 / 3 * s) ^ t) / 6 := min_le_right _ _
  refine ⟨t, ht1, ξ, hξ0, ?_⟩
  -- limits in m
  have hee := em_nm_tendsto Q hF
  have hLL := Lm_nm_tendsto Q hF
  have P1 : Tendsto (fun m : ℕ => (1 - (em Q m : ℝ) / (nm Q m : ℝ)) ^ t) atTop
      (𝓝 ((1 - s) ^ t)) := ((tendsto_const_nhds (x := (1 : ℝ))).sub hee).pow t
  have P2 : Tendsto (fun m : ℕ => (1 - 4 * (em Q m : ℝ) / (3 * (nm Q m : ℝ))) ^ t) atTop
      (𝓝 ((1 - 4 / 3 * s) ^ t)) := by
    have := ((tendsto_const_nhds (x := (1 : ℝ))).sub (hee.const_mul (4 / 3 : ℝ))).pow t
    refine this.congr fun m => ?_
    by_cases hn : (nm Q m : ℝ) = 0
    · simp [hn]
    · congr 2; field_simp
  have P3 : Tendsto (fun m : ℕ => (1 - 3 * (em Q m : ℝ) / (nm Q m : ℝ))) atTop
      (𝓝 (1 - 3 * s)) := by
    have := (tendsto_const_nhds (x := (1 : ℝ))).sub (hee.const_mul (3 : ℝ))
    refine this.congr fun m => ?_
    simp [mul_div_assoc]
  have P3' : Tendsto (fun m : ℕ => (1 - 3 * (em Q m : ℝ) / (nm Q m : ℝ)) ^ t) atTop
      (𝓝 ((1 - 3 * s) ^ t)) := P3.pow t
  have P4 : Tendsto (fun m : ℕ => (1 - (Lm Q m : ℝ) / (nm Q m : ℝ)) ^ t) atTop
      (𝓝 ((1 - 3 * s * (1 - (Q : ℝ)⁻¹) ^ 2) ^ t)) := ((tendsto_const_nhds (x := (1 : ℝ))).sub hLL).pow t
  have hq1 : (1 - (Q : ℝ)⁻¹) ^ 2 ≤ 1 := by
    have h0 : 0 ≤ 1 - (Q : ℝ)⁻¹ := by
      have : (Q : ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by exact_mod_cast (by omega : 1 ≤ Q))
      linarith
    have h1 : 1 - (Q : ℝ)⁻¹ ≤ 1 := by
      have : 0 < (Q : ℝ)⁻¹ := by positivity
      linarith
    nlinarith
  have hPD : (1 - 3 * s * (1 - (Q : ℝ)⁻¹) ^ 2) ^ t ≤ (1 - 3 * p * s) ^ t := by
    have m1 := mul_le_mul_of_nonneg_left hq1 hs0.le
    have m2 := mul_le_mul_of_nonneg_left hEE.le hs0.le
    apply pow_le_pow_left₀
    · linarith
    · linarith
  rw [one_mul] at hA hξ1
  have F1 := P1.eventually (lt_mem_nhds (show c + 3 * ξ < (1 - s) ^ t by linarith))
  have F2 := P2.eventually (gt_mem_nhds (show (1 - 4 / 3 * s) ^ t < a ^ ((4 : ℝ) / 9) - 3 * ξ by
    linarith))
  have F3 := P3'.eventually (lt_mem_nhds hC)
  have F3' := P3.eventually (lt_mem_nhds (show 0 < 1 - 3 * s by linarith))
  have F4 := P4.eventually (gt_mem_nhds (show (1 - 3 * s * (1 - (Q : ℝ)⁻¹) ^ 2) ^ t < a by
    have : (1 - 3 * p * s) ^ t < a := hD
    linarith))
  obtain ⟨m₀, hm₀⟩ := eventually_atTop.1 (F1.and (F2.and (F3.and (F3'.and F4))))
  refine ⟨m₀, fun m hm => ?_⟩
  obtain ⟨g1, g2, g3, g3', g4⟩ := hm₀ m hm
  refine ⟨?_, ?_, ?_⟩
  · unfold Phi; linarith
  · unfold Phi; linarith
  · intro u hu
    obtain ⟨hu1, hu2⟩ := hu
    have hnn : 0 ≤ 1 - u := by linarith
    have k1 : (1 - 3 * (em Q m : ℝ) / (nm Q m : ℝ)) ^ t ≤ (1 - u) ^ t :=
      pow_le_pow_left₀ g3'.le (by linarith) t
    have k2 : (1 - u) ^ t ≤ (1 - (Lm Q m : ℝ) / (nm Q m : ℝ)) ^ t :=
      pow_le_pow_left₀ hnn (by linarith) t
    unfold Phi
    rw [abs_lt]
    constructor <;> linarith

end ProxGapTight
end

theorem solution : type_of% @ProxGapTight.chk_parameter_choice := @ProxGapTight.chk_parameter_choice
