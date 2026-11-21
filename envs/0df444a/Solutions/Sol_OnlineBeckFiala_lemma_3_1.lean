-- Prove2me | solution 1 for OnlineBeckFiala.lemma_3_1
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-20T11:24:32.874315+00:00
-- url     : https://prove2.me/submissions/5a24fcf0-a7a5-4255-b929-2f9e99ff66c5

import Mathlib
import Definitions.Def_OnlineBeckFiala_W
import Theorems.Thm_OnlineBeckFiala_eq_13
import Theorems.Thm_OnlineBeckFiala_eq_10

section
open MeasureTheory

namespace OnlineBeckFiala

namespace Dev.L31

lemma one_sub_sq_pos {y : ℝ} (hy : y ∈ Set.Ioo (-1 : ℝ) 1) : 0 < 1 - y ^ 2 := by
  obtain ⟨h1, h2⟩ := hy; nlinarith

lemma A_ge_one {η y : ℝ} (hη : 0 < η) (hy : y ∈ Set.Ioo (-1 : ℝ) 1) : 1 ≤ A η y := by
  have hp := one_sub_sq_pos hy
  unfold A
  apply Real.one_le_rpow_of_pos_of_le_one_of_nonpos hp (by nlinarith [sq_nonneg y])
  have : 0 < 2 / η := by positivity
  rw [neg_div]; linarith

lemma A_cd {η : ℝ} (y : ℝ) (hy : y ∈ Set.Ioo (-1 : ℝ) 1) : ContDiffAt ℝ 2 (A η) y := by
  have hp := one_sub_sq_pos hy
  unfold A
  exact ((contDiffAt_const.sub (contDiffAt_id.pow 2)).rpow_const_of_ne hp.ne')

lemma u_cdOn (η : ℝ) : ContDiffOn ℝ 2 (u η) (Set.Ioo (-1 : ℝ) 1) := by
  intro y hy
  exact (((A_cd (η := η) y hy).exp)).contDiffWithinAt

lemma u_d1 (η : ℝ) {t : ℝ} (ht : t ∈ Set.Ioo (-1 : ℝ) 1) :
    HasDerivAt (u η) (deriv (u η) t) t := by
  have h := ((u_cdOn η).contDiffAt (Ioo_mem_nhds ht.1 ht.2)).differentiableAt (by norm_num)
  exact h.hasDerivAt

lemma u_d2 (η : ℝ) {t : ℝ} (ht : t ∈ Set.Ioo (-1 : ℝ) 1) :
    HasDerivAt (deriv (u η)) (iteratedDeriv 2 (u η) t) t := by
  have h1 : ContDiffOn ℝ 1 (deriv (u η)) (Set.Ioo (-1 : ℝ) 1) :=
    (u_cdOn η).deriv_of_isOpen isOpen_Ioo (by norm_num)
  have h := (h1.contDiffAt (Ioo_mem_nhds ht.1 ht.2)).differentiableAt (by norm_num)
  have := h.hasDerivAt
  rw [iteratedDeriv_succ, iteratedDeriv_one]
  exact this

lemma taylor_le (g g' g'' : ℝ → ℝ) (y s B : ℝ) (hs : 0 ≤ s)
    (hd : ∀ t ∈ Set.Icc (y - s) (y + s), HasDerivAt g (g' t) t)
    (hd2 : ∀ t ∈ Set.Icc (y - s) (y + s), HasDerivAt g' (g'' t) t)
    (hB : ∀ t ∈ Set.Icc (y - s) (y + s), g'' t ≤ B) :
    g (y + s) + g (y - s) - 2 * g y ≤ s ^ 2 * B := by
  have hk : AntitoneOn (fun τ => g' τ - B * τ) (Set.Icc (y - s) (y + s)) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc _ _)
    · intro t ht
      exact ((hd2 t ht).sub ((hasDerivAt_id t).const_mul B)).continuousAt.continuousWithinAt
    · intro t ht
      rw [interior_Icc] at ht
      exact ((hd2 t (Set.Ioo_subset_Icc_self ht)).sub ((hasDerivAt_id t).const_mul B)).differentiableAt.differentiableWithinAt
    · intro t ht
      rw [interior_Icc] at ht
      have := (hd2 t (Set.Ioo_subset_Icc_self ht)).sub ((hasDerivAt_id t).const_mul B)
      have e : deriv (fun τ => g' τ - B * τ) t = g'' t - B := by
        have h : HasDerivAt (fun τ => g' τ - B * τ) (g'' t - B * 1) t :=
          (hd2 t (Set.Ioo_subset_Icc_self ht)).sub ((hasDerivAt_id' t).const_mul B)
        rw [h.deriv]; ring
      rw [e]
      have := hB t (Set.Ioo_subset_Icc_self ht)
      linarith
  have hmem : ∀ t ∈ Set.Icc (0:ℝ) s, y + t ∈ Set.Icc (y - s) (y + s) ∧ y - t ∈ Set.Icc (y - s) (y + s) := by
    intro t ht; obtain ⟨h0, h1⟩ := ht
    exact ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩
  let h : ℝ → ℝ := fun t => g (y + t) + g (y - t) - 2 * g y - B * t ^ 2
  have hh : ∀ t ∈ Set.Icc (0:ℝ) s, HasDerivAt h (g' (y + t) - g' (y - t) - 2 * B * t) t := by
    intro t ht
    obtain ⟨m1, m2⟩ := hmem t ht
    have e1 : HasDerivAt (fun t => g (y + t)) (g' (y + t)) t := by
      exact HasDerivAt.comp_const_add y t (by simpa using hd _ m1)
    have e2 : HasDerivAt (fun t => g (y - t)) (-g' (y - t)) t := by
      exact HasDerivAt.comp_const_sub y t (by simpa using hd _ m2)
    have e3 := (e1.add e2).sub_const (2 * g y) |>.sub ((hasDerivAt_pow 2 t).const_mul B)
    exact e3.congr_deriv (by norm_num; ring)
  have hanti : AntitoneOn h (Set.Icc 0 s) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc _ _)
    · intro t ht; exact (hh t ht).continuousAt.continuousWithinAt
    · intro t ht
      rw [interior_Icc] at ht
      exact (hh t (Set.Ioo_subset_Icc_self ht)).differentiableAt.differentiableWithinAt
    · intro t ht
      rw [interior_Icc] at ht
      have ht' := Set.Ioo_subset_Icc_self ht
      rw [(hh t ht').deriv]
      obtain ⟨m1, m2⟩ := hmem t ht'
      have := hk m2 m1 (by linarith [ht.1])
      simp only at this
      linarith
  have := hanti ⟨le_refl _, hs⟩ ⟨hs, le_refl _⟩ hs
  simp only [h] at this
  simp at this
  nlinarith

set_option maxHeartbeats 2000000 in
/-- Window lemma. -/
lemma window {η y s t r : ℝ} (hη : 0 < η) (hy : y ∈ Set.Ioo (-1 : ℝ) 1) (hs : 0 ≤ s)
    (hr4 : 4 ≤ r) (hrη : 16 ≤ r * η) (hsa : s * A η y * r ≤ 1 - y ^ 2)
    (ht : |t - y| ≤ s) : t ∈ Set.Ioo (-1 : ℝ) 1 ∧ A η t ≤ A η y + 1 := by
  have hp := one_sub_sq_pos hy
  set p := 1 - y ^ 2 with hpdef
  set a := A η y with hadef
  have ha1 : 1 ≤ a := A_ge_one hη hy
  have har : 4 ≤ a * r := by nlinarith
  have hsp : 4 * s ≤ p := by nlinarith
  have hsa' : s * a * r ≤ p := hsa
  -- |t| < 1
  have hy1 := abs_lt.mpr hy
  have hp2 : p ≤ 2 * (1 - |y|) := by
    have : p = (1 - |y|) * (1 + |y|) := by
      rw [hpdef]; nlinarith [sq_abs y]
    rw [this]; nlinarith [abs_nonneg y]
  have htabs : |t| ≤ |y| + s := by
    have := abs_sub_abs_le_abs_sub t y
    linarith [abs_le.mp ht]
  have htI : t ∈ Set.Ioo (-1 : ℝ) 1 := by
    have : |t| < 1 := by linarith
    exact abs_lt.mp this
  refine ⟨htI, ?_⟩
  have h1t : p - 2 * s ≤ 1 - t ^ 2 := by
    have : t ^ 2 - y ^ 2 = (t - y) * (t + y) := by ring
    have hty : |t + y| ≤ 2 := by
      have := abs_add_le t y
      have := htI.1; have := htI.2
      have := abs_lt.mpr htI
      linarith
    have : |t ^ 2 - y ^ 2| ≤ 2 * s := by
      rw [this, abs_mul]
      nlinarith [abs_nonneg (t - y), abs_nonneg (t + y)]
    have := (abs_le.mp this).2
    rw [hpdef]; linarith
  set x := 2 * s / p with hxdef
  have hx0 : 0 ≤ x := by positivity
  have hxa : a * x * r ≤ 2 := by
    rw [hxdef]
    have : a * (2 * s / p) * r = 2 * (s * a * r) / p := by ring
    rw [this, div_le_iff₀ hp]; linarith
  have hx12 : x ≤ 1 / 2 := by
    have : x * r ≤ 2 := by nlinarith
    nlinarith
  have hpx : p * (1 - x) ≤ 1 - t ^ 2 := by
    have : p * x = 2 * s := by rw [hxdef]; field_simp
    nlinarith
  have hpos : 0 < p * (1 - x) := by apply mul_pos hp; linarith
  set q : ℝ := 2 / η with hq
  have hq0 : 0 < q := by positivity
  have hAt : A η t ≤ (p * (1 - x)) ^ (-q) := by
    unfold A
    rw [show -2 / η = -q by rw [hq]; ring]
    exact Real.rpow_le_rpow_of_nonpos hpos hpx (by linarith)
  have hpa : p ^ (-q) = a := by
    rw [hadef]; unfold A; rw [hpdef]; congr 1; ring
  rw [Real.mul_rpow hp.le (by linarith)] at hAt
  rw [hpa] at hAt
  -- (1-x)^(-q) ≤ exp(2 q x)
  have h1x : 0 < 1 - x := by linarith
  have hlog : Real.log ((1 - x)⁻¹) ≤ 2 * x := by
    have := Real.log_le_sub_one_of_pos (inv_pos.mpr h1x)
    have h2 : (1 - x)⁻¹ - 1 ≤ 2 * x := by
      rw [inv_eq_one_div, div_sub_one h1x.ne', div_le_iff₀ h1x]
      nlinarith
    linarith
  have hpow : (1 - x) ^ (-q) ≤ Real.exp (q * (2 * x)) := by
    rw [Real.rpow_def_of_pos h1x]
    apply Real.exp_le_exp.mpr
    rw [Real.log_inv] at hlog
    nlinarith
  set z := q * (2 * x) with hz
  have hz0 : 0 ≤ z := by positivity
  have hzr : a * z ≤ 1 / 2 := by
    have : a * z = (4 / η) * (a * x) := by rw [hz, hq]; field_simp; ring
    rw [this]
    have h3 : a * x ≤ 2 / r := by rw [le_div_iff₀ (by linarith)]; nlinarith
    have : 4 / η * (a * x) ≤ 4 / η * (2 / r) := by gcongr
    have h5 : 4 / η * (2 / r) = 8 / (r * η) := by field_simp; norm_num
    have h6 : 8 / (r * η) ≤ 1 / 2 := by rw [div_le_iff₀ (by positivity)]; linarith
    linarith
  have hz12 : z ≤ 1 / 2 := by nlinarith
  have hexp : Real.exp z ≤ 1 + 2 * z := by
    have h1 : 1 - z ≤ Real.exp (-z) := by linarith [Real.add_one_le_exp (-z)]
    have h2 : Real.exp z * Real.exp (-z) = 1 := by rw [← Real.exp_add]; simp
    have h3 : Real.exp z * (1 - z) ≤ 1 := by
      calc Real.exp z * (1 - z) ≤ Real.exp z * Real.exp (-z) := by gcongr
        _ = 1 := h2
    nlinarith [Real.exp_pos z]
  calc A η t ≤ a * (1 - x) ^ (-q) := by linarith
    _ ≤ a * (1 + 2 * z) := by gcongr; linarith
    _ ≤ a + 1 := by nlinarith

lemma Z_pos {η : ℝ} (hη : 0 < η) :
    IntegrableOn (fun y => Real.exp (-u η y)) (Set.Ioo (-1) 1) ∧ 0 < Zu (u η) := by
  have hc : ContinuousOn (fun y => Real.exp (-u η y)) (Set.Ioo (-1) 1) := by
    intro y hy
    have := (u_cdOn η).continuousOn y hy
    exact (this.neg.rexp)
  have hb : ∀ y ∈ Set.Ioo (-1 : ℝ) 1, ‖Real.exp (-u η y)‖ ≤ 1 := by
    intro y hy
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.exp_le_one_iff, neg_nonpos]
    unfold u; exact (Real.exp_pos _).le
  have hint : IntegrableOn (fun y => Real.exp (-u η y)) (Set.Ioo (-1) 1) := by
    refine Integrable.of_bound (C := 1) (hc.aestronglyMeasurable measurableSet_Ioo) ?_
    exact (ae_restrict_iff' measurableSet_Ioo).mpr (Filter.Eventually.of_forall hb)
  refine ⟨hint, ?_⟩
  have hii : IntervalIntegrable (fun y => Real.exp (-u η y)) volume (-1) 1 := by
    rw [intervalIntegrable_iff_integrableOn_Ioo_of_le (by norm_num)]; exact hint
  have := intervalIntegral.intervalIntegral_pos_of_pos_on hii
    (fun y hy => Real.exp_pos _) (by norm_num : (-1:ℝ) < 1)
  unfold Zu
  rw [intervalIntegral.integral_of_le (by norm_num), integral_Ioc_eq_integral_Ioo] at this
  exact this

lemma potLaw_compl (v : ℝ → ℝ) : potLaw v (Set.Ioo (-1 : ℝ) 1)ᶜ = 0 := by
  unfold potLaw
  rw [withDensity_apply _ measurableSet_Ioo.compl]
  refine (setLIntegral_congr_fun measurableSet_Ioo.compl (fun y hy => ?_)).trans lintegral_zero
  simp [uRho, Set.indicator_of_notMem (show y ∉ Set.Ioo (-1:ℝ) 1 by simpa using hy)]

lemma part16 {η : ℝ} (hη : 0 < η) {C : ℝ} (hCpos : 0 < C)
    (hC : ∀ y ∈ Set.Ioo (-1 : ℝ) 1,
      iteratedDeriv 2 (u η) y ≤ C * u η y * (Real.log (u η y)) ^ (2 + η))
    {M : ℝ} (hM1 : 16 ≤ M) (hM2 : (16 / η) ^ 2 ≤ M)
    (hM3 : C * Real.exp 1 * 2 ^ (2 + η) ≤ M)
    {y : ℝ} (hy : y ∈ Set.Ioo (-1 : ℝ) 1) {s : ℝ} (hs : 0 ≤ s)
    (h : s ^ 2 * W η M y ≤ 1) :
    y + s ∈ Set.Ioo (-1 : ℝ) 1 ∧ y - s ∈ Set.Ioo (-1 : ℝ) 1 ∧
      u η (y + s) + u η (y - s) - 2 * u η y ≤ s ^ 2 * W η M y := by
  have hp := one_sub_sq_pos hy
  set p := 1 - y ^ 2 with hpdef
  set a := A η y with hadef
  have ha1 : 1 ≤ a := A_ge_one hη hy
  have hapos : 0 < a := by linarith
  set r := Real.sqrt M with hrdef
  have hMr : r ^ 2 = M := Real.sq_sqrt (by linarith)
  have hr4 : 4 ≤ r := by
    rw [hrdef]; apply Real.le_sqrt_of_sq_le; linarith
  have hrη : 16 ≤ r * η := by
    have : 16 / η ≤ r := by
      rw [hrdef]; apply Real.le_sqrt_of_sq_le; exact hM2
    rw [div_le_iff₀ hη] at this; exact this
  have hk : (2 : ℝ) + η = (1 + η / 2) * 2 := by ring
  set b := a ^ (1 + η / 2) with hbdef
  have hb2 : a ^ (2 + η) = b ^ 2 := by
    rw [hk, Real.rpow_mul hapos.le]; norm_cast
  have hb0 : 0 ≤ b := by positivity
  have hWdef : W η M y = M * Real.exp a * a ^ (2 + η) := rfl
  have hsrb : s * r * b ≤ 1 := by
    have h1 : (s * r * b) ^ 2 ≤ 1 := by
      have : (s * r * b) ^ 2 = s ^ 2 * M * a ^ (2 + η) := by rw [hb2, ← hMr]; ring
      rw [this]
      have he : 1 ≤ Real.exp a := Real.one_le_exp (by linarith)
      have hpos : 0 ≤ s ^ 2 * M * a ^ (2 + η) := by positivity
      rw [hWdef] at h
      nlinarith
    have h0 : 0 ≤ s * r * b := by positivity
    nlinarith
  have hpa : a ^ (η / 2) * p = 1 := by
    have : a ^ (η / 2) = p ^ (-1 : ℝ) := by
      rw [hadef]; unfold A
      rw [← Real.rpow_mul hp.le]; congr 1; field_simp
    rw [this, Real.rpow_neg_one]; exact inv_mul_cancel₀ hp.ne'
  have hba : b = a * a ^ (η / 2) := by
    rw [hbdef, Real.rpow_add hapos, Real.rpow_one]
  have hsa : s * a * r ≤ p := by
    have : s * r * b * p = s * a * r := by
      rw [hba]; calc s * r * (a * a ^ (η / 2)) * p = s * r * a * (a ^ (η / 2) * p) := by ring
        _ = s * a * r := by rw [hpa]; ring
    rw [← this]
    nlinarith [mul_nonneg hs (by linarith : (0:ℝ) ≤ r)]
  have hwin : ∀ t, |t - y| ≤ s → t ∈ Set.Ioo (-1 : ℝ) 1 ∧ A η t ≤ a + 1 :=
    fun t ht => window hη hy hs hr4 hrη hsa ht
  have hIcc : ∀ t ∈ Set.Icc (y - s) (y + s), t ∈ Set.Ioo (-1 : ℝ) 1 ∧ A η t ≤ a + 1 := by
    intro t ht
    apply hwin
    rw [abs_le]; constructor <;> linarith [ht.1, ht.2]
  have hB : ∀ t ∈ Set.Icc (y - s) (y + s), iteratedDeriv 2 (u η) t ≤ W η M y := by
    intro t ht
    obtain ⟨htI, hAt⟩ := hIcc t ht
    have h1 := hC t htI
    have hA1 := A_ge_one hη htI
    have : Real.log (u η t) = A η t := by unfold u; exact Real.log_exp _
    rw [this] at h1
    have hu : u η t = Real.exp (A η t) := rfl
    rw [hu] at h1
    have e1 : Real.exp (A η t) ≤ Real.exp 1 * Real.exp a := by
      rw [← Real.exp_add]; apply Real.exp_le_exp.mpr; linarith
    have e2 : A η t ^ (2 + η) ≤ 2 ^ (2 + η) * a ^ (2 + η) := by
      rw [← Real.mul_rpow (by norm_num) hapos.le]
      exact Real.rpow_le_rpow (by linarith) (by linarith) (by positivity)
    have e3 : 0 ≤ A η t ^ (2 + η) := by positivity
    have e4 : 0 ≤ a ^ (2 + η) := by positivity
    calc iteratedDeriv 2 (u η) t ≤ C * Real.exp (A η t) * A η t ^ (2 + η) := h1
      _ ≤ C * (Real.exp 1 * Real.exp a) * (2 ^ (2 + η) * a ^ (2 + η)) := by
          apply mul_le_mul (mul_le_mul_of_nonneg_left e1 hCpos.le) e2 e3
          positivity
      _ = (C * Real.exp 1 * 2 ^ (2 + η)) * Real.exp a * a ^ (2 + η) := by ring
      _ ≤ M * Real.exp a * a ^ (2 + η) := by
          gcongr
      _ = W η M y := hWdef.symm
  have hy1 := hwin (y + s) (by simp [abs_of_nonneg hs])
  have hy2 := hwin (y - s) (by simp [abs_of_nonneg hs])
  refine ⟨hy1.1, hy2.1, ?_⟩
  exact taylor_le (u η) (deriv (u η)) (iteratedDeriv 2 (u η)) y s (W η M y) hs
    (fun t ht => u_d1 η (hIcc t ht).1) (fun t ht => u_d2 η (hIcc t ht).1) hB

lemma part15 {η : ℝ} (hη : 0 < η) {M : ℝ} (hM : 1 ≤ M) {x : ℝ} (hx : 1 ≤ x) :
    rho1 η {y | x < W η M y} ≤
      ENNReal.ofReal (2 / Zu (u η) * Real.exp (-(1 / M * x) /
        (Real.log (Real.exp 1 * x)) ^ (2 + η))) := by
  obtain ⟨hint, hZ⟩ := Z_pos hη
  set L := Real.log (Real.exp 1 * x) with hL
  have hL1 : 1 ≤ L := by
    rw [hL, Real.log_mul (Real.exp_pos 1).ne' (by linarith), Real.log_exp]
    linarith [Real.log_nonneg hx]
  have hLk : 1 ≤ L ^ (2 + η) := Real.one_le_rpow hL1 (by linarith)
  set r := x / (M * L ^ (2 + η)) with hr
  have hrx : r ≤ x := by
    rw [hr, div_le_iff₀ (by positivity)]
    nlinarith [mul_le_mul hM hLk zero_le_one (by linarith : (0:ℝ) ≤ M)]
  have hsub : {y | x < W η M y} ⊆ {y | r < u η y} ∪ (Set.Ioo (-1 : ℝ) 1)ᶜ := by
    intro y hy
    by_cases hyI : y ∈ Set.Ioo (-1 : ℝ) 1
    · left
      have hA1 := A_ge_one hη hyI
      have hy' : x < M * Real.exp (A η y) * A η y ^ (2 + η) := hy
      show r < Real.exp (A η y)
      by_cases hc : L ≤ A η y
      · have : Real.exp L ≤ Real.exp (A η y) := Real.exp_le_exp.mpr hc
        have h2 : Real.exp L = Real.exp 1 * x := by
          rw [hL, Real.exp_log (by positivity)]
        have := Real.exp_one_gt_d9
        nlinarith [Real.exp_pos 1]
      · push_neg at hc
        have h3 : A η y ^ (2 + η) ≤ L ^ (2 + η) :=
          Real.rpow_le_rpow (by linarith) hc.le (by positivity)
        have h4 : x < M * Real.exp (A η y) * L ^ (2 + η) := by
          refine lt_of_lt_of_le hy' ?_
          gcongr
        rw [hr, div_lt_iff₀ (by positivity)]
        linarith
    · right; exact hyI
  have h10 := eq_10 (u η) hint r |>.2
  calc rho1 η {y | x < W η M y} ≤ potLaw (u η) ({y | r < u η y} ∪ (Set.Ioo (-1 : ℝ) 1)ᶜ) :=
        measure_mono hsub
    _ ≤ potLaw (u η) {y | r < u η y} + potLaw (u η) (Set.Ioo (-1 : ℝ) 1)ᶜ := measure_union_le _ _
    _ = potLaw (u η) {y | r < u η y} := by rw [potLaw_compl, add_zero]
    _ ≤ ENNReal.ofReal (2 / Zu (u η) * Real.exp (-r)) := h10
    _ = _ := by
        congr 3
        rw [hr]; ring

end Dev.L31

theorem chk_lemma_3_1 (η : ℝ) (hη : 0 < η) :
    ∃ M : ℝ, 1 ≤ M ∧ ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      (∀ x : ℝ, 1 ≤ x →
        rho1 η {y | x < W η M y} ≤
          ENNReal.ofReal (C * Real.exp (-(c * x) / (Real.log (Real.exp 1 * x)) ^ (2 + η)))) ∧
      (∀ y ∈ Set.Ioo (-1 : ℝ) 1, ∀ s : ℝ, s ^ 2 * W η M y ≤ 1 →
        y + s ∈ Set.Ioo (-1 : ℝ) 1 ∧ y - s ∈ Set.Ioo (-1 : ℝ) 1 ∧
        u η (y + s) + u η (y - s) - 2 * u η y ≤ s ^ 2 * W η M y) := by
  obtain ⟨C, hCpos, hC13⟩ := eq_13 η hη
  have hC : ∀ y ∈ Set.Ioo (-1 : ℝ) 1,
      iteratedDeriv 2 (u η) y ≤ C * u η y * (Real.log (u η y)) ^ (2 + η) :=
    fun y hy => (hC13 y hy).2.2
  set M := max (max 16 ((16 / η) ^ 2)) (C * Real.exp 1 * 2 ^ (2 + η)) with hM
  have hM1 : 16 ≤ M := le_trans (le_max_left _ _) (le_max_left _ _)
  have hM2 : (16 / η) ^ 2 ≤ M := le_trans (le_max_right _ _) (le_max_left _ _)
  have hM3 : C * Real.exp 1 * 2 ^ (2 + η) ≤ M := le_max_right _ _
  have hZ := (Dev.L31.Z_pos hη).2
  refine ⟨M, by linarith, 1 / M, 2 / Zu (u η), by positivity, by positivity, ?_, ?_⟩
  · intro x hx
    exact Dev.L31.part15 hη (by linarith) hx
  · intro y hy s hs
    rcases le_total 0 s with h0 | h0
    · exact Dev.L31.part16 hη hCpos hC hM1 hM2 hM3 hy h0 hs
    · have := Dev.L31.part16 hη hCpos hC hM1 hM2 hM3 hy (neg_nonneg.mpr h0)
        (by simpa using hs)
      obtain ⟨a1, a2, a3⟩ := this
      refine ⟨by simpa using a2, by simpa [sub_eq_add_neg] using a1, ?_⟩
      have e : u η (y + -s) + u η (y - -s) = u η (y + s) + u η (y - s) := by
        rw [sub_neg_eq_add, ← sub_eq_add_neg]; ring
      rw [e] at a3; simpa using a3

end OnlineBeckFiala
end

theorem solution : type_of% @OnlineBeckFiala.chk_lemma_3_1 := @OnlineBeckFiala.chk_lemma_3_1
