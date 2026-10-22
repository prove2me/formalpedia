-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Claimed50.P39.entropyBoundAsymptotics
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T08:13:17.681286+00:00
-- url     : https://prove2.me/submissions/34576694-5ad9-45d5-8741-33c0feafc8f0

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P39
noncomputable section

open QAlgorithms.Papers.Independent.Claimed50.P39

open Filter MeasureTheory

open scoped Topology ENNReal

attribute [local instance] Classical.propDecidable



theorem g67q_log1p : Tendsto (fun x : ℝ => Real.log (1 + x) / x) (𝓝[>] 0) (𝓝 1) := by
  have hlow : Tendsto (fun x : ℝ => 1 / (1 + x)) (𝓝[>] 0) (𝓝 1) := by
    have : Tendsto (fun x : ℝ => 1 / (1 + x)) (𝓝 0) (𝓝 (1 / (1 + 0))) :=
      tendsto_const_nhds.div (tendsto_const_nhds.add tendsto_id) (by norm_num)
    simpa using tendsto_nhdsWithin_of_tendsto_nhds this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow tendsto_const_nhds ?_ ?_
  · filter_upwards [self_mem_nhdsWithin] with x (hx : 0 < x)
    have h := Real.one_sub_inv_le_log_of_pos (show 0 < 1 + x by linarith)
    rw [le_div_iff₀ hx]
    have : 1 - (1 + x)⁻¹ = x / (1 + x) := by field_simp; ring
    rw [this] at h
    calc 1 / (1 + x) * x = x / (1 + x) := by ring
      _ ≤ _ := h
  · filter_upwards [self_mem_nhdsWithin] with x (hx : 0 < x)
    rw [div_le_iff₀ hx, one_mul]
    have := Real.log_le_sub_one_of_pos (show 0 < 1 + x by linarith)
    linarith

theorem g67q_part2 : Tendsto (fun n : ℝ => (1 + Real.log n) /
    ((n + 1) * Real.log (n + 1) - n * Real.log n)) atTop (𝓝 1) := by
  set G : ℝ → ℝ := fun n => (n + 1) * Real.log (n + 1) - n * Real.log n with hGdef
  set D : ℝ → ℝ := fun n => (n + 1) * Real.log (1 + 1 / n) - 1 with hDdef
  have hlg : Tendsto (fun n : ℝ => Real.log (1 + 1 / n)) atTop (𝓝 0) := by
    have h1 : Tendsto (fun n : ℝ => 1 + 1 / n) atTop (𝓝 (1 + 0)) :=
      tendsto_const_nhds.add (tendsto_const_nhds.div_atTop tendsto_id)
    rw [add_zero] at h1
    have := ((Real.continuousAt_log one_ne_zero).tendsto).comp h1
    rwa [Real.log_one] at this
  have hD : Tendsto D atTop (𝓝 0) := by
    have h1 := Real.tendsto_mul_log_one_add_div_atTop 1
    have : Tendsto (fun n : ℝ => n * Real.log (1 + 1 / n) + Real.log (1 + 1 / n) - 1) atTop
        (𝓝 (1 + 0 - 1)) := (h1.add hlg).sub tendsto_const_nhds
    rw [show (1 : ℝ) + 0 - 1 = 0 by ring] at this
    refine this.congr fun n => ?_
    simp only [hDdef]; ring
  have hG : ∀ n : ℝ, 0 < n → G n = 1 + Real.log n + D n := by
    intro n hn
    have : Real.log (n + 1) = Real.log n + Real.log (1 + 1 / n) := by
      rw [← Real.log_mul hn.ne' (by positivity)]; congr 1; field_simp
    simp only [hGdef, hDdef, this]; ring
  have hGge : ∀ n : ℝ, 0 < n → Real.log n ≤ G n := by
    intro n hn
    have : Real.log (n + 1) = Real.log n + Real.log (1 + 1 / n) := by
      rw [← Real.log_mul hn.ne' (by positivity)]; congr 1; field_simp
    have h0 : 0 ≤ Real.log (1 + 1 / n) := Real.log_nonneg (by have h : 0 < 1 / n := (by positivity); linarith)
    simp only [hGdef, this]; nlinarith
  have hGtop : Tendsto G atTop atTop :=
    tendsto_atTop_mono' atTop ((eventually_gt_atTop 0).mono fun n hn => hGge n hn) Real.tendsto_log_atTop
  have hlim : Tendsto (fun n => 1 - D n * (G n)⁻¹) atTop (𝓝 (1 - 0 * 0)) :=
    tendsto_const_nhds.sub (hD.mul hGtop.inv_tendsto_atTop)
  rw [show (1 : ℝ) - 0 * 0 = 1 by ring] at hlim
  refine hlim.congr' ?_
  filter_upwards [eventually_gt_atTop 0, hGtop.eventually_gt_atTop 0] with n hn hGn
  show 1 - D n * (G n)⁻¹ = (1 + Real.log n) / G n
  rw [hG n hn] at hGn ⊢
  field_simp
  ring

theorem g67q_part1 :
    Tendsto (fun n : ℝ => (-((1 - Real.sqrt ((1 - 2 * n) / (1 + 2 * n))) / 2) *
        Real.log ((1 - Real.sqrt ((1 - 2 * n) / (1 + 2 * n))) / 2) -
      (1 - (1 - Real.sqrt ((1 - 2 * n) / (1 + 2 * n))) / 2) *
        Real.log ((1 - (1 - Real.sqrt ((1 - 2 * n) / (1 + 2 * n))) / 2) / 1)) /
      ((n + 1) * Real.log (n + 1) - n * Real.log n)) (𝓝[>] 0) (𝓝 1) := by
  set q : ℝ → ℝ := fun n => Real.sqrt ((1 - 2 * n) / (1 + 2 * n)) with hq
  set lam : ℝ → ℝ := fun n => (1 - q n) / 2 with hlamdef
  set a : ℝ → ℝ := fun n => 2 / ((1 + 2 * n) * (1 + q n)) with ha
  set c : ℝ → ℝ := fun n => Real.log (1 - lam n) / lam n with hc
  have hqc : Tendsto q (𝓝[>] 0) (𝓝 1) := by
    have : Tendsto (fun n : ℝ => (1 - 2 * n) / (1 + 2 * n)) (𝓝 0) (𝓝 ((1 - 2 * 0) / (1 + 2 * 0))) :=
      (tendsto_const_nhds.sub (tendsto_const_nhds.mul tendsto_id)).div
        (tendsto_const_nhds.add (tendsto_const_nhds.mul tendsto_id)) (by norm_num)
    have h2 := this.sqrt
    simp only [mul_zero, sub_zero, add_zero, div_one, Real.sqrt_one] at h2
    exact tendsto_nhdsWithin_of_tendsto_nhds h2
  have hac : Tendsto a (𝓝[>] 0) (𝓝 1) := by
    have h1 : Tendsto (fun n : ℝ => 1 + 2 * n) (𝓝[>] 0) (𝓝 (1 + 2 * 0)) :=
      tendsto_nhdsWithin_of_tendsto_nhds (tendsto_const_nhds.add (tendsto_const_nhds.mul tendsto_id))
    have : Tendsto (fun n => 2 / ((1 + 2 * n) * (1 + q n))) (𝓝[>] 0)
        (𝓝 (2 / ((1 + 2 * 0) * (1 + 1)))) :=
      tendsto_const_nhds.div (h1.mul ((tendsto_const_nhds (x := (1 : ℝ))).add hqc)) (by norm_num)
    norm_num at this
    exact this
  have hlam0 : Tendsto lam (𝓝[>] 0) (𝓝 0) := by
    have := (tendsto_const_nhds (x := (1 : ℝ))).sub hqc |>.div_const 2
    simpa [hlamdef] using this
  have hev : ∀ᶠ n in 𝓝[>] (0 : ℝ), n ∈ Set.Ioo (0 : ℝ) (1 / 2) := Ioo_mem_nhdsGT (by norm_num)
  have hq0 : ∀ n, 0 ≤ q n := fun n => Real.sqrt_nonneg _
  have hlam : ∀ n ∈ Set.Ioo (0 : ℝ) (1 / 2), lam n = n * a n := by
    intro n hn
    have h1 : q n ^ 2 * (1 + 2 * n) = 1 - 2 * n := by
      rw [Real.sq_sqrt (div_nonneg (by linarith [hn.2]) (by linarith [hn.1])),
        div_mul_cancel₀ _ (ne_of_gt (by linarith [hn.1] : (0 : ℝ) < 1 + 2 * n))]
    have h2 : 0 < 1 + 2 * n := by linarith [hn.1]
    have h3 : 0 < 1 + q n := by linarith [hq0 n]
    simp only [hlamdef, ha]
    field_simp
    linear_combination (-1 : ℝ) * h1
  have hapos : ∀ n ∈ Set.Ioo (0 : ℝ) (1 / 2), 0 < a n := by
    intro n hn
    have h2 : 0 < 1 + 2 * n := by linarith [hn.1]
    have h3 : 0 < 1 + q n := by linarith [hq0 n]
    simp only [ha]; positivity
  have hlampos : ∀ n ∈ Set.Ioo (0 : ℝ) (1 / 2), 0 < lam n := fun n hn => by
    rw [hlam n hn]; exact mul_pos hn.1 (hapos n hn)
  have hlamlt : ∀ n, lam n ≤ 1 / 2 := fun n => by
    simp only [hlamdef]; linarith [hq0 n]
  -- c → -1
  have hcc : Tendsto c (𝓝[>] 0) (𝓝 (-1)) := by
    have hlow : Tendsto (fun n => -1 / (1 - lam n)) (𝓝[>] 0) (𝓝 (-1 / (1 - 0))) :=
      tendsto_const_nhds.div (tendsto_const_nhds.sub hlam0) (by norm_num)
    rw [sub_zero, div_one] at hlow
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow tendsto_const_nhds ?_ ?_
    · filter_upwards [hev] with n hn
      have hl := hlampos n hn
      have hl1 := hlamlt n
      have h1 : 0 < 1 - lam n := by linarith
      have h := Real.one_sub_inv_le_log_of_pos h1
      simp only [hc]
      rw [le_div_iff₀ hl]
      have e : 1 - (1 - lam n)⁻¹ = -1 / (1 - lam n) * lam n := by field_simp; ring
      linarith
    · filter_upwards [hev] with n hn
      have hl := hlampos n hn
      have hl1 := hlamlt n
      have h := Real.log_le_sub_one_of_pos (show 0 < 1 - lam n by linarith)
      simp only [hc]
      rw [div_le_iff₀ hl]
      linarith
  have hL : Tendsto (fun n : ℝ => (Real.log n)⁻¹) (𝓝[>] 0) (𝓝 0) :=
    tendsto_inv_atBot_zero.comp Real.tendsto_log_nhdsGT_zero
  have hb : Tendsto (fun n => Real.log (a n)) (𝓝[>] 0) (𝓝 0) := by
    have := ((Real.continuousAt_log one_ne_zero).tendsto).comp hac
    rwa [Real.log_one] at this
  have hl1p := g67q_log1p
  have hn0 : Tendsto (fun n : ℝ => n + 1) (𝓝[>] 0) (𝓝 (0 + 1)) :=
    tendsto_nhdsWithin_of_tendsto_nhds (tendsto_id.add tendsto_const_nhds)
  rw [zero_add] at hn0
  -- numerator and denominator after division by -n log n
  set NUM : ℝ → ℝ := fun n => a n * (1 + Real.log (a n) * (Real.log n)⁻¹) +
      (1 - lam n) * c n * a n * (Real.log n)⁻¹ with hNUM
  set DEN : ℝ → ℝ := fun n => 1 - (n + 1) * (Real.log (1 + n) / n) * (Real.log n)⁻¹ with hDEN
  have hnum : Tendsto NUM (𝓝[>] 0) (𝓝 (1 * (1 + 0 * 0) + (1 - 0) * (-1) * 1 * 0)) :=
    (hac.mul (tendsto_const_nhds.add (hb.mul hL))).add
      ((((tendsto_const_nhds.sub hlam0).mul hcc).mul hac).mul hL)
  have hden : Tendsto DEN (𝓝[>] 0) (𝓝 (1 - 1 * 1 * 0)) :=
    tendsto_const_nhds.sub ((hn0.mul hl1p).mul hL)
  have hlim : Tendsto (fun n => NUM n / DEN n) (𝓝[>] 0) (𝓝 1) := by
    have := hnum.div hden (by norm_num)
    norm_num at this
    exact this
  refine hlim.congr' ?_
  filter_upwards [hev] with n hn
  have hn1 := hn.1
  have hlogn : Real.log n < 0 := Real.log_neg hn1 (by linarith [hn.2])
  have hl := hlampos n hn
  have hapos' := hapos n hn
  have hlamn := hlam n hn
  have hnL : -n * Real.log n ≠ 0 := by
    have : 0 < -n * Real.log n := by nlinarith
    exact this.ne'
  have hlog0 : Real.log n ≠ 0 := hlogn.ne
  have hnne : n ≠ 0 := hn1.ne'
  have hloglam : Real.log (lam n) = Real.log n + Real.log (a n) := by
    rw [hlamn, Real.log_mul hn1.ne' hapos'.ne']
  have e1 : NUM n = (-lam n * Real.log (lam n) - (1 - lam n) * Real.log ((1 - lam n) / 1)) /
      (-n * Real.log n) := by
    rw [hloglam, div_one]
    simp only [hNUM, hc]
    rw [hlamn]
    field_simp
    ring
  have e2 : DEN n = ((n + 1) * Real.log (n + 1) - n * Real.log n) / (-n * Real.log n) := by
    simp only [hDEN]
    rw [add_comm n 1]
    field_simp
    ring
  show NUM n / DEN n = (-lam n * Real.log (lam n) - (1 - lam n) * Real.log ((1 - lam n) / 1)) /
      ((n + 1) * Real.log (n + 1) - n * Real.log n)
  rw [e1, e2, div_div_div_cancel_right₀ hnL]

theorem solution :
    Tendsto (fun n : ℝ => boundC 1 n / g n) (nhdsWithin 0 (Set.Ioi 0)) (nhds 1) ∧
    Tendsto (fun n : ℝ => (1 + Real.log n) / g n) atTop (nhds 1) := by
  refine ⟨?_, ?_⟩
  · refine g67q_part1.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with n (hn : 0 < n)
    have e : (1 : ℝ) - (1 + 1) * (1 - 1 / (2 * n + 1)) = (1 - 2 * n) / (1 + 2 * n) := by
      have : (2 * n + 1) ≠ 0 := by linarith
      have : (1 + 2 * n) ≠ 0 := by linarith
      field_simp
      ring
    have hl : lambdaBound 1 n = (1 - Real.sqrt ((1 - 2 * n) / (1 + 2 * n))) / 2 := by
      simp only [lambdaBound, Nat.cast_one]
      rw [e]
      norm_num
    simp only [boundC, g, hl, Nat.cast_one]
  · exact g67q_part2

end
