-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Renew46.P42.criticalVortex_radiusAndLimits
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T06:07:37.876824+00:00
-- url     : https://prove2.me/submissions/dfb3423c-f0ea-4752-9c0e-b5981455e70f

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P42
open QAlgorithms.Papers.Independent.Renew46.P42

noncomputable section

open Filter Set Topology Real

theorem g66k2_beta (n : ℝ) (hn : 1 < n) :
    let m := n ^ 2
    let s := Real.sqrt (6 * m - 5)
    let A := -(27 - 70 * n ^ 2 + 45 * n ^ 4)
    let B := 2 * n ^ 2 * (6 * n ^ 2 - 5) * s
    0 < s ∧ s ^ 2 = 6 * m - 5 ∧ 0 < B ∧ A < 0 ∧ -1 ≤ A / B ∧ A / B ≤ 1 := by
  intro m s A B
  have hm : 1 < m := by simp only [m]; nlinarith
  have hD : 0 < 6 * m - 5 := by linarith
  have hs : 0 < s := Real.sqrt_pos.2 hD
  have hs2 : s ^ 2 = 6 * m - 5 := Real.sq_sqrt hD.le
  have hB : 0 < B := by simp only [B]; have : 0 < 6 * n ^ 2 - 5 := by nlinarith
                        positivity
  have hA : A < 0 := by
    simp only [A]; nlinarith [sq_nonneg (n ^ 2 - 1)]
  have hAB : A ^ 2 ≤ B ^ 2 := by
    have e : B ^ 2 - A ^ 2 = 27 * (m - 1) ^ 4 * (32 * m - 27) := by
      simp only [B, A]
      rw [mul_pow, hs2]; simp only [m]; ring
    have : 0 ≤ 27 * (m - 1) ^ 4 * (32 * m - 27) := by
      have : 0 < 32 * m - 27 := by linarith
      positivity
    linarith
  obtain ⟨h1, h2⟩ := abs_le_of_sq_le_sq' hAB hB.le
  refine ⟨hs, hs2, hB, hA, ?_, ?_⟩
  · rw [le_div_iff₀ hB]; linarith
  · rw [div_le_iff₀ hB]; linarith

theorem g66k2_trig (n : ℝ) (hn : 1 < n) :
    0 < Real.cos ((2 * π * (((2 : Fin 3).val : ℕ) : ℝ) + criticalBeta n) / 3) ∧
    Real.cos ((2 * π * (((2 : Fin 3).val : ℕ) : ℝ) + criticalBeta n) / 3) ≤ 1 / 2 ∧
    4 * Real.cos ((2 * π * (((2 : Fin 3).val : ℕ) : ℝ) + criticalBeta n) / 3) ^ 3 -
      3 * Real.cos ((2 * π * (((2 : Fin 3).val : ℕ) : ℝ) + criticalBeta n) / 3) =
      -(27 - 70 * n ^ 2 + 45 * n ^ 4) / (2 * n ^ 2 * (6 * n ^ 2 - 5) * Real.sqrt (6 * n ^ 2 - 5)) := by
  obtain ⟨hs, hs2, hB, hA, hC1, hC2⟩ := g66k2_beta n hn
  have h2 : (((2 : Fin 3).val : ℕ) : ℝ) = 2 := by
    have : ((2 : Fin 3).val) = 2 := rfl
    rw [this]; norm_num
  rw [h2]
  set C := -(27 - 70 * n ^ 2 + 45 * n ^ 4) / (2 * n ^ 2 * (6 * n ^ 2 - 5) * Real.sqrt (6 * n ^ 2 - 5))
    with hCdef
  have hb : criticalBeta n = Real.arccos C := rfl
  have hβ1 : π / 2 < criticalBeta n := by
    rw [hb, Real.arccos_eq_pi_div_two_sub_arcsin]
    have : Real.arcsin C < 0 := Real.arcsin_lt_zero.2 (div_neg_of_neg_of_pos hA hB)
    linarith
  have hβ2 : criticalBeta n ≤ π := by rw [hb]; exact Real.arccos_le_pi _
  have hcb : Real.cos (criticalBeta n) = C := by rw [hb]; exact Real.cos_arccos hC1 hC2
  have hθ' : (2 * π * 2 + criticalBeta n) / 3 = 2 * π - (2 * π - criticalBeta n) / 3 := by ring
  have hxφ : Real.cos ((2 * π * 2 + criticalBeta n) / 3) = Real.cos ((2 * π - criticalBeta n) / 3) := by
    rw [hθ', Real.cos_two_pi_sub]
  refine ⟨?_, ?_, ?_⟩
  · rw [hxφ]; apply Real.cos_pos_of_mem_Ioo; constructor <;> linarith [Real.pi_pos]
  · rw [hxφ, ← Real.cos_pi_div_three]
    apply Real.cos_le_cos_of_nonneg_of_le_pi <;> linarith [Real.pi_pos]
  · have : Real.cos (3 * ((2 * π * 2 + criticalBeta n) / 3)) = Real.cos (criticalBeta n) := by
      have e : 3 * ((2 * π * 2 + criticalBeta n) / 3) = criticalBeta n + ((2 : ℕ) : ℝ) * (2 * π) := by
        push_cast; ring
      rw [e, Real.cos_add_nat_mul_two_pi]
    rw [Real.cos_three_mul, hcb] at this
    linarith

theorem g66k2_cs (c n : ℝ) : criticalSpeed c n 2 = c * criticalSpeed 1 n 2 := by
  simp only [criticalSpeed]; ring

theorem g66k2_core (n : ℝ) (hn : 1 < n) :
    0 < criticalSpeed 1 n 2 ∧ criticalSpeed 1 n 2 < 1 ∧
    (n ^ 2 - 1) * criticalSpeed 1 n 2 ^ 3 + n * criticalSpeed 1 n 2 ^ 2 -
      2 * n ^ 2 * criticalSpeed 1 n 2 + n = 0 := by
  obtain ⟨hs, hs2, hB, hA, hC1, hC2⟩ := g66k2_beta n hn
  obtain ⟨hx0, hx1, h3⟩ := g66k2_trig n hn
  generalize hX : Real.cos ((2 * π * (((2 : Fin 3).val : ℕ) : ℝ) + criticalBeta n) / 3) = x at hx0 hx1 h3
  generalize hS : Real.sqrt (6 * n ^ 2 - 5) = s at hs hs2 hB h3
  have hxi : criticalSpeed 1 n 2 = n * (2 * s * x - 1) / (3 * (n ^ 2 - 1)) := by
    simp only [criticalSpeed]
    rw [hS, hX]
    ring
  rw [hxi]
  have hn0 : 0 < n := by linarith
  have hk : 0 < n ^ 2 - 1 := by nlinarith
  have hBC : (4 * x ^ 3 - 3 * x) * (2 * n ^ 2 * (6 * n ^ 2 - 5) * s) = -(27 - 70 * n ^ 2 + 45 * n ^ 4) := by
    rw [h3]; exact div_mul_cancel₀ _ hB.ne'
  have hs3 : s ^ 3 = s * (6 * n ^ 2 - 5) := by rw [pow_succ, hs2]; ring
  have hQ : n ^ 2 * (2 * s * x - 1) ^ 3 + 3 * n ^ 2 * (2 * s * x - 1) ^ 2 -
      18 * n ^ 2 * (n ^ 2 - 1) * (2 * s * x - 1) + 27 * (n ^ 2 - 1) ^ 2 = 0 := by
    linear_combination hBC + (8 * n ^ 2 * x ^ 3) * hs3
  generalize hY : 2 * s * x - 1 = y at hQ
  have hy1 : -1 < y := by rw [← hY]; have : 0 < s * x := mul_pos hs hx0
                          linarith
  have hy0 : 0 < y := by
    by_contra hneg; push Not at hneg
    have t1 : 0 ≤ n ^ 2 * y ^ 2 * (y + 3) := by
      have : 0 ≤ y + 3 := by linarith
      positivity
    have t2 : 0 ≤ 18 * n ^ 2 * (n ^ 2 - 1) * (-y) := by
      have : 0 ≤ -y := by linarith
      positivity
    have t3 : 0 < 27 * (n ^ 2 - 1) ^ 2 := by positivity
    have : n ^ 2 * y ^ 3 + 3 * n ^ 2 * y ^ 2 = n ^ 2 * y ^ 2 * (y + 3) := by ring
    linarith
  refine ⟨?_, ?_, ?_⟩
  · apply div_pos (mul_pos hn0 hy0); linarith
  · rw [div_lt_one (by linarith)]
    have hys : y ≤ s - 1 := by rw [← hY]; nlinarith
    have hns : n * s < n + 3 * (n ^ 2 - 1) := by
      have hsq : (n * s) ^ 2 < (n + 3 * (n ^ 2 - 1)) ^ 2 := by
        rw [mul_pow, hs2]; nlinarith
      have : 0 < n + 3 * (n ^ 2 - 1) := by linarith
      nlinarith [mul_pos hn0 hs]
    nlinarith
  · field_simp
    linear_combination (n * (1:ℝ)) * hQ

theorem g66k2_vs_eq (c W r : ℝ) (hc : 0 < c) (hr : 0 < r) :
    vortexSpeed c W r = W / Real.sqrt (r ^ 2 + W ^ 2 / c ^ 2) := by
  rw [vortexSpeed, vortexGamma]
  congr 1
  rw [← Real.sqrt_sq hr.le, ← Real.sqrt_mul (by positivity), Real.sqrt_sq hr.le]
  congr 1
  field_simp

theorem g66k2_part1 (c W n : ℝ) (hc : 0 < c) (hW : 0 < W) (hn : 1 < n) :
    0 < criticalRadius c W n ∧
      vortexSpeed c W (criticalRadius c W n) = criticalSpeed c n 2 ∧
      deriv (turningBranch c n (vortexSpeed c W) (-1)) (criticalRadius c W n) = 0 := by
  obtain ⟨hx0, hx1, hcub⟩ := g66k2_core n hn
  have hcs := g66k2_cs c n
  generalize hX : criticalSpeed 1 n 2 = ξ at hx0 hx1 hcub hcs
  have hσ2 : 0 < 1 - ξ ^ 2 := by nlinarith
  set σ := Real.sqrt (1 - ξ ^ 2) with hσ
  have hσ0 : 0 < σ := Real.sqrt_pos.2 hσ2
  have hσsq : σ ^ 2 = 1 - ξ ^ 2 := Real.sq_sqrt hσ2.le
  have hR : criticalRadius c W n = W / (c * ξ) * σ := by
    rw [criticalRadius, hcs]
    congr 2
    congr 1
    field_simp
  set r := criticalRadius c W n with hrdef
  have hr0 : 0 < r := by rw [hR]; positivity
  have hS : Real.sqrt (r ^ 2 + W ^ 2 / c ^ 2) = W / (c * ξ) := by
    rw [hR]
    have : (W / (c * ξ) * σ) ^ 2 + W ^ 2 / c ^ 2 = (W / (c * ξ)) ^ 2 := by
      rw [mul_pow, hσsq]; field_simp; ring
    rw [this, Real.sqrt_sq (by positivity)]
  have hV : vortexSpeed c W r = c * ξ := by
    rw [g66k2_vs_eq c W r hc hr0, hS]; field_simp
  refine ⟨hr0, by rw [hV, hcs], ?_⟩
  -- derivative
  set V : ℝ → ℝ := fun t => W / Real.sqrt (t ^ 2 + W ^ 2 / c ^ 2) with hVdef
  have hev : turningBranch c n (vortexSpeed c W) (-1) =ᶠ[nhds r]
      fun t => t * (n * c + (-1) * V t) / (n * V t + (-1) * c) := by
    filter_upwards [lt_mem_nhds hr0] with t ht
    simp only [turningBranch, hVdef, g66k2_vs_eq c W t hc ht]
  rw [hev.deriv_eq]
  have hpos : r ^ 2 + W ^ 2 / c ^ 2 ≠ 0 := by positivity
  have hSd : HasDerivAt (fun t => Real.sqrt (t ^ 2 + W ^ 2 / c ^ 2))
      ((2 * r) / (2 * Real.sqrt (r ^ 2 + W ^ 2 / c ^ 2))) r := by
    have h1 : HasDerivAt (fun t : ℝ => t ^ 2 + W ^ 2 / c ^ 2) (2 * r) r := by
      simpa using (hasDerivAt_pow 2 r).add_const (W ^ 2 / c ^ 2)
    exact h1.sqrt hpos
  have hSne : Real.sqrt (r ^ 2 + W ^ 2 / c ^ 2) ≠ 0 := by rw [hS]; positivity
  have hVd := (hasDerivAt_const r W).div hSd hSne
  have hVr : V r = c * ξ := by rw [hVdef]; simp only; rw [hS]; field_simp
  have hden : n * V r + (-1) * c ≠ 0 := by
    rw [hVr]
    intro h
    have : n * ξ = 1 := by
      have : c * (n * ξ - 1) = 0 := by linarith
      rcases mul_eq_zero.1 this with h | h
      · exact absurd h hc.ne'
      · linarith
    have hξ : ξ = 1 / n := by field_simp; linarith
    rw [hξ] at hcub
    have hn0 : 0 < n := by linarith
    field_simp at hcub
    have h4 : (n ^ 2 - 1) ^ 2 = 0 := by nlinarith [hcub]
    have h5 := (pow_eq_zero_iff two_ne_zero).1 h4
    nlinarith
  have hT := ((hasDerivAt_id r).mul ((hVd.const_mul (-1)).const_add (n * c))).div
    ((hVd.const_mul n).add_const ((-1) * c)) hden
  have hT' : HasDerivAt (fun t => t * (n * c + (-1) * V t) / (n * V t + (-1) * c)) _ r := hT
  rw [hT'.deriv]
  simp only [Pi.div_apply, Pi.mul_apply, id]
  rw [hS]
  rw [hR]
  field_simp
  have hn0 : 0 < n := by linarith
  rw [mul_zero, div_eq_zero_iff]
  left
  linear_combination (-c) * hcub + c * ξ * (n ^ 2 - 1) * hσsq

theorem g66k2_bounds (n : ℝ) (hn : 1 < n) :
    0 < criticalSpeed 1 n 2 ∧ n * criticalSpeed 1 n 2 ≤ 2 ∧
    1 ≤ 2 * n * criticalSpeed 1 n 2 ∧ 2 * n * criticalSpeed 1 n 2 ≤ 1 + 12 / n ∧
    (criticalSpeed 1 n 2 - n) ^ 2 ≤ n ^ 2 - 1 := by
  obtain ⟨hx0, hx1, hcub⟩ := g66k2_core n hn
  generalize criticalSpeed 1 n 2 = ξ at hx0 hx1 hcub
  have hn0 : 0 < n := by linarith
  have hk : 0 < n ^ 2 - 1 := by nlinarith
  have hξ2 : ξ ^ 2 ≤ 1 := by nlinarith
  have hξ3 : ξ ^ 3 ≤ ξ := by nlinarith
  have hξ30 : 0 ≤ ξ ^ 3 := by positivity
  have hnξ : n * ξ ≤ 2 := by
    have : n ^ 2 * ξ ≤ 2 * n := by nlinarith
    nlinarith
  refine ⟨hx0, hnξ, ?_, ?_, ?_⟩
  · have : n ≤ 2 * n ^ 2 * ξ := by nlinarith
    nlinarith
  · have h1 : 2 * n ^ 2 * ξ - n ≤ 12 / n := by
      have e : 2 * n ^ 2 * ξ - n = (n ^ 2 - 1) * ξ ^ 3 + n * ξ ^ 2 := by linarith
      rw [e]
      have a1 : (n ^ 2 - 1) * ξ ^ 3 ≤ (n * ξ) ^ 2 * ξ := by nlinarith
      have a2 : (n * ξ) ^ 2 * ξ ≤ 4 * ξ := by
        have : (n * ξ) ^ 2 ≤ 4 := by nlinarith
        nlinarith
      have a3 : n * ξ ^ 2 ≤ 2 * ξ := by nlinarith
      have a4 : ξ ≤ 2 / n := by rw [le_div_iff₀ hn0]; linarith
      have : 6 * (2 / n) = 12 / n := by ring
      nlinarith
    have : 2 * n * ξ - 1 ≤ 12 / n ^ 2 := by
      rw [le_div_iff₀ (by positivity)]
      have := mul_le_mul_of_nonneg_left h1 hn0.le
      have e : n * (12 / n) = 12 := by field_simp
      nlinarith
    have : 12 / n ^ 2 ≤ 12 / n := by
      apply div_le_div_of_nonneg_left (by norm_num) hn0; nlinarith
    linarith
  · have e : n * (ξ - n) ^ 2 = (n ^ 2 - 1) * (n - ξ ^ 3) := by linear_combination hcub
    have : n * (ξ - n) ^ 2 ≤ n * (n ^ 2 - 1) := by rw [e]; nlinarith
    exact le_of_mul_le_mul_left this hn0

theorem g66k2_limits (c : ℝ) (hc : 0 < c) :
    Tendsto (fun n => criticalSpeed c n 2) (nhdsWithin 1 (Ioi 1)) (nhds c) ∧
    Tendsto (fun n => criticalSpeed c n 2) atTop (nhds 0) ∧
    Tendsto (fun n => criticalSpeed c n 2 / (c / (2 * n))) atTop (nhds 1) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [← tendsto_sub_nhds_zero_iff]
    have hg : Tendsto (fun n : ℝ => c * (Real.sqrt (n ^ 2 - 1) + (n - 1))) (nhdsWithin 1 (Ioi 1)) (nhds 0) := by
      have : Continuous (fun n : ℝ => c * (Real.sqrt (n ^ 2 - 1) + (n - 1))) := by fun_prop
      have h := this.tendsto 1
      simp at h
      exact h.mono_left nhdsWithin_le_nhds
    refine squeeze_zero_norm' ?_ hg
    filter_upwards [self_mem_nhdsWithin] with n hn
    simp only [Set.mem_Ioi] at hn
    obtain ⟨-, -, -, -, h5⟩ := g66k2_bounds n hn
    rw [g66k2_cs, Real.norm_eq_abs]
    have h6 := Real.abs_le_sqrt h5
    have : c * criticalSpeed 1 n 2 - c = c * ((criticalSpeed 1 n 2 - n) + (n - 1)) := by ring
    rw [this, abs_mul, abs_of_pos hc]
    apply mul_le_mul_of_nonneg_left _ hc.le
    calc |criticalSpeed 1 n 2 - n + (n - 1)| ≤ |criticalSpeed 1 n 2 - n| + |n - 1| := abs_add_le _ _
      _ ≤ _ := by rw [abs_of_pos (by linarith : (0:ℝ) < n - 1)]; linarith
  · have hup : Tendsto (fun n : ℝ => 2 * c / n) atTop (nhds 0) :=
      tendsto_const_nhds.div_atTop tendsto_id
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup ?_ ?_
    · filter_upwards [eventually_gt_atTop 1] with n hn
      obtain ⟨h1, -⟩ := g66k2_bounds n hn
      rw [g66k2_cs]; positivity
    · filter_upwards [eventually_gt_atTop 1] with n hn
      obtain ⟨-, h2, -⟩ := g66k2_bounds n hn
      rw [g66k2_cs, le_div_iff₀ (by linarith)]
      nlinarith
  · have hup : Tendsto (fun n : ℝ => 1 + 12 / n) atTop (nhds 1) := by
      simpa using (tendsto_const_nhds (x := (12:ℝ))).div_atTop tendsto_id |>.const_add 1
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup ?_ ?_
    · filter_upwards [eventually_gt_atTop 1] with n hn
      obtain ⟨-, -, h3, -⟩ := g66k2_bounds n hn
      have hn0 : 0 < n := by linarith
      rw [g66k2_cs, show c * criticalSpeed 1 n 2 / (c / (2 * n)) = 2 * n * criticalSpeed 1 n 2 by
        field_simp]
      exact h3
    · filter_upwards [eventually_gt_atTop 1] with n hn
      obtain ⟨-, -, -, h4, -⟩ := g66k2_bounds n hn
      have hn0 : 0 < n := by linarith
      rw [g66k2_cs, show c * criticalSpeed 1 n 2 / (c / (2 * n)) = 2 * n * criticalSpeed 1 n 2 by
        field_simp]
      exact h4

theorem solution (c W : ℝ) (hc : 0 < c) (hW : 0 < W) :
    (∀ n : ℝ, 1 < n →
      0 < criticalRadius c W n ∧
      vortexSpeed c W (criticalRadius c W n) = criticalSpeed c n 2 ∧
      deriv (turningBranch c n (vortexSpeed c W) (-1)) (criticalRadius c W n) = 0) ∧
    Tendsto (fun n => criticalSpeed c n 2) (nhdsWithin 1 (Ioi 1)) (nhds c) ∧
    Tendsto (fun n => criticalSpeed c n 2) atTop (nhds 0) ∧
    Tendsto (fun n => criticalSpeed c n 2 / (c / (2 * n))) atTop (nhds 1) := by
  exact ⟨fun n hn => g66k2_part1 c W n hc hW hn, g66k2_limits c hc⟩
