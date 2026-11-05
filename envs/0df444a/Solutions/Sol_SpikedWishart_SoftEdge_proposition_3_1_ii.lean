-- Prove2me | solution 1 for SpikedWishart.SoftEdge.proposition_3_1_ii
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-04T07:15:50.826868+00:00
-- url     : https://prove2.me/submissions/2b5c147c-2ce2-491f-8122-85d72a10c0ce

import Mathlib
import Definitions.Def_SpikedWishart_SoftEdge_Airy
import Definitions.Def_SpikedWishart_SoftEdge_Kernels
import Theorems.Thm_SpikedWishart_SoftEdge_circle_eq_polygonJ
import Theorems.Thm_SpikedWishart_SoftEdge_J_near_ray
import Theorems.Thm_SpikedWishart_SoftEdge_J_conn_piece
import Theorems.Thm_SpikedWishart_SoftEdge_J_far_all
import Theorems.Thm_SpikedWishart_SoftEdge_Jinf_vertex_shift
import Theorems.Thm_SpikedWishart_SoftEdge_lemma_3_2

set_option linter.all false
set_option Elab.async false

set_option autoImplicit false

namespace P31

open Complex SpikedWishart.SoftEdge

/-- Cubic Taylor remainder of `log (1 + x)` for `‖x‖ ≤ 1/2`. -/
theorem log_one_add_cubic (x : ℂ) (hx : ‖x‖ ≤ 1 / 2) :
    ‖log (1 + x) - (x - x ^ 2 / 2 + x ^ 3 / 3)‖ ≤ ‖x‖ ^ 4 / 2 := by
  have hx1 : ‖x‖ < 1 := by linarith only [hx]
  have h := Complex.norm_log_sub_logTaylor_le 3 hx1
  have hT : logTaylor (3 + 1) x = x - x ^ 2 / 2 + x ^ 3 / 3 := by
    simp only [logTaylor, Finset.sum_range_succ, Finset.sum_range_zero]
    push_cast
    ring
  rw [hT] at h
  refine h.trans ?_
  have hn : 0 ≤ ‖x‖ := norm_nonneg x
  have h1 : (1 - ‖x‖)⁻¹ ≤ 2 := by
    rw [inv_le_comm₀ (by linarith only [hx1]) (by norm_num)]; linarith only [hx]
  have h4 : 0 ≤ ‖x‖ ^ 4 := by positivity
  norm_num
  nlinarith [mul_le_mul_of_nonneg_left h1 h4]

theorem nu_cube (γ : ℝ) (hγ : 0 < γ) : nu γ ^ 3 = (1 + γ) ^ 4 / γ ^ 3 := by
  unfold nu
  rw [div_pow, ← Real.rpow_natCast ((1 + γ) ^ (4 / 3 : ℝ)), ← Real.rpow_mul (by linarith only [hγ])]
  norm_num

/-- `f(pc + w) - f(pc)` through `log (1 + ·)` of the two scaled increments. -/
theorem fFn_sub_pc (γ q : ℝ) (hγ : 0 < γ) (w : ℂ)
    (ha : ‖w * (((γ : ℂ) + 1) / γ)‖ < 1) (hb : ‖-(w * ((γ : ℂ) + 1))‖ < 1) :
    fFn γ q ((pc γ : ℂ) + w) - fFn γ q (pc γ) =
      -(mu γ : ℂ) * w + log (1 + w * (((γ : ℂ) + 1) / γ)) -
        (1 / (γ : ℂ) ^ 2) * log (1 + -(w * ((γ : ℂ) + 1))) := by
  have hγ1 : (0 : ℝ) < γ + 1 := by linarith only [hγ]
  have hpc : 0 < pc γ := div_pos hγ hγ1
  have hpc1 : 0 < 1 - pc γ := by
    unfold pc; rw [sub_pos, div_lt_one hγ1]; linarith only []
  have hγc : (γ : ℂ) ≠ 0 := by exact_mod_cast hγ.ne'
  have hγ1c : (γ : ℂ) + 1 ≠ 0 := by exact_mod_cast hγ1.ne'
  have hne1 : (1 : ℂ) + w * (((γ : ℂ) + 1) / γ) ≠ 0 := by
    intro h0
    have : ‖w * (((γ : ℂ) + 1) / γ)‖ = 1 := by
      rw [show w * (((γ : ℂ) + 1) / γ) = -1 by linear_combination h0]; simp
    linarith only [ha, this]
  have hne2 : (1 : ℂ) + -(w * ((γ : ℂ) + 1)) ≠ 0 := by
    intro h0
    have : ‖-(w * ((γ : ℂ) + 1))‖ = 1 := by
      rw [show -(w * ((γ : ℂ) + 1)) = -1 by linear_combination h0]; simp
    linarith only [hb, this]
  have e1 : (pc γ : ℂ) + w = ((pc γ : ℝ) : ℂ) * (1 + w * (((γ : ℂ) + 1) / γ)) := by
    unfold pc; push_cast; field_simp; try ring
  have e2 : (1 : ℂ) - ((pc γ : ℂ) + w) = ((1 - pc γ : ℝ) : ℂ) * (1 + -(w * ((γ : ℂ) + 1))) := by
    unfold pc; push_cast; field_simp; try ring
  have e3 : (1 : ℂ) - (pc γ : ℂ) = ((1 - pc γ : ℝ) : ℂ) := by push_cast; ring
  unfold fFn
  rw [e2, e1, e3, log_ofReal_mul hpc hne1, log_ofReal_mul hpc1 hne2, ← ofReal_log hpc.le,
    ← ofReal_log hpc1.le]
  unfold pc; push_cast; field_simp; ring

/-- N1 (BBP (143)-(145)): uniform cubic Taylor bound of `f` at the double critical point `p_c`. -/
theorem fFn_cubic_taylor (γ₀ γ q : ℝ) (z : ℂ) (h1 : 1 ≤ γ) (h2 : γ ≤ γ₀)
    (hz : ‖z - (pc γ : ℂ)‖ ≤ 1 / (2 * (γ₀ + 1))) :
    ‖fFn γ q z - fFn γ q (pc γ) - ((nu γ ^ 3 / 3 : ℝ) : ℂ) * (z - pc γ) ^ 3‖ ≤
      (16 + (γ₀ + 1) ^ 4) / 2 * ‖z - (pc γ : ℂ)‖ ^ 4 := by
  have hγ : 0 < γ := by linarith only [h1]
  have hγ1 : (0 : ℝ) < γ + 1 := by linarith only [hγ]
  have hγ01 : (0 : ℝ) < γ₀ + 1 := by linarith only [h1, h2]
  set w : ℂ := z - (pc γ : ℂ) with hw
  have hzw : z = (pc γ : ℂ) + w := by rw [hw]; ring
  have hwn : 0 ≤ ‖w‖ := norm_nonneg w
  have hγc : (γ : ℂ) ≠ 0 := by exact_mod_cast hγ.ne'
  -- norms of the two increments
  have hna : ‖w * (((γ : ℂ) + 1) / γ)‖ = ‖w‖ * ((γ + 1) / γ) := by
    rw [norm_mul, show ((γ : ℂ) + 1) / γ = (((γ + 1) / γ : ℝ) : ℂ) by push_cast; ring,
      norm_real, Real.norm_of_nonneg (by positivity)]
  have hnb : ‖-(w * ((γ : ℂ) + 1))‖ = ‖w‖ * (γ + 1) := by
    rw [norm_neg, norm_mul, show (γ : ℂ) + 1 = ((γ + 1 : ℝ) : ℂ) by push_cast; ring,
      norm_real, Real.norm_of_nonneg hγ1.le]
  have hq1 : (γ + 1) / γ ≤ 2 := by rw [div_le_iff₀ hγ]; linarith only [h1]
  have hq0 : 0 ≤ (γ + 1) / γ := by positivity
  have hδ : ‖w‖ * (2 * (γ₀ + 1)) ≤ 1 := by
    rw [hw]; rwa [le_div_iff₀ (by positivity)] at hz
  have ha2 : ‖w * (((γ : ℂ) + 1) / γ)‖ ≤ 1 / 2 := by
    rw [hna]
    have e1 : ‖w‖ * ((γ + 1) / γ) ≤ ‖w‖ * 2 := mul_le_mul_of_nonneg_left hq1 hwn
    have e2 : ‖w‖ * 4 ≤ ‖w‖ * (2 * (γ₀ + 1)) :=
      mul_le_mul_of_nonneg_left (by linarith only [h1, h2]) hwn
    linarith only [e1, e2, hδ]
  have hb2 : ‖-(w * ((γ : ℂ) + 1))‖ ≤ 1 / 2 := by
    rw [hnb]
    have e1 : ‖w‖ * (γ + 1) ≤ ‖w‖ * (γ₀ + 1) := mul_le_mul_of_nonneg_left (by linarith only [h2]) hwn
    have e2 : ‖w‖ * (2 * (γ₀ + 1)) = 2 * (‖w‖ * (γ₀ + 1)) := by ring
    linarith only [e1, e2, hδ]
  rw [hzw, fFn_sub_pc γ q hγ w (by linarith only [ha2]) (by linarith only [hb2])]
  have hA := log_one_add_cubic _ ha2
  have hB := log_one_add_cubic _ hb2
  have hν : ((nu γ ^ 3 / 3 : ℝ) : ℂ) = ((1 : ℂ) + γ) ^ 4 / (3 * (γ : ℂ) ^ 3) := by
    rw [nu_cube γ hγ]; push_cast; ring
  have hμ : (mu γ : ℂ) = (((1 : ℂ) + γ) / γ) ^ 2 := by unfold mu; push_cast; ring
  set a : ℂ := w * (((γ : ℂ) + 1) / γ) with ha
  set b : ℂ := -(w * ((γ : ℂ) + 1)) with hb
  have key : -(mu γ : ℂ) * w + log (1 + a) - 1 / (γ : ℂ) ^ 2 * log (1 + b) -
      ((nu γ ^ 3 / 3 : ℝ) : ℂ) * w ^ 3 =
      (log (1 + a) - (a - a ^ 2 / 2 + a ^ 3 / 3)) -
        (1 / (γ : ℂ) ^ 2) * (log (1 + b) - (b - b ^ 2 / 2 + b ^ 3 / 3)) := by
    rw [hν, hμ, ha, hb]; field_simp; ring
  rw [key]
  have hg2 : ‖(1 / (γ : ℂ) ^ 2)‖ ≤ 1 := by
    rw [norm_div, norm_one, norm_pow, norm_real, Real.norm_of_nonneg hγ.le]
    rw [div_le_one (by positivity)]; exact one_le_pow₀ h1
  have hg2' : 0 ≤ ‖(1 / (γ : ℂ) ^ 2)‖ := norm_nonneg _
  calc _ ≤ ‖log (1 + a) - (a - a ^ 2 / 2 + a ^ 3 / 3)‖ +
        ‖(1 / (γ : ℂ) ^ 2)‖ * ‖log (1 + b) - (b - b ^ 2 / 2 + b ^ 3 / 3)‖ := by
          refine (norm_sub_le _ _).trans ?_; rw [norm_mul]
    _ ≤ ‖a‖ ^ 4 / 2 + 1 * (‖b‖ ^ 4 / 2) := by
          exact add_le_add hA (mul_le_mul hg2 hB (norm_nonneg _) zero_le_one)
    _ ≤ (16 + (γ₀ + 1) ^ 4) / 2 * ‖w‖ ^ 4 := by
          rw [hna, hnb]
          have e1 : (‖w‖ * ((γ + 1) / γ)) ^ 4 ≤ (‖w‖ * 2) ^ 4 :=
            pow_le_pow_left₀ (by positivity) (mul_le_mul_of_nonneg_left hq1 hwn) 4
          have e2 : (‖w‖ * (γ + 1)) ^ 4 ≤ (‖w‖ * (γ₀ + 1)) ^ 4 :=
            pow_le_pow_left₀ (by positivity) (mul_le_mul_of_nonneg_left (by linarith only [h2]) hwn) 4
          have e3 : (‖w‖ * 2) ^ 4 = 16 * ‖w‖ ^ 4 := by ring
          have e4 : (‖w‖ * (γ₀ + 1)) ^ 4 = (γ₀ + 1) ^ 4 * ‖w‖ ^ 4 := by ring
          linarith only [e1, e2, e3, e4]

theorem nu_cube_ge_one (γ : ℝ) (hγ : 1 ≤ γ) : 1 ≤ nu γ ^ 3 := by
  rw [nu_cube γ (by linarith only [hγ]), le_div_iff₀ (by positivity), one_mul]
  have h1 : γ ^ 3 ≤ (1 + γ) ^ 3 := pow_le_pow_left₀ (by linarith only [hγ]) (by linarith only [hγ]) 3
  have h2 : (1 + γ) ^ 3 ≤ (1 + γ) ^ 4 := pow_le_pow_right₀ (by linarith only [hγ]) (by norm_num)
  linarith only [h1, h2]

/-- Real part of the Taylor bound: `Re (f z - f pc) ≤ (ν³/3) Re ((z - pc)³) + C ‖z - pc‖⁴`. -/
theorem re_fFn_sub_le (γ₀ γ q : ℝ) (z : ℂ) (h1 : 1 ≤ γ) (h2 : γ ≤ γ₀)
    (hz : ‖z - (pc γ : ℂ)‖ ≤ 1 / (2 * (γ₀ + 1))) :
    (fFn γ q z).re - (fFn γ q (pc γ)).re ≤
      nu γ ^ 3 / 3 * ((z - pc γ) ^ 3).re + (16 + (γ₀ + 1) ^ 4) / 2 * ‖z - (pc γ : ℂ)‖ ^ 4 := by
  have h := fFn_cubic_taylor γ₀ γ q z h1 h2 hz
  have hre := (re_le_norm (fFn γ q z - fFn γ q (pc γ) - ((nu γ ^ 3 / 3 : ℝ) : ℂ) * (z - pc γ) ^ 3)).trans h
  simp only [sub_re, re_ofReal_mul] at hre
  linarith only [hre]

/-- N1b (BBP (146)): `Re f(pc + t e^{iπ/3}) - Re f(pc) ≤ -ν³t³/6` for `0 ≤ t ≤ δ₁`. -/
theorem re_f_ray_cubic_decay (γ₀ γ q t : ℝ) (h1 : 1 ≤ γ) (h2 : γ ≤ γ₀) (ht0 : 0 ≤ t)
    (ht : t ≤ min (1 / (2 * (γ₀ + 1))) (1 / (3 * (16 + (γ₀ + 1) ^ 4)))) :
    (fFn γ q ((pc γ : ℂ) + (t : ℂ) * exp ((Real.pi / 3 : ℝ) * I))).re - (fFn γ q (pc γ)).re
      ≤ -(nu γ ^ 3 / 6) * t ^ 3 := by
  have hγ01 : (0 : ℝ) < γ₀ + 1 := by linarith only [h1, h2]
  have hC : (0 : ℝ) < 16 + (γ₀ + 1) ^ 4 := by positivity
  have hn : ‖(pc γ : ℂ) + (t : ℂ) * exp ((Real.pi / 3 : ℝ) * I) - (pc γ : ℂ)‖ = t := by
    rw [add_sub_cancel_left, norm_mul, norm_exp_ofReal_mul_I, mul_one, norm_real,
      Real.norm_of_nonneg ht0]
  have hcube : (((pc γ : ℂ) + (t : ℂ) * exp ((Real.pi / 3 : ℝ) * I) - pc γ) ^ 3).re = -t ^ 3 := by
    rw [add_sub_cancel_left, mul_pow, ← Complex.exp_nat_mul]
    have : ((3 : ℕ) : ℂ) * (((Real.pi / 3 : ℝ) : ℂ) * I) = (Real.pi : ℂ) * I := by
      push_cast; ring
    rw [this, exp_pi_mul_I]
    simp [← ofReal_pow]
  have h := re_fFn_sub_le γ₀ γ q ((pc γ : ℂ) + (t : ℂ) * exp ((Real.pi / 3 : ℝ) * I)) h1 h2
    (by rw [hn]; exact ht.trans (min_le_left _ _))
  rw [hn, hcube] at h
  have hν := nu_cube_ge_one γ h1
  have ht2 : t * (3 * (16 + (γ₀ + 1) ^ 4)) ≤ 1 := by
    have := ht.trans (min_le_right _ _); rwa [le_div_iff₀ (by positivity)] at this
  have ht3 : 0 ≤ t ^ 3 := by positivity
  have : (16 + (γ₀ + 1) ^ 4) / 2 * t ^ 4 ≤ nu γ ^ 3 / 6 * t ^ 3 := by
    have e : (16 + (γ₀ + 1) ^ 4) / 2 * t ^ 4 = (t * (3 * (16 + (γ₀ + 1) ^ 4))) * t ^ 3 / 6 := by ring
    rw [e]
    have e2 : (t * (3 * (16 + (γ₀ + 1) ^ 4))) * t ^ 3 ≤ nu γ ^ 3 * t ^ 3 :=
      mul_le_mul_of_nonneg_right (ht2.trans hν) ht3
    linarith only [e2]
  linarith only [h, this]

end P31

open Complex

namespace P31E2
open SpikedWishart.SoftEdge

/-- `‖Π (1 + eᵢ) - 1‖ ≤ n 2ⁿ η` when every `‖eᵢ‖ ≤ η ≤ 1`. -/
theorem prod_one_add_sub_one {ι : Type*} (s : Finset ι) (e : ι → ℂ) (η : ℝ) (hη0 : 0 ≤ η)
    (hη1 : η ≤ 1) (he : ∀ i ∈ s, ‖e i‖ ≤ η) :
    ‖∏ i ∈ s, (1 + e i) - 1‖ ≤ (s.card : ℝ) * 2 ^ s.card * η := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    have hs : ∀ j ∈ s, ‖e j‖ ≤ η := fun j hj => he j (Finset.mem_insert_of_mem hj)
    have hei : ‖e i‖ ≤ η := he i (Finset.mem_insert_self i s)
    have ih' := ih hs
    rw [Finset.prod_insert hi, Finset.card_insert_of_notMem hi]
    have hsplit : (1 + e i) * ∏ j ∈ s, (1 + e j) - 1 =
        (1 + e i) * (∏ j ∈ s, (1 + e j) - 1) + e i := by ring
    rw [hsplit]
    have h1 : ‖1 + e i‖ ≤ 2 := by
      calc ‖1 + e i‖ ≤ ‖(1 : ℂ)‖ + ‖e i‖ := norm_add_le _ _
        _ ≤ 2 := by rw [norm_one]; linarith only [hη1, hei]
    have hP0 : (0 : ℝ) ≤ (s.card : ℝ) * 2 ^ s.card * η := by positivity
    have h2 : (1 : ℝ) ≤ 2 ^ s.card := one_le_pow₀ (by norm_num)
    calc ‖(1 + e i) * (∏ j ∈ s, (1 + e j) - 1) + e i‖
        ≤ ‖1 + e i‖ * ‖∏ j ∈ s, (1 + e j) - 1‖ + ‖e i‖ := by
          refine (norm_add_le _ _).trans ?_; rw [norm_mul]
      _ ≤ 2 * ((s.card : ℝ) * 2 ^ s.card * η) + η :=
          add_le_add (mul_le_mul h1 ih' (norm_nonneg _) (by norm_num)) hei
      _ ≤ ((s.card + 1 : ℕ) : ℝ) * 2 ^ (s.card + 1) * η := by
          push_cast
          have : η ≤ 2 ^ s.card * η := le_mul_of_one_le_left hη0 h2
          have he2 : ((s.card : ℝ) + 1) * 2 ^ (s.card + 1) * η =
              2 * ((s.card : ℝ) * 2 ^ s.card * η) + 2 * (2 ^ s.card * η) := by ring
          linarith only [hη0, this, he2]

/-- E2 (BBP (150)): `g(p)/g(z) = 1 + O(|z - p|)` near `p`, uniformly in the spikes `π_j` (`j ≥ k`)
staying at distance `≥ d` to the right of `p`, and `1 - p ≥ d`. -/
theorem gFn_ratio_bound {r : ℕ} (k : ℕ) (π : Fin r → ℝ) (p d : ℝ) (z : ℂ) (hd : 0 < d)
    (h1 : d ≤ 1 - p) (hπ : ∀ j : Fin r, k ≤ (j : ℕ) → d ≤ π j - p) (hz : ‖z - p‖ ≤ d / 2) :
    ‖gFn k π (p : ℂ) / gFn k π z - 1‖ ≤
      ((r : ℝ) * 2 ^ r * (2 + (r : ℝ) * 2 ^ r) * (2 / d)) * ‖z - p‖ := by
  classical
  set S := Finset.univ.filter (fun j : Fin r => k ≤ (j : ℕ)) with hS
  set η : ℝ := 2 * ‖z - p‖ / d with hη
  have hη0 : 0 ≤ η := by positivity
  have hη1 : η ≤ 1 := by rw [hη, div_le_one hd]; linarith only [hz]
  have hzp0 : 0 ≤ ‖z - p‖ := norm_nonneg _
  -- distances
  have h1p : (0 : ℝ) < 1 - p := by linarith only [hd, h1]
  have h1z : d / 2 ≤ ‖(1 : ℂ) - z‖ := by
    have : ‖((1 - p : ℝ) : ℂ)‖ ≤ ‖(1 : ℂ) - z‖ + ‖z - p‖ := by
      have := norm_add_le ((1 : ℂ) - z) (z - p)
      rw [show (1 : ℂ) - z + (z - p) = ((1 - p : ℝ) : ℂ) by push_cast; ring] at this; exact this
    rw [norm_real, Real.norm_of_nonneg h1p.le] at this; linarith only [h1, hz, this]
  have hπz : ∀ j ∈ S, d / 2 ≤ ‖(π j : ℂ) - z‖ := by
    intro j hj
    have hj' : d ≤ π j - p := hπ j (Finset.mem_filter.mp hj).2
    have : ‖((π j - p : ℝ) : ℂ)‖ ≤ ‖(π j : ℂ) - z‖ + ‖z - p‖ := by
      have := norm_add_le ((π j : ℂ) - z) (z - p)
      rw [show (π j : ℂ) - z + (z - p) = ((π j - p : ℝ) : ℂ) by push_cast; ring] at this
      exact this
    rw [norm_real, Real.norm_of_nonneg (by linarith only [hz, hzp0, hj'])] at this; linarith only [hz, hj', this]
  have hd2 : 0 < d / 2 := by linarith only [hd]
  have h1z0 : (1 : ℂ) - z ≠ 0 := by
    intro h; rw [h, norm_zero] at h1z; linarith only [h1z, hd2]
  have hπz0 : ∀ j ∈ S, (π j : ℂ) - z ≠ 0 := by
    intro j hj h; have := hπz j hj; rw [h, norm_zero] at this; linarith only [hd2, this]
  have h1p0 : (1 : ℂ) - (p : ℂ) ≠ 0 := by
    rw [show (1 : ℂ) - (p : ℂ) = ((1 - p : ℝ) : ℂ) by push_cast; ring]
    exact_mod_cast h1p.ne'
  -- the factorisation g(p)/g(z) = A * B
  set e0 : ℂ := -(z - p) / (1 - p) with he0
  set e : Fin r → ℂ := fun j => (z - p) / ((π j : ℂ) - z) with he
  have hA : ((1 : ℂ) - z) / (1 - p) = 1 + e0 := by
    rw [he0]; field_simp; ring
  have hB : ∀ j ∈ S, ((π j : ℂ) - p) / ((π j : ℂ) - z) = 1 + e j := by
    intro j hj; rw [he]; field_simp [hπz0 j hj]; ring
  have hfac : gFn k π (p : ℂ) / gFn k π z =
      (∏ i ∈ Finset.range r, (1 + e0)) * ∏ j ∈ S, (1 + e j) := by
    rw [Finset.prod_const, Finset.card_range, ← hA, ← Finset.prod_congr rfl hB,
      Finset.prod_div_distrib]
    unfold gFn
    have hPz : ∏ j ∈ S, ((π j : ℂ) - z) ≠ 0 := Finset.prod_ne_zero_iff.mpr hπz0
    rw [← hS, div_pow]
    field_simp
  -- bounds on the pieces
  have he0b : ‖e0‖ ≤ η := by
    rw [he0, norm_div, norm_neg, hη]
    rw [show (1 : ℂ) - (p : ℂ) = ((1 - p : ℝ) : ℂ) by push_cast; ring, norm_real,
      Real.norm_of_nonneg h1p.le, div_le_div_iff₀ h1p hd]
    nlinarith
  have heb : ∀ j ∈ S, ‖e j‖ ≤ η := by
    intro j hj
    have hp : 0 < ‖(π j : ℂ) - z‖ := by linarith [hπz j hj]
    simp only [he]
    rw [norm_div, hη, div_le_div_iff₀ hp hd]
    nlinarith [hπz j hj]
  have hAb := prod_one_add_sub_one (Finset.range r) (fun _ => e0) η hη0 hη1 (fun _ _ => he0b)
  have hBb := prod_one_add_sub_one S e η hη0 hη1 heb
  rw [Finset.card_range] at hAb
  have hcard : (S.card : ℝ) * 2 ^ S.card ≤ (r : ℝ) * 2 ^ r := by
    have hc : S.card ≤ r := by
      calc S.card ≤ (Finset.univ : Finset (Fin r)).card := Finset.card_filter_le _ _
        _ = r := by simp
    have h2 : (2 : ℝ) ^ S.card ≤ 2 ^ r := pow_le_pow_right₀ (by norm_num) hc
    have h3 : (S.card : ℝ) ≤ r := by exact_mod_cast hc
    exact mul_le_mul h3 h2 (by positivity) (by positivity)
  set P : ℂ := ∏ i ∈ Finset.range r, (1 + e0)
  set Q : ℂ := ∏ j ∈ S, (1 + e j)
  set R : ℝ := (r : ℝ) * 2 ^ r with hR
  have hR0 : 0 ≤ R := by positivity
  have hP1 : ‖P - 1‖ ≤ R * η := hAb
  have hQ1 : ‖Q - 1‖ ≤ R * η := hBb.trans (mul_le_mul_of_nonneg_right hcard hη0)
  have hPn : ‖P‖ ≤ 1 + R := by
    have := norm_le_norm_add_norm_sub' P 1
    rw [norm_one] at this; linarith only [this, hP1, mul_le_of_le_one_right hR0 hη1]
  rw [hfac]
  have hsplit : P * Q - 1 = P * (Q - 1) + (P - 1) := by ring
  rw [hsplit]
  calc ‖P * (Q - 1) + (P - 1)‖ ≤ ‖P‖ * ‖Q - 1‖ + ‖P - 1‖ := by
        refine (norm_add_le _ _).trans ?_; rw [norm_mul]
    _ ≤ (1 + R) * (R * η) + R * η :=
        add_le_add (mul_le_mul hPn hQ1 (norm_nonneg _) (by positivity)) hP1
    _ = (R * (2 + R) * (2 / d)) * ‖z - p‖ := by rw [hη]; field_simp; ring

end P31E2

open Complex

namespace P31J3
open SpikedWishart.SoftEdge MeasureTheory

/-- The `𝓙` integrand (BBP (104)) as a function of `z`. -/
noncomputable def hJ {r : ℕ} (γ q v : ℝ) (M k : ℕ) (π : Fin r → ℝ) (z : ℂ) : ℂ :=
  exp (((nu γ * (M : ℝ) ^ (1 / 3 : ℝ) * v : ℝ) : ℂ) * (z - q)) * exp (-(M : ℂ) * fFn γ q z) *
    (((pc γ : ℂ) - z) ^ k * gFn k π z)

/-- Log-free form of the `𝓙` integrand (`γ² = M/N`, `r ≤ N`): entire apart from a pole at `0`. -/
noncomputable def hJT {r : ℕ} (γ q v : ℝ) (M N k : ℕ) (π : Fin r → ℝ) (z : ℂ) : ℂ :=
  exp (((nu γ * (M : ℝ) ^ (1 / 3 : ℝ) * v : ℝ) : ℂ) * (z - q)) *
      exp ((M : ℂ) * (mu γ : ℂ) * (z - q)) * (1 - z) ^ (N - r) *
      (((pc γ : ℂ) - z) ^ k *
        ∏ j ∈ Finset.univ.filter (fun j : Fin r => k ≤ (j : ℕ)), ((π j : ℂ) - z)) / z ^ M

theorem exp_neg_M_fFn (γ q : ℝ) (M N : ℕ) (hM : 0 < M) (hN : 0 < N) (hγ : γ ^ 2 = (M : ℝ) / N)
    (z : ℂ) (hz0 : z ≠ 0) (hz1 : 1 - z ≠ 0) :
    exp (-(M : ℂ) * fFn γ q z) = exp ((M : ℂ) * (mu γ : ℂ) * (z - q)) * (1 - z) ^ N / z ^ M := by
  have hM' : (M : ℂ) ≠ 0 := by exact_mod_cast hM.ne'
  have hN' : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  have hγc : (γ : ℂ) ^ 2 = (((M : ℝ) / N : ℝ) : ℂ) := by rw [← hγ]; push_cast; ring
  have hMN : (M : ℂ) * (1 / (γ : ℂ) ^ 2) = N := by
    rw [hγc]; push_cast; field_simp
  unfold fFn
  have e : -(M : ℂ) * (-(mu γ : ℂ) * (z - q) + log z - (1 / (γ : ℂ) ^ 2) * log (1 - z)) =
      ((M : ℂ) * (mu γ : ℂ) * (z - q) + N * log (1 - z)) - M * log z := by
    rw [← hMN]; ring
  rw [e, exp_sub, exp_add, exp_nat_mul, exp_nat_mul, exp_log hz0, exp_log hz1]

theorem hJ_eq_hJT {r : ℕ} (γ q v : ℝ) (M N k : ℕ) (π : Fin r → ℝ) (hM : 0 < M) (hN : 0 < N)
    (hrN : r ≤ N) (hγ : γ ^ 2 = (M : ℝ) / N) (z : ℂ) (hz0 : z ≠ 0) (hz1 : 1 - z ≠ 0) :
    hJ γ q v M k π z = hJT γ q v M N k π z := by
  unfold hJ hJT gFn
  rw [exp_neg_M_fFn γ q M N hM hN hγ z hz0 hz1, ← pow_sub_mul_pow (1 - z) hrN]
  have h1 : (1 - z) ^ r ≠ 0 := pow_ne_zero _ hz1
  have h2 : z ^ M ≠ 0 := pow_ne_zero _ hz0
  field_simp

theorem hJT_differentiableAt {r : ℕ} (γ q v : ℝ) (M N k : ℕ) (π : Fin r → ℝ) (z : ℂ)
    (hz0 : z ≠ 0) : DifferentiableAt ℂ (hJT γ q v M N k π) z := by
  unfold hJT
  have hp : DifferentiableAt ℂ (fun z : ℂ =>
      ∏ j ∈ Finset.univ.filter (fun j : Fin r => k ≤ (j : ℕ)), ((π j : ℂ) - z)) z :=
    by fun_prop
  have hn : DifferentiableAt ℂ (fun z : ℂ =>
      exp (((nu γ * (M : ℝ) ^ (1 / 3 : ℝ) * v : ℝ) : ℂ) * (z - q)) *
        exp ((M : ℂ) * (mu γ : ℂ) * (z - q)) * (1 - z) ^ (N - r) * ((pc γ : ℂ) - z) ^ k) z := by
    fun_prop
  have hnum := hn.mul hp
  have hd : DifferentiableAt ℂ (fun z : ℂ => z ^ M) z := by fun_prop
  have e : (fun z : ℂ => exp (((nu γ * (M : ℝ) ^ (1 / 3 : ℝ) * v : ℝ) : ℂ) * (z - q)) *
      exp ((M : ℂ) * (mu γ : ℂ) * (z - q)) * (1 - z) ^ (N - r) *
      (((pc γ : ℂ) - z) ^ k *
        ∏ j ∈ Finset.univ.filter (fun j : Fin r => k ≤ (j : ℕ)), ((π j : ℂ) - z)) / z ^ M) =
      fun z : ℂ => (exp (((nu γ * (M : ℝ) ^ (1 / 3 : ℝ) * v : ℝ) : ℂ) * (z - q)) *
        exp ((M : ℂ) * (mu γ : ℂ) * (z - q)) * (1 - z) ^ (N - r) * ((pc γ : ℂ) - z) ^ k *
        ∏ j ∈ Finset.univ.filter (fun j : Fin r => k ≤ (j : ℕ)), ((π j : ℂ) - z)) / z ^ M := by
    funext w; ring
  rw [e]
  exact hnum.div hd (pow_ne_zero _ hz0)

theorem hJT_differentiableOn {r : ℕ} (γ q v : ℝ) (M N k : ℕ) (π : Fin r → ℝ) :
    DifferentiableOn ℂ (hJT γ q v M N k π) {z : ℂ | z.im ≠ 0 ∨ z.re < 0 ∨ 0 < z.re} := by
  intro z hz
  refine (hJT_differentiableAt γ q v M N k π z ?_).differentiableWithinAt
  intro h
  rw [h] at hz
  simp only [Set.mem_setOf_eq, zero_im, zero_re] at hz
  rcases hz with hz | hz | hz
  · exact hz rfl
  · exact lt_irrefl _ hz
  · exact lt_irrefl _ hz

theorem hJ_continuousOn {r : ℕ} (γ q v : ℝ) (M N k : ℕ) (π : Fin r → ℝ) (hM : 0 < M)
    (hN : 0 < N) (hrN : r ≤ N) (hγ : γ ^ 2 = (M : ℝ) / N) (s : Set ℂ)
    (hs : ∀ z ∈ s, z ≠ 0 ∧ 1 - z ≠ 0) :
    ContinuousOn (hJ γ q v M k π) s := by
  have hc : ContinuousOn (hJT γ q v M N k π) s := fun z hz =>
    (hJT_differentiableAt γ q v M N k π z (hs z hz).1).continuousAt.continuousWithinAt
  refine hc.congr (fun z hz => ?_)
  exact hJ_eq_hJT γ q v M N k π hM hN hrN hγ z (hs z hz).1 (hs z hz).2

end P31J3

namespace P31Hd
open SpikedWishart.SoftEdge MeasureTheory

/-- Cubic decay at the start of the far ray, `𝓙` side: `Re(-f)(p_c + δω₂) ≤ Re(-f)(p_c) - δ³/6`. -/
theorem hdecJ (γ q δ C₁ : ℝ) (hν : 1 ≤ nu γ) (hδ : 0 < δ) (hC : C₁ * δ ≤ 1 / 6)
    (hT : ‖fFn γ q ((pc γ : ℂ) + (δ : ℂ) * exp (((2 * Real.pi / 3 : ℝ) : ℂ) * I)) - fFn γ q (pc γ) -
      ((nu γ ^ 3 / 3 : ℝ) : ℂ) * ((pc γ : ℂ) + (δ : ℂ) * exp (((2 * Real.pi / 3 : ℝ) : ℂ) * I) -
        pc γ) ^ 3‖ ≤
      C₁ * ‖(pc γ : ℂ) + (δ : ℂ) * exp (((2 * Real.pi / 3 : ℝ) : ℂ) * I) - pc γ‖ ^ 4) :
    (-fFn γ q ((pc γ : ℂ) + (δ : ℂ) * exp (((2 * Real.pi / 3 : ℝ) : ℂ) * I))).re -
      (-fFn γ q (pc γ)).re ≤ -(δ ^ 3 / 6) := by
  set z : ℂ := (pc γ : ℂ) + (δ : ℂ) * exp (((2 * Real.pi / 3 : ℝ) : ℂ) * I) with hz
  have hn : ‖z - pc γ‖ = δ := by
    rw [hz, add_sub_cancel_left, norm_mul, norm_exp_ofReal_mul_I, mul_one, norm_real,
      Real.norm_of_nonneg hδ.le]
  have hcube : (z - pc γ) ^ 3 = ((δ ^ 3 : ℝ) : ℂ) := by
    rw [hz, add_sub_cancel_left, mul_pow, ← Complex.exp_nat_mul]
    have : ((3 : ℕ) : ℂ) * (((2 * Real.pi / 3 : ℝ) : ℂ) * I) = 2 * (Real.pi : ℂ) * I := by
      push_cast; ring
    rw [this, exp_two_pi_mul_I]; push_cast; ring
  rw [hn, hcube] at hT
  have hre := Complex.re_le_norm
    (-(fFn γ q z - fFn γ q (pc γ) - ((nu γ ^ 3 / 3 : ℝ) : ℂ) * ((δ ^ 3 : ℝ) : ℂ)))
  rw [norm_neg] at hre
  have e : (-(fFn γ q z - fFn γ q (pc γ) - ((nu γ ^ 3 / 3 : ℝ) : ℂ) * ((δ ^ 3 : ℝ) : ℂ))).re =
      (-fFn γ q z).re - (-fFn γ q (pc γ)).re + nu γ ^ 3 / 3 * δ ^ 3 := by
    rw [← ofReal_mul]; simp only [neg_re, sub_re, ofReal_re]; ring
  rw [e] at hre
  have hν3 : 1 ≤ nu γ ^ 3 := one_le_pow₀ hν
  have hd3 : 0 ≤ δ ^ 3 := by positivity
  have h4 : C₁ * δ ^ 4 ≤ δ ^ 3 / 6 := by
    have : C₁ * δ ^ 4 = (C₁ * δ) * δ ^ 3 := by ring
    rw [this]; nlinarith
  nlinarith

end P31Hd

set_option autoImplicit false

open Complex

namespace P31A2
open SpikedWishart.SoftEdge MeasureTheory

/-! Assembly of part (ii) of proposition_3_1 from the proved pieces, stated as Props
(each Prop is the verbatim statement of a lemma proved in scratch/probe/13dd0fd1_*.lean). -/

noncomputable def hJ {r : ℕ} (γ q v : ℝ) (M k : ℕ) (π : Fin r → ℝ) (z : ℂ) : ℂ :=
  exp (((nu γ * (M : ℝ) ^ (1 / 3 : ℝ) * v : ℝ) : ℂ) * (z - q)) * exp (-(M : ℂ) * fFn γ q z) *
    (((pc γ : ℂ) - z) ^ k * gFn k π z)

noncomputable def hJT {r : ℕ} (γ q v : ℝ) (M N k : ℕ) (π : Fin r → ℝ) (z : ℂ) : ℂ :=
  exp (((nu γ * (M : ℝ) ^ (1 / 3 : ℝ) * v : ℝ) : ℂ) * (z - q)) *
      exp ((M : ℂ) * (mu γ : ℂ) * (z - q)) * (1 - z) ^ (N - r) *
      (((pc γ : ℂ) - z) ^ k *
        ∏ j ∈ Finset.univ.filter (fun j : Fin r => k ≤ (j : ℕ)), ((π j : ℂ) - z)) / z ^ M

noncomputable def phiJ (v : ℝ) (k : ℕ) (a : ℂ) : ℂ := exp ((v : ℂ) * a - a ^ 3 / 3) * a ^ k

/-- `circle_eq_polygonJ` (13dd0fd1_K3.lean). -/
def K3J : Prop := ∀ (h : ℂ → ℂ) (c ρ : ℝ), c - ρ < 0 → 0 < c + ρ →
    DifferentiableOn ℂ h {z : ℂ | z.im ≠ 0 ∨ z.re < 0 ∨ 0 < z.re} →
    ∀ (p w0 δ ℓ R : ℝ), 0 < w0 → w0 ≤ p → 0 < δ → δ ≤ ℓ → 0 ≤ R → p - ℓ / 2 - R < 0 →
    (∮ z in C((c : ℂ), ρ), h z) =
    -(∫ y in (-(ℓ * (Real.sqrt 3 / 2)))..(ℓ * (Real.sqrt 3 / 2)),
        h (((p - ℓ / 2 - R : ℝ) : ℂ) + (y : ℂ) * I) * I)
      - (∫ x in (0 : ℝ)..R,
          h ((p : ℂ) + (ℓ : ℂ) * exp (((2 * Real.pi / 3 : ℝ) : ℂ) * I) - (x : ℂ)))
      + (∫ t in δ..ℓ, h ((p : ℂ) + (t : ℂ) * exp (((2 * Real.pi / 3 : ℝ) : ℂ) * I)) *
          exp (((2 * Real.pi / 3 : ℝ) : ℂ) * I))
      + (∫ s in (0 : ℝ)..(p - w0),
          h ((w0 : ℂ) + (δ : ℂ) * exp (((2 * Real.pi / 3 : ℝ) : ℂ) * I) + (s : ℂ)))
      + (∫ t in (0 : ℝ)..δ, h ((w0 : ℂ) + (t : ℂ) * exp (((2 * Real.pi / 3 : ℝ) : ℂ) * I)) *
          exp (((2 * Real.pi / 3 : ℝ) : ℂ) * I))
      - (∫ t in (0 : ℝ)..δ, h ((w0 : ℂ) + (t : ℂ) * exp (((-2 * Real.pi / 3 : ℝ) : ℂ) * I)) *
          exp (((-2 * Real.pi / 3 : ℝ) : ℂ) * I))
      - (∫ s in (0 : ℝ)..(p - w0),
          h ((w0 : ℂ) + (δ : ℂ) * exp (((-2 * Real.pi / 3 : ℝ) : ℂ) * I) + (s : ℂ)))
      - (∫ t in δ..ℓ, h ((p : ℂ) + (t : ℂ) * exp (((-2 * Real.pi / 3 : ℝ) : ℂ) * I)) *
          exp (((-2 * Real.pi / 3 : ℝ) : ℂ) * I))
      + (∫ x in (0 : ℝ)..R,
          h ((p : ℂ) + (ℓ : ℂ) * exp (((-2 * Real.pi / 3 : ℝ) : ℂ) * I) - (x : ℂ)))

/-- `near_rayJ` (13dd0fd1_J1.lean). -/
def NearRayJ : Prop := ∀ (ε V₀ C₁ K₂ δ₀ δ θ : ℝ) (k : ℕ), 0 < ε → Real.cos θ = -(1 / 2) →
    Real.sin θ ^ 2 = 3 / 4 → 0 ≤ C₁ → 0 ≤ K₂ → 0 < δ →
    ∃ B : ℝ, 0 ≤ B ∧ ∀ {r : ℕ} (π : Fin r → ℝ) (γ q v m σ : ℝ) (M : ℕ),
      V₀ ≤ v → 1 ≤ m → m ^ 3 = (M : ℝ) → 1 ≤ nu γ → nu γ * (M : ℝ) ^ (1 / 3 : ℝ) = σ →
      σ = nu γ * m → q = pc γ - ε / σ → δ + 2 * ε / σ ≤ δ₀ →
      (C₁ + 2 * K₂) * (nu γ * δ + 2 * ε / m) ≤ 1 / 8 →
      (∀ z : ℂ, ‖z - pc γ‖ ≤ δ₀ → ‖fFn γ q z - fFn γ q (pc γ) -
          ((nu γ ^ 3 / 3 : ℝ) : ℂ) * (z - pc γ) ^ 3‖ ≤ C₁ * ‖z - pc γ‖ ^ 4) →
      (∀ z : ℂ, ‖z - pc γ‖ ≤ δ₀ → gFn k π z ≠ 0 ∧
          ‖gFn k π (pc γ) / gFn k π z - 1‖ ≤ K₂ * ‖z - pc γ‖) →
      gFn k π (pc γ) ≠ 0 →
      ContinuousOn (hJ γ q v M k π) (Metric.closedBall (pc γ : ℂ) δ₀) →
      ‖(ZM γ q M k π)⁻¹ * ((σ / (2 * Real.pi) : ℝ) : ℂ) *
          (∫ t in (0 : ℝ)..δ, hJ γ q v M k π (((pc γ + (-2 * ε) / σ : ℝ) : ℂ) +
            (t : ℂ) * exp ((θ : ℂ) * I)) * exp ((θ : ℂ) * I)) -
        ((Real.exp (ε * v) / (2 * Real.pi) : ℝ) : ℂ) *
          ∫ τ in Set.Ioi (0 : ℝ), phiJ v k (((-2 * ε : ℝ) : ℂ) + (τ : ℂ) * exp ((θ : ℂ) * I)) *
            exp ((θ : ℂ) * I)‖ ≤
        B * Real.exp (-ε * v) / m

/-- `conn_pieceJ` (13dd0fd1_J2.lean). -/
def ConnPieceJ : Prop := ∀ (ε V₀ C₁ K₂ δ₀ δ θ : ℝ) (k : ℕ), 0 < ε → Real.cos θ = -(1 / 2) →
    Real.sin θ ^ 2 = 3 / 4 → 0 ≤ C₁ → 0 ≤ K₂ → 0 < δ →
    ∃ B : ℝ, 0 ≤ B ∧ ∀ {r : ℕ} (π : Fin r → ℝ) (γ q v m σ : ℝ) (M : ℕ),
      V₀ ≤ v → 1 ≤ m → m ^ 3 = (M : ℝ) → 1 ≤ nu γ → nu γ * (M : ℝ) ^ (1 / 3 : ℝ) = σ →
      σ = nu γ * m → q = pc γ - ε / σ → δ + 2 * ε / σ ≤ δ₀ →
      (C₁ + 2 * K₂) * (nu γ * δ + 2 * ε / m) ≤ 1 / 8 → 4 * ε ≤ σ * δ →
      (∀ z : ℂ, ‖z - pc γ‖ ≤ δ₀ → ‖fFn γ q z - fFn γ q (pc γ) -
          ((nu γ ^ 3 / 3 : ℝ) : ℂ) * (z - pc γ) ^ 3‖ ≤ C₁ * ‖z - pc γ‖ ^ 4) →
      (∀ z : ℂ, ‖z - pc γ‖ ≤ δ₀ → gFn k π z ≠ 0 ∧
          ‖gFn k π (pc γ) / gFn k π z - 1‖ ≤ K₂ * ‖z - pc γ‖) →
      gFn k π (pc γ) ≠ 0 →
      ‖(ZM γ q M k π)⁻¹ * ((σ / (2 * Real.pi) : ℝ) : ℂ) *
          ∫ s in (0 : ℝ)..(pc γ - (pc γ + (-2 * ε) / σ)), hJ γ q v M k π
            (((pc γ + (-2 * ε) / σ : ℝ) : ℂ) + (δ : ℂ) * exp ((θ : ℂ) * I) + (s : ℂ))‖ ≤
        B * Real.exp (-ε * v) / m

/-- `far_allJ` (13dd0fd1_J5.lean). -/
def FarAllJ : Prop := ∀ (ε V₀ γ₀ P₀ δ R Nmax d : ℝ) (r k : ℕ), 0 < ε → 1 ≤ γ₀ → 0 ≤ P₀ →
    0 < δ → δ ≤ 1 / (2 * (γ₀ + 1)) → 0 ≤ R → 0 ≤ Nmax → 0 < d → d ≤ P₀ + 1 →
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (π : Fin r → ℝ) (γ q v m σ ℓ : ℝ) (M : ℕ),
      V₀ ≤ v → 1 ≤ m → m ^ 3 = (M : ℝ) → 1 ≤ γ → γ ≤ γ₀ → 0 ≤ nu γ → nu γ ≤ Nmax →
      nu γ * (M : ℝ) ^ (1 / 3 : ℝ) = σ → σ = nu γ * m → q = pc γ - ε / σ → 4 * ε ≤ σ * δ →
      (∀ j : Fin r, k ≤ (j : ℕ) → 0 ≤ π j ∧ π j ≤ P₀) →
      (∀ j : Fin r, k ≤ (j : ℕ) → d ≤ ‖(π j : ℂ) - pc γ‖) → ℓ = 2 * pc γ →
      3 * ε / (nu γ * (M : ℝ) ^ (1 / 3 : ℝ)) ≤ δ →
      StrictAntiOn (fun t : ℝ =>
        (-fFn γ q ((pc γ : ℂ) + (t : ℂ) * exp (((2 * Real.pi / 3 : ℝ) : ℂ) * I))).re)
        (Set.Icc (3 * ε / (nu γ * (M : ℝ) ^ (1 / 3 : ℝ))) (2 * pc γ)) →
      StrictAntiOn (fun x : ℝ =>
        (-fFn γ q ((pc γ : ℂ) + 2 * (pc γ : ℂ) * exp (((2 * Real.pi / 3 : ℝ) : ℂ) * I) -
          (x : ℂ))).re) (Set.Icc 0 R) →
      (∀ y : ℝ, 0 ≤ y → y ≤ Real.sqrt 3 * pc γ →
        (-fFn γ q (-(R : ℂ) + ((Real.sqrt 3 * pc γ - y : ℝ) : ℂ) * I)).re ≤
          (-fFn γ q ((pc γ : ℂ) + 2 * (pc γ : ℂ) * exp (((2 * Real.pi / 3 : ℝ) : ℂ) * I))).re) →
      (-fFn γ q ((pc γ : ℂ) + (δ : ℂ) * exp (((2 * Real.pi / 3 : ℝ) : ℂ) * I))).re -
        (-fFn γ q (pc γ)).re ≤ -(δ ^ 3 / 6) →
      (‖(ZM γ q M k π)⁻¹ * ((σ / (2 * Real.pi) : ℝ) : ℂ) *
          ∫ y in (-(ℓ * (Real.sqrt 3 / 2)))..(ℓ * (Real.sqrt 3 / 2)),
            hJ γ q v M k π (((pc γ - ℓ / 2 - R : ℝ) : ℂ) + (y : ℂ) * I) * I‖ ≤
          B * Real.exp (-ε * v) / m) ∧
      (‖(ZM γ q M k π)⁻¹ * ((σ / (2 * Real.pi) : ℝ) : ℂ) *
          ∫ x in (0 : ℝ)..R, hJ γ q v M k π
            ((pc γ : ℂ) + (ℓ : ℂ) * exp (((2 * Real.pi / 3 : ℝ) : ℂ) * I) - (x : ℂ))‖ ≤
          B * Real.exp (-ε * v) / m) ∧
      (‖(ZM γ q M k π)⁻¹ * ((σ / (2 * Real.pi) : ℝ) : ℂ) *
          ∫ t in δ..ℓ, hJ γ q v M k π ((pc γ : ℂ) + (t : ℂ) * exp (((2 * Real.pi / 3 : ℝ) : ℂ) * I)) *
            exp (((2 * Real.pi / 3 : ℝ) : ℂ) * I)‖ ≤
          B * Real.exp (-ε * v) / m) ∧
      (‖(ZM γ q M k π)⁻¹ * ((σ / (2 * Real.pi) : ℝ) : ℂ) *
          ∫ t in δ..ℓ, hJ γ q v M k π ((pc γ : ℂ) + (t : ℂ) * exp (((-2 * Real.pi / 3 : ℝ) : ℂ) * I)) *
            exp (((-2 * Real.pi / 3 : ℝ) : ℂ) * I)‖ ≤
          B * Real.exp (-ε * v) / m) ∧
      (‖(ZM γ q M k π)⁻¹ * ((σ / (2 * Real.pi) : ℝ) : ℂ) *
          ∫ x in (0 : ℝ)..R, hJ γ q v M k π
            ((pc γ : ℂ) + (ℓ : ℂ) * exp (((-2 * Real.pi / 3 : ℝ) : ℂ) * I) - (x : ℂ))‖ ≤
          B * Real.exp (-ε * v) / m)

/-- `hdecJ` (13dd0fd1_J5.lean). -/
def HdecJ : Prop := ∀ (γ q δ C₁ : ℝ), 1 ≤ nu γ → 0 < δ → C₁ * δ ≤ 1 / 6 →
    ‖fFn γ q ((pc γ : ℂ) + (δ : ℂ) * exp (((2 * Real.pi / 3 : ℝ) : ℂ) * I)) - fFn γ q (pc γ) -
      ((nu γ ^ 3 / 3 : ℝ) : ℂ) * ((pc γ : ℂ) + (δ : ℂ) * exp (((2 * Real.pi / 3 : ℝ) : ℂ) * I) -
        pc γ) ^ 3‖ ≤
      C₁ * ‖(pc γ : ℂ) + (δ : ℂ) * exp (((2 * Real.pi / 3 : ℝ) : ℂ) * I) - pc γ‖ ^ 4 →
    (-fFn γ q ((pc γ : ℂ) + (δ : ℂ) * exp (((2 * Real.pi / 3 : ℝ) : ℂ) * I))).re -
      (-fFn γ q (pc γ)).re ≤ -(δ ^ 3 / 6)

/-- `fFn_cubic_taylor` (13dd0fd1_N1.lean). -/
def Taylor : Prop := ∀ (γ₀ γ q : ℝ) (z : ℂ), 1 ≤ γ → γ ≤ γ₀ →
    ‖z - (pc γ : ℂ)‖ ≤ 1 / (2 * (γ₀ + 1)) →
    ‖fFn γ q z - fFn γ q (pc γ) - ((nu γ ^ 3 / 3 : ℝ) : ℂ) * (z - pc γ) ^ 3‖ ≤
      (16 + (γ₀ + 1) ^ 4) / 2 * ‖z - (pc γ : ℂ)‖ ^ 4

/-- `gFn_ratio_bound` (13dd0fd1_E2.lean). -/
def GRatio : Prop := ∀ {r : ℕ} (k : ℕ) (π : Fin r → ℝ) (p d : ℝ) (z : ℂ), 0 < d →
    d ≤ 1 - p → (∀ j : Fin r, k ≤ (j : ℕ) → d ≤ π j - p) → ‖z - p‖ ≤ d / 2 →
    ‖gFn k π (p : ℂ) / gFn k π z - 1‖ ≤
      ((r : ℝ) * 2 ^ r * (2 + (r : ℝ) * 2 ^ r) * (2 / d)) * ‖z - p‖

/-- `hJ_eq_hJT` (13dd0fd1_J3.lean). -/
def HJeqT : Prop := ∀ {r : ℕ} (γ q v : ℝ) (M N k : ℕ) (π : Fin r → ℝ), 0 < M → 0 < N →
    r ≤ N → γ ^ 2 = (M : ℝ) / N → ∀ z : ℂ, z ≠ 0 → 1 - z ≠ 0 →
    hJ γ q v M k π z = hJT γ q v M N k π z

/-- `hJT_differentiableOn` (13dd0fd1_J3.lean). -/
def HJTdiff : Prop := ∀ {r : ℕ} (γ q v : ℝ) (M N k : ℕ) (π : Fin r → ℝ),
    DifferentiableOn ℂ (hJT γ q v M N k π) {z : ℂ | z.im ≠ 0 ∨ z.re < 0 ∨ 0 < z.re}

/-- `hJ_continuousOn` (13dd0fd1_J3.lean). -/
def HJCont : Prop := ∀ {r : ℕ} (γ q v : ℝ) (M N k : ℕ) (π : Fin r → ℝ), 0 < M → 0 < N →
    r ≤ N → γ ^ 2 = (M : ℝ) / N → ∀ s : Set ℂ, (∀ z ∈ s, z ≠ 0 ∧ 1 - z ≠ 0) →
    ContinuousOn (hJ γ q v M k π) s

/-- `Jinf_vertex` (13dd0fd1_J4.lean). -/
def JinfV : Prop := ∀ (ε : ℝ) (k : ℕ) (c c' v : ℝ), Jinf ε k c v = Jinf ε k c' v

/-- The statement of `lemma_3_2` (32e13a45). -/
def L32 : Prop :=
    (∀ (γ q ε : ℝ) (M : ℕ), 1 ≤ γ → 0 < ε → 0 < M →
      StrictAntiOn
        (fun t : ℝ => (-fFn γ q ((pc γ : ℂ) + (t : ℂ) * exp ((2 * Real.pi / 3 : ℝ) * I))).re)
        (Set.Icc (3 * ε / (nu γ * (M : ℝ) ^ (1 / 3 : ℝ))) (2 * pc γ))) ∧
    (∀ (γ q R : ℝ), 1 ≤ γ →
      StrictAntiOn
        (fun x : ℝ => (-fFn γ q ((pc γ : ℂ) + 2 * pc γ * exp ((2 * Real.pi / 3 : ℝ) * I) - x)).re)
        (Set.Icc 0 R)) ∧
    (∀ γ₀ : ℝ, 1 ≤ γ₀ → ∃ R₀ : ℝ, 0 < R₀ ∧ ∀ (γ q R y : ℝ), 1 ≤ γ → γ ≤ γ₀ → R₀ ≤ R →
      0 ≤ y → y ≤ Real.sqrt 3 * pc γ →
      (-fFn γ q (-(R : ℂ) + ((Real.sqrt 3 * pc γ - y : ℝ) : ℂ) * I)).re ≤
        (-fFn γ q ((pc γ : ℂ) + 2 * pc γ * exp ((2 * Real.pi / 3 : ℝ) * I))).re)

/-! ## elementary helpers -/

theorem norm9J (a b c d e f g h i : ℂ) :
    ‖a - b - c - d + e + f - g - h + i‖ ≤
      ‖a‖ + ‖b‖ + ‖c‖ + ‖d‖ + ‖e‖ + ‖f‖ + ‖g‖ + ‖h‖ + ‖i‖ := by
  have h1 := norm_add_le (a - b - c - d + e + f - g - h) i
  have h2 := norm_sub_le (a - b - c - d + e + f - g) h
  have h3 := norm_sub_le (a - b - c - d + e + f) g
  have h4 := norm_add_le (a - b - c - d + e) f
  have h5 := norm_add_le (a - b - c - d) e
  have h6 := norm_sub_le (a - b - c) d
  have h7 := norm_sub_le (a - b) c
  have h8 := norm_sub_le a b
  linarith

theorem assembleJ (Z S E V Hp Rp Cp Np Nm Cm Rm Hm Iout Iin : ℂ)
    (b1 b2 b3 b4 b5 b6 b7 b8 b9 : ℝ)
    (h1 : ‖Z * S * Np - E * Iout‖ ≤ b1) (h2 : ‖Z * S * Nm - E * Iin‖ ≤ b2)
    (h3 : ‖Z * S * V‖ ≤ b3) (h4 : ‖Z * S * Hp‖ ≤ b4) (h5 : ‖Z * S * Rp‖ ≤ b5)
    (h6 : ‖Z * S * Cp‖ ≤ b6) (h7 : ‖Z * S * Cm‖ ≤ b7) (h8 : ‖Z * S * Rm‖ ≤ b8)
    (h9 : ‖Z * S * Hm‖ ≤ b9) :
    ‖Z * (S * (-V - Hp + Rp + Cp + Np - Nm - Cm - Rm + Hm)) - E * (Iout - Iin)‖ ≤
      b1 + b2 + b3 + b4 + b5 + b6 + b7 + b8 + b9 := by
  have e : Z * (S * (-V - Hp + Rp + Cp + Np - Nm - Cm - Rm + Hm)) - E * (Iout - Iin) =
      (Z * S * Np - E * Iout) - (Z * S * Nm - E * Iin) - Z * S * V - Z * S * Hp +
        Z * S * Rp + Z * S * Cp - Z * S * Cm - Z * S * Rm + Z * S * Hm := by ring
  rw [e]
  have := norm9J (Z * S * Np - E * Iout) (Z * S * Nm - E * Iin) (Z * S * V) (Z * S * Hp)
    (Z * S * Rp) (Z * S * Cp) (Z * S * Cm) (Z * S * Rm) (Z * S * Hm)
  linarith

theorem pt_re (p t θ : ℝ) : ((p : ℂ) + (t : ℂ) * exp ((θ : ℂ) * I)).re = p + t * Real.cos θ := by
  simp [Complex.add_re, Complex.mul_re, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im]

theorem pt_im (p t θ : ℝ) : ((p : ℂ) + (t : ℂ) * exp ((θ : ℂ) * I)).im = t * Real.sin θ := by
  simp [Complex.add_im, Complex.mul_im, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im]

theorem pt2_im (p t θ x : ℝ) :
    ((p : ℂ) + (t : ℂ) * exp ((θ : ℂ) * I) + (x : ℂ)).im = t * Real.sin θ := by
  rw [Complex.add_im, pt_im, Complex.ofReal_im, add_zero]

theorem pt3_im (p t θ x : ℝ) :
    ((p : ℂ) + (t : ℂ) * exp ((θ : ℂ) * I) - (x : ℂ)).im = t * Real.sin θ := by
  rw [Complex.sub_im, pt_im, Complex.ofReal_im, sub_zero]

theorem okJ_im (z : ℂ) (h : z.im ≠ 0) : z ≠ 0 ∧ 1 - z ≠ 0 := by
  refine ⟨fun e => h (by rw [e]; rfl), fun e => h ?_⟩
  have : z = 1 := (sub_eq_zero.mp e).symm
  rw [this]; rfl

theorem okJ_re (z : ℂ) (h : z.re < 0 ∨ (0 < z.re ∧ z.re < 1)) : z ≠ 0 ∧ 1 - z ≠ 0 := by
  constructor
  · intro e; rw [e, Complex.zero_re] at h
    rcases h with h | ⟨h, -⟩ <;> exact lt_irrefl _ h
  · intro e
    have : z = 1 := (sub_eq_zero.mp e).symm
    rw [this, Complex.one_re] at h
    rcases h with h | ⟨-, h⟩ <;> norm_num at h

theorem norm_sub_ofReal (x y : ℝ) : ‖(x : ℂ) - (y : ℂ)‖ = |x - y| := by
  rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]

theorem icongr (f g : ℂ → ℂ) (P : ℝ → ℂ) (w : ℂ) (a b : ℝ)
    (h : ∀ x ∈ Set.uIcc a b, f (P x) = g (P x)) :
    (∫ x in a..b, f (P x) * w) = ∫ x in a..b, g (P x) * w :=
  intervalIntegral.integral_congr (fun x hx => by simp only [h x hx])

theorem icongr0 (f g : ℂ → ℂ) (P : ℝ → ℂ) (a b : ℝ)
    (h : ∀ x ∈ Set.uIcc a b, f (P x) = g (P x)) :
    (∫ x in a..b, f (P x)) = ∫ x in a..b, g (P x) :=
  intervalIntegral.integral_congr (fun x hx => by simp only [h x hx])

/-! ## the assembly of part (ii) -/

set_option maxHeartbeats 2000000 in
theorem part_ii (hK3 : K3J) (hNR : NearRayJ) (hCP : ConnPieceJ) (hFA : FarAllJ) (hDc : HdecJ)
    (hTay : Taylor) (hGR : GRatio) (hEq : HJeqT) (hTd : HJTdiff) (hJc : HJCont) (hJv : JinfV)
    (hL32 : L32) (ε γ₀ c₀ : ℝ) (hε : 0 < ε) (hγ₀ : 1 ≤ γ₀) (hc₀ : 0 < c₀) (r k : ℕ) :
    ∀ V₀ : ℝ, ∃ C c M₀ : ℝ, 0 < C ∧ 0 < c ∧ 0 < M₀ ∧
      ∀ (M N : ℕ) (γ : ℝ) (π : Fin r → ℝ) (cS ρS cJ v : ℝ),
        M₀ ≤ M → r ≤ N → γ = Real.sqrt ((M : ℝ) / (N : ℝ)) → 1 ≤ γ → γ ≤ γ₀ →
        (∀ j : Fin r, (j : ℕ) < k → π j = pc γ) →
        (∀ j : Fin r, k ≤ (j : ℕ) → c₀ ≤ (π j)⁻¹ ∧ (π j)⁻¹ ≤ 1 + γ⁻¹ - c₀) →
        |cS| < ρS → cS + ρS < qM γ ε M →
        cJ < -ε → V₀ ≤ v →
        ‖Jcal γ (qM γ ε M) M k π cS ρS v / ZM γ (qM γ ε M) M k π - Jinf ε k cJ v‖ ≤
          C * Real.exp (-c * v) / (M : ℝ) ^ (1 / 3 : ℝ) := by
  intro V₀
  have hγ01 : (0 : ℝ) < γ₀ + 1 := by linarith only [hγ₀]
  obtain ⟨δ₀, hδ₀⟩ : ∃ x : ℝ, x = 1 / (2 * (γ₀ + 1)) := ⟨_, rfl⟩
  obtain ⟨C₁, hC₁⟩ : ∃ x : ℝ, x = (16 + (γ₀ + 1) ^ 4) / 2 := ⟨_, rfl⟩
  obtain ⟨P₀, hP₀⟩ : ∃ x : ℝ, x = 1 / c₀ := ⟨_, rfl⟩
  obtain ⟨d, hd⟩ : ∃ x : ℝ, x = min (1 / (γ₀ + 1)) (c₀ / 4) := ⟨_, rfl⟩
  obtain ⟨K₂, hK₂⟩ : ∃ x : ℝ, x = (r : ℝ) * 2 ^ r * (2 + (r : ℝ) * 2 ^ r) * (2 / d) := ⟨_, rfl⟩
  obtain ⟨δ₀', hδ₀'⟩ : ∃ x : ℝ, x = min δ₀ (d / 2) := ⟨_, rfl⟩
  obtain ⟨Nmax, hNmax⟩ : ∃ x : ℝ, x = (1 + γ₀) ^ 2 := ⟨_, rfl⟩
  have hδ₀0 : 0 < δ₀ := by rw [hδ₀]; positivity
  have hC₁0 : 0 < C₁ := by rw [hC₁]; positivity
  have hP₀0 : 0 < P₀ := by rw [hP₀]; positivity
  have hd0 : 0 < d := by rw [hd]; exact lt_min (by positivity) (by positivity)
  have hd1 : d ≤ 1 / (γ₀ + 1) := by rw [hd]; exact min_le_left _ _
  have hd2 : d ≤ c₀ / 4 := by rw [hd]; exact min_le_right _ _
  try clear hd
  have hK₂0 : 0 ≤ K₂ := by rw [hK₂]; positivity
  have hδ₀'0 : 0 < δ₀' := by rw [hδ₀']; exact lt_min hδ₀0 (by positivity)
  try clear hδ₀0
  have hδ₀'a : δ₀' ≤ δ₀ := by rw [hδ₀']; exact min_le_left _ _
  have hδ₀'b : δ₀' ≤ d / 2 := by rw [hδ₀']; exact min_le_right _ _
  try clear hδ₀'
  have hNmax0 : 0 < Nmax := by rw [hNmax]; positivity
  have hCK : 0 < C₁ + 2 * K₂ := by linarith only [hC₁0, hK₂0]
  have hdP : d ≤ P₀ + 1 := by
    have : 1 / (γ₀ + 1) ≤ 1 := by rw [div_le_one hγ01]; linarith only [hγ₀]
    linarith only [hP₀0, hd1, this]
  try clear hγ01
  obtain ⟨δ, hδ⟩ : ∃ x : ℝ, x = min (min (δ₀' / 2) (1 / (6 * C₁)))
      (1 / (16 * (C₁ + 2 * K₂) * Nmax)) := ⟨_, rfl⟩
  have hδ0 : 0 < δ := by
    rw [hδ]; exact lt_min (lt_min (by positivity) (by positivity)) (by positivity)
  have hδa : δ ≤ δ₀' / 2 := by rw [hδ]; exact (min_le_left _ _).trans (min_le_left _ _)
  have hδb : δ ≤ 1 / (6 * C₁) := by rw [hδ]; exact (min_le_left _ _).trans (min_le_right _ _)
  have hδc : δ ≤ 1 / (16 * (C₁ + 2 * K₂) * Nmax) := by rw [hδ]; exact min_le_right _ _
  try clear hδ
  have hδδ₀ : δ ≤ δ₀ := by linarith only [hδa, hδ₀'a, hδ₀'0, hδ0]
  have hδq : δ ≤ 1 / 4 := by
    have : δ₀ ≤ 1 / 4 := by
      rw [hδ₀, div_le_div_iff₀ (by positivity) (by norm_num)]; linarith only [hγ₀]
    linarith only [hδδ₀, this]
  try clear δ₀
  try clear hδq
  obtain ⟨R, hR0, hL3⟩ := hL32.2.2 γ₀ hγ₀
  have hs3 : Real.sin (2 * Real.pi / 3) = Real.sqrt 3 / 2 := by
    rw [show 2 * Real.pi / 3 = Real.pi - Real.pi / 3 by ring, Real.sin_pi_sub,
      Real.sin_pi_div_three]
  have hθ1 : Real.cos (2 * Real.pi / 3) = -(1 / 2) := by
    rw [show 2 * Real.pi / 3 = Real.pi - Real.pi / 3 by ring, Real.cos_pi_sub,
      Real.cos_pi_div_three]
  have hθ1' : Real.sin (2 * Real.pi / 3) ^ 2 = 3 / 4 := by
    rw [hs3, div_pow, Real.sq_sqrt (by norm_num)]; norm_num
  try clear hs3
  have hθ2 : Real.cos (-2 * Real.pi / 3) = -(1 / 2) := by
    rw [show -2 * Real.pi / 3 = -(2 * Real.pi / 3) by ring, Real.cos_neg]; exact hθ1
  have hθ2' : Real.sin (-2 * Real.pi / 3) ^ 2 = 3 / 4 := by
    rw [show -2 * Real.pi / 3 = -(2 * Real.pi / 3) by ring, Real.sin_neg, neg_sq]; exact hθ1'
  have hs1 : Real.sin (2 * Real.pi / 3) ≠ 0 := fun h => by rw [h] at hθ1'; norm_num at hθ1'
  have hs2 : Real.sin (-2 * Real.pi / 3) ≠ 0 := fun h => by rw [h] at hθ2'; norm_num at hθ2'
  obtain ⟨B1, hB1, hn1⟩ := hNR ε V₀ C₁ K₂ δ₀' δ (2 * Real.pi / 3) k hε hθ1 hθ1' hC₁0.le hK₂0 hδ0
  obtain ⟨B2, hB2, hn2⟩ := hNR ε V₀ C₁ K₂ δ₀' δ (-2 * Real.pi / 3) k hε hθ2 hθ2' hC₁0.le hK₂0 hδ0
  obtain ⟨B3, hB3, hc1⟩ := hCP ε V₀ C₁ K₂ δ₀' δ (2 * Real.pi / 3) k hε hθ1 hθ1' hC₁0.le hK₂0 hδ0
  try clear hθ1'
  obtain ⟨B4, hB4, hc2⟩ := hCP ε V₀ C₁ K₂ δ₀' δ (-2 * Real.pi / 3) k hε hθ2 hθ2' hC₁0.le hK₂0 hδ0
  try clear hK₂0
  try clear hθ2'
  obtain ⟨B5, hB5, hfa⟩ := hFA ε V₀ γ₀ P₀ δ R Nmax d r k hε hγ₀ hP₀0.le hδ0
    (hδδ₀.trans_eq hδ₀) hR0.le hNmax0.le hd0 hdP
  try clear V₀
  try clear hP₀0
  try clear hdP
  obtain ⟨mq, hmq⟩ : ∃ x : ℝ, x = max (max (4 * ε / δ + 1) (2 * ε + 1))
      (max (4 * ε / δ₀') (32 * (C₁ + 2 * K₂) * ε)) := ⟨_, rfl⟩
  have hmqa : 4 * ε / δ + 1 ≤ mq := by rw [hmq]; exact (le_max_left _ _).trans (le_max_left _ _)
  have hmqb : 2 * ε + 1 ≤ mq := by rw [hmq]; exact (le_max_right _ _).trans (le_max_left _ _)
  have hmqc : 4 * ε / δ₀' ≤ mq := by rw [hmq]; exact (le_max_left _ _).trans (le_max_right _ _)
  have hmqd : 32 * (C₁ + 2 * K₂) * ε ≤ mq := by
    rw [hmq]; exact (le_max_right _ _).trans (le_max_right _ _)
  try clear hmq
  have hmq1 : 1 ≤ mq := by linarith only [hmqb, hε]
  try clear hmqb
  have hmq3 : 1 ≤ mq ^ 3 := one_le_pow₀ hmq1
  refine ⟨B1 + B2 + B3 + B4 + 5 * B5 + 1, ε, mq ^ 3 + 1, by linarith only [hB1, hB2, hB3, hB4, hB5], hε,
    by linarith only [hmq3], ?_⟩
  try clear hB1
  try clear hB2
  try clear hB3
  try clear hB4
  try clear hB5
  intro M N γ π cS ρS cJ v hM hN hγdef hγ1 hγ hπk hπ hcS hcSq hcJ hv
  try clear hπk
  try clear hcJ
  have hγ0 : 0 < γ := by linarith only [hγ1]
  have hM1 : (1 : ℝ) ≤ M := by linarith only [hM, hmq3]
  try clear hmq3
  have hMn : 0 < M := by exact_mod_cast (show (0 : ℝ) < M by linarith only [hM1])
  try clear hM1
  have hNpos : 0 < N := by
    rcases Nat.eq_zero_or_pos N with h | h
    · exfalso; rw [h, Nat.cast_zero, div_zero, Real.sqrt_zero] at hγdef; linarith only [hγdef, hγ1]
    · exact h
  have hγsq : γ ^ 2 = (M : ℝ) / N := by rw [hγdef, Real.sq_sqrt (by positivity)]
  try clear hγdef
  obtain ⟨m, hmdef⟩ : ∃ x : ℝ, x = (M : ℝ) ^ (1 / 3 : ℝ) := ⟨_, rfl⟩
  have hm3 : m ^ 3 = (M : ℝ) := by
    rw [hmdef, ← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]; norm_num
  have hm0 : 0 < m := by rw [hmdef]; positivity
  have hmqm : mq ≤ m := by
    have h3 : mq ^ 3 ≤ m ^ 3 := by rw [hm3]; linarith only [hM]
    exact le_of_pow_le_pow_left₀ (by norm_num) hm0.le h3
  try clear mq
  try clear hM
  have hm1 : 1 ≤ m := hmq1.trans hmqm
  try clear hmq1
  have hν1 : 1 ≤ nu γ := by
    unfold nu
    rw [le_div_iff₀ hγ0, one_mul]
    have h := Real.rpow_le_rpow_of_exponent_le (show (1 : ℝ) ≤ 1 + γ by linarith only [hγ0])
      (show (1 : ℝ) ≤ 4 / 3 by norm_num)
    rw [Real.rpow_one] at h; linarith only [h]
  have hνN : nu γ ≤ Nmax := by
    unfold nu; rw [hNmax, div_le_iff₀ hγ0]
    have h1 := Real.rpow_le_rpow_of_exponent_le (show (1 : ℝ) ≤ 1 + γ by linarith only [hγ0])
      (show (4 / 3 : ℝ) ≤ 2 by norm_num)
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast] at h1
    have h2 : (1 + γ) ^ 2 ≤ (1 + γ₀) ^ 2 := pow_le_pow_left₀ (by linarith only [hγ0]) (by linarith only [hγ]) 2
    have h3 : (1 + γ₀) ^ 2 ≤ (1 + γ₀) ^ 2 * γ := le_mul_of_one_le_right (by positivity) hγ1
    linarith only [h1, h2, h3]
  try clear hNmax
  try clear hγ0
  obtain ⟨σ, hσdef⟩ : ∃ x : ℝ, nu γ * (M : ℝ) ^ (1 / 3 : ℝ) = x := ⟨_, rfl⟩
  have hσ : σ = nu γ * m := by rw [← hσdef, hmdef]
  have hσ0 : 0 < σ := by rw [hσ]; positivity
  have hσm : m ≤ σ := by rw [hσ]; exact le_mul_of_one_le_left hm0.le hν1
  obtain ⟨q, hq⟩ : ∃ x : ℝ, qM γ ε M = x := ⟨_, rfl⟩
  have hq' : q = pc γ - ε / σ := by rw [← hq]; unfold qM; rw [hσdef]
  rw [hq] at hcSq ⊢
  -- elementary facts about pc, π
  have hpc : pc γ = γ / (γ + 1) := rfl
  have hpch : 1 / 2 ≤ pc γ := by rw [hpc, le_div_iff₀ (by linarith only [hγ1])]; linarith only [hγ1]
  have hpc0 : 0 < pc γ := by linarith only [hpch]
  have hpc1 : pc γ < 1 := by rw [hpc, div_lt_one (by linarith only [hγ1])]; linarith only []
  have h1pc : 1 / (γ₀ + 1) ≤ 1 - pc γ := by
    have e : 1 - pc γ = 1 / (γ + 1) := by rw [hpc]; field_simp; ring
    rw [e]; exact one_div_le_one_div_of_le (by linarith only [hγ1]) (by linarith only [hγ])
  have hπpos : ∀ j : Fin r, k ≤ (j : ℕ) → 0 < π j := fun j hj =>
    inv_pos.mp (lt_of_lt_of_le hc₀ (hπ j hj).1)
  have hπP : ∀ j : Fin r, k ≤ (j : ℕ) → π j ≤ P₀ := by
    intro j hj
    have h1 := (hπ j hj).1
    rw [le_inv_comm₀ hc₀ (hπpos j hj)] at h1
    rw [hP₀, one_div]; exact h1
  try clear P₀
  try clear hP₀
  have hipc : (pc γ)⁻¹ = 1 + γ⁻¹ := by rw [hpc]; field_simp
  try clear hpc
  have hπge : ∀ j : Fin r, k ≤ (j : ℕ) → pc γ < π j := by
    intro j hj
    have h2 := (hπ j hj).2
    have h3 : (π j)⁻¹ < (pc γ)⁻¹ := by rw [hipc]; linarith only [hd0, hd2, h2]
    exact (inv_lt_inv₀ (hπpos j hj) hpc0).mp h3
  have hπd : ∀ j : Fin r, k ≤ (j : ℕ) → d ≤ π j - pc γ := by
    intro j hj
    have hp := hπpos j hj
    have hge : c₀ ≤ (pc γ)⁻¹ - (π j)⁻¹ := by have := (hπ j hj).2; rw [hipc]; linarith only [this]
    have hk : π j - pc γ = π j * pc γ * ((pc γ)⁻¹ - (π j)⁻¹) := by field_simp
    have e1 : pc γ * pc γ * c₀ ≤ π j * pc γ * ((pc γ)⁻¹ - (π j)⁻¹) :=
      mul_le_mul (mul_le_mul_of_nonneg_right (hπge j hj).le hpc0.le) hge hc₀.le (by positivity)
    have e2 : 1 / 4 * c₀ ≤ pc γ * pc γ * c₀ :=
      mul_le_mul_of_nonneg_right (by have := mul_le_mul hpch hpch (by norm_num) hpc0.le; linarith only [this]) hc₀.le
    rw [hk]; linarith only [hd2, e1, e2]
  try clear hd2
  try clear hπ
  try clear hipc
  have hπd' : ∀ j : Fin r, k ≤ (j : ℕ) → d ≤ ‖(π j : ℂ) - pc γ‖ := fun j hj => by
    rw [norm_sub_ofReal]; exact (hπd j hj).trans (le_abs_self _)
  have hd1pc : d ≤ 1 - pc γ := hd1.trans h1pc
  -- local hypotheses of near_rayJ / conn_pieceJ
  try clear h1pc
  have hTay' : ∀ z : ℂ, ‖z - pc γ‖ ≤ δ₀' → ‖fFn γ q z - fFn γ q (pc γ) -
      ((nu γ ^ 3 / 3 : ℝ) : ℂ) * (z - pc γ) ^ 3‖ ≤ C₁ * ‖z - pc γ‖ ^ 4 := fun z hz => by
    rw [hC₁]; exact hTay γ₀ γ q z hγ1 hγ (hz.trans (hδ₀'a.trans_eq hδ₀))
  try clear hδ₀
  try clear hC₁
  try clear hδ₀'a
  have hball : ∀ z : ℂ, ‖z - pc γ‖ ≤ δ₀' → z ≠ 0 ∧ 1 - z ≠ 0 ∧ gFn k π z ≠ 0 := by
    intro z hz
    have hz2 : ‖z - pc γ‖ ≤ d / 2 := hz.trans hδ₀'b
    have hne : ∀ x : ℝ, d ≤ |x - pc γ| → (x : ℂ) - z ≠ 0 := by
      intro x hx e
      have : z = (x : ℂ) := (sub_eq_zero.mp e).symm
      rw [this, norm_sub_ofReal] at hz2; linarith only [hδ₀'0, hδ₀'b, hz2, hx]
    have h1 : 1 - z ≠ 0 := by
      have := hne 1 (by rw [abs_of_pos (by linarith only [hpc1])]; linarith only [hd1pc]); simpa using this
    refine ⟨?_, h1, ?_⟩
    · intro e
      have := hne 0 (by
        rw [zero_sub, abs_neg, abs_of_pos hpc0]
        have : 1 / (γ₀ + 1) ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) (by linarith only [hγ1, hγ])
        linarith only [hd1, hpch, hd1pc])
      exact this (by rw [e]; simp)
    · unfold gFn
      refine mul_ne_zero (one_div_ne_zero (pow_ne_zero _ h1)) ?_
      rw [Finset.prod_ne_zero_iff]
      intro j hj
      have hj' : k ≤ (j : ℕ) := (Finset.mem_filter.mp hj).2
      exact hne (π j) (by rw [abs_of_pos (by linarith [hπge j hj'])]; exact hπd j hj')
  try clear hpc0
  try clear hπge
  have hGr' : ∀ z : ℂ, ‖z - pc γ‖ ≤ δ₀' → gFn k π z ≠ 0 ∧
      ‖gFn k π (pc γ) / gFn k π z - 1‖ ≤ K₂ * ‖z - pc γ‖ := fun z hz =>
    ⟨(hball z hz).2.2, by rw [hK₂]; exact hGR k π (pc γ) d z hd0 hd1pc hπd (hz.trans hδ₀'b)⟩
  try clear d
  try clear hK₂
  try clear hd0
  try clear hπd
  try clear hd1pc
  have hg0 : gFn k π (pc γ) ≠ 0 := (hball (pc γ) (by rw [sub_self, norm_zero]; exact hδ₀'0.le)).2.2
  have hcont : ContinuousOn (hJ γ q v M k π) (Metric.closedBall (pc γ : ℂ) δ₀') := by
    refine hJc γ q v M N k π hMn hNpos hN hγsq _ (fun z hz => ?_)
    have hz1 : ‖z - pc γ‖ ≤ δ₀' := by rwa [Metric.mem_closedBall, dist_eq_norm] at hz
    exact ⟨(hball z hz1).1, (hball z hz1).2.1⟩
  try clear hball
  have hσδ4 : 4 * ε ≤ σ * δ := by
    have h := (hmqa.trans (hmqm.trans hσm))
    have h2 : 4 * ε / δ ≤ σ := by linarith only [h]
    rw [div_le_iff₀ hδ0] at h2; linarith only [h2]
  try clear hmqa
  have h2εσ : 2 * ε / σ ≤ δ₀' / 2 := by
    rw [div_le_iff₀ hσ0]
    have h := hmqc.trans (hmqm.trans hσm)
    rw [div_le_iff₀ hδ₀'0] at h
    linarith only [h]
  try clear hmqc
  try clear hσm
  have hsm1 : δ + 2 * ε / σ ≤ δ₀' := by linarith only [h2εσ, hδa]
  try clear δ₀'
  try clear h2εσ
  have hsm2 : (C₁ + 2 * K₂) * (nu γ * δ + 2 * ε / m) ≤ 1 / 8 := by
    have h16 : 16 * (C₁ + 2 * K₂) * Nmax * δ ≤ 1 := by
      have := hδc; rw [le_div_iff₀ (mul_pos (mul_pos (by norm_num) hCK) hNmax0)] at this; linarith only [this]
    have hA : (C₁ + 2 * K₂) * (nu γ * δ) ≤ (C₁ + 2 * K₂) * (Nmax * δ) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hνN hδ0.le) hCK.le
    have hB : (C₁ + 2 * K₂) * (2 * ε / m) ≤ 1 / 16 := by
      rw [mul_div_assoc', div_le_iff₀ (by positivity)]
      have := hmqd.trans hmqm; linarith only [this]
    have e : (C₁ + 2 * K₂) * (nu γ * δ + 2 * ε / m) =
        (C₁ + 2 * K₂) * (nu γ * δ) + (C₁ + 2 * K₂) * (2 * ε / m) := by ring
    have e2 : (C₁ + 2 * K₂) * (Nmax * δ) = (16 * (C₁ + 2 * K₂) * Nmax * δ) / 16 := by ring
    linarith only [h16, hA, hB]
  try clear K₂
  try clear Nmax
  try clear hNmax0
  try clear hCK
  try clear hδc
  try clear hmqd
  try clear hmqm
  have h3ε : 3 * ε / (nu γ * (M : ℝ) ^ (1 / 3 : ℝ)) ≤ δ := by
    rw [hσdef, div_le_iff₀ hσ0]; linarith only [hε, hσδ4]
  -- far pieces
  have hδn : ‖(pc γ : ℂ) + (δ : ℂ) * exp (((2 * Real.pi / 3 : ℝ) : ℂ) * I) - pc γ‖ = δ := by
    rw [add_sub_cancel_left, norm_mul, norm_exp_ofReal_mul_I, mul_one, norm_real,
      Real.norm_of_nonneg hδ0.le]
  have hdec := hDc γ q δ C₁ hν1 hδ0
    (by have := hδb; rw [le_div_iff₀ (mul_pos (by norm_num) hC₁0)] at this; linarith only [this])
    (hTay' _ (by rw [hδn]; linarith only [hδa, hδ₀'0, hδδ₀, hδ0]))
  try clear C₁
  try clear hC₁0
  try clear hδ₀'0
  try clear hδb
  try clear hδδ₀
  try clear hδn
  obtain ⟨f1, f2, f3, f4, f5⟩ := hfa π γ q v m σ (2 * pc γ) M hv hm1 hm3 hγ1 hγ (by linarith only [hν1])
    hνN hσdef hσ hq' hσδ4 (fun j hj => ⟨(hπpos j hj).le, hπP j hj⟩) hπd' rfl h3ε
    (hL32.1 γ q ε M hγ1 hε hMn) (hL32.2.1 γ q R hγ1) (fun y hy0 hy1 => hL3 γ q R y hγ1 hγ le_rfl hy0 hy1)
    hdec
  try clear hL3
  try clear hfa
  try clear hγ1
  try clear hγ
  try clear hνN
  try clear hπpos
  try clear hπP
  try clear hπd'
  try clear h3ε
  try clear hdec
  have n1 := hn1 π γ q v m σ M hv hm1 hm3 hν1 hσdef hσ hq' hsm1 hsm2 hTay' hGr' hg0 hcont
  try clear hn1
  have n2 := hn2 π γ q v m σ M hv hm1 hm3 hν1 hσdef hσ hq' hsm1 hsm2 hTay' hGr' hg0 hcont
  try clear hn2
  try clear hcont
  have c1 := hc1 π γ q v m σ M hv hm1 hm3 hν1 hσdef hσ hq' hsm1 hsm2 hσδ4 hTay' hGr' hg0
  try clear hc1
  have c2 := hc2 π γ q v m σ M hv hm1 hm3 hν1 hσdef hσ hq' hsm1 hsm2 hσδ4 hTay' hGr' hg0
  -- the contour identity
  try clear hc2
  try clear hv
  try clear hm3
  try clear hm1
  try clear hν1
  try clear hσ
  try clear hTay'
  try clear hGr'
  try clear hg0
  try clear hsm1
  try clear hsm2
  have hρ0 : 0 ≤ ρS := by have := abs_nonneg cS; linarith only [hcS, this]
  obtain ⟨w0, hw0def⟩ : ∃ x : ℝ, x = pc γ + (-2 * ε) / σ := ⟨_, rfl⟩
  obtain ⟨ℓ, hℓdef⟩ : ∃ x : ℝ, x = 2 * pc γ := ⟨_, rfl⟩
  have h2εσ' : 2 * ε / σ ≤ δ / 2 := by
    rw [div_le_iff₀ hσ0]; linarith only [hσδ4]
  try clear hσδ4
  have hw0e : w0 = pc γ - 2 * ε / σ := by rw [hw0def]; ring
  have h2εσ0 : (0 : ℝ) ≤ 2 * ε / σ := div_nonneg (by linarith only [hε]) hσ0.le
  have hw0pc : w0 ≤ pc γ := by rw [hw0e]; linarith only [h2εσ0]
  try clear h2εσ0
  have hw0pos : 0 < w0 := by
    rw [hw0e]; have : 1 / (γ₀ + 1) ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) (by linarith only [hγ₀])
    linarith only [h2εσ', hδa, hδ₀'b, hd1, hpch, this]
  have hw0δ : δ / 2 < w0 := by
    rw [hw0e]; have : 1 / (γ₀ + 1) ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) (by linarith only [hγ₀])
    linarith only [h2εσ', hδa, hδ₀'b, hd1, hpch, this]
  try clear h2εσ'
  try clear hw0e
  have hδℓ : δ ≤ ℓ := by
    rw [hℓdef]; have : 1 / (γ₀ + 1) ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) (by linarith only [hγ₀])
    linarith only [hδa, hδ₀'b, hd1, hpch, hw0pc, hw0δ]
  try clear hd1
  try clear hδ₀'b
  try clear hδa
  try clear hpch
  have hX : pc γ - ℓ / 2 - R < 0 := by rw [hℓdef]; linarith only [hR0]
  have hcS1 := abs_lt.mp hcS
  have hpoly := hK3 (hJT γ q v M N k π) cS ρS (by linarith only [hcS1.1, hcS1]) (by linarith only [hcS1.2, hcS1]) (hTd γ q v M N k π)
    (pc γ) w0 δ ℓ R hw0pos hw0pc hδ0 hδℓ hR0.le hX
  try clear hR0
  try clear hw0pos
  try clear hcS1
  have hεσ0 : (0 : ℝ) < ε / σ := div_pos hε hσ0
  try clear hσ0
  have hq1 : q < 1 := by rw [hq']; linarith only [hεσ0, hpc1]
  try clear hq'
  try clear hεσ0
  have hcirc : (∮ z in C((cS : ℂ), ρS), hJ γ q v M k π z) =
      ∮ z in C((cS : ℂ), ρS), hJT γ q v M N k π z := by
    refine circleIntegral.integral_congr hρ0 (fun z hz => ?_)
    have hz' : ‖z - cS‖ = ρS := mem_sphere_iff_norm.mp hz
    have hz0 : z ≠ 0 := fun e => by
      rw [e, zero_sub, norm_neg, Complex.norm_real, Real.norm_eq_abs] at hz'; linarith only [hcS, hz']
    have hz1 : 1 - z ≠ 0 := by
      intro e
      have : z = 1 := (sub_eq_zero.mp e).symm
      rw [this, show (1 : ℂ) = ((1 : ℝ) : ℂ) by simp, norm_sub_ofReal] at hz'
      have : |1 - cS| = 1 - cS := abs_of_pos (by linarith only [hcSq, hq, hq1, hρ0])
      linarith only [hcSq, hq, hq1, hz', this]
    exact hEq γ q v M N k π hMn hNpos hN hγsq z hz0 hz1
  try clear hcS
  try clear hcSq
  try clear hq
  try clear hρ0
  try clear hq1
  have conv : ∀ z : ℂ, z ≠ 0 ∧ 1 - z ≠ 0 → hJT γ q v M N k π z = hJ γ q v M k π z :=
    fun z hz => (hEq γ q v M N k π hMn hNpos hN hγsq z hz.1 hz.2).symm
  try clear hN
  try clear hMn
  try clear hNpos
  try clear hγsq
  have hℓ0 : 0 < ℓ := by linarith only [hδ0, hδℓ]
  rw [icongr (hJT γ q v M N k π) (hJ γ q v M k π)
      (fun y : ℝ => ((pc γ - ℓ / 2 - R : ℝ) : ℂ) + (y : ℂ) * I) I _ _
      (fun y _ => conv _ (okJ_re _ (Or.inl (by simp; linarith only [hX])))),
    icongr0 (hJT γ q v M N k π) (hJ γ q v M k π)
      (fun x : ℝ => (pc γ : ℂ) + (ℓ : ℂ) * exp (((2 * Real.pi / 3 : ℝ) : ℂ) * I) - (x : ℂ)) _ _
      (fun x _ => conv _ (okJ_im _ (by rw [pt3_im]; exact mul_ne_zero hℓ0.ne' hs1))),
    icongr (hJT γ q v M N k π) (hJ γ q v M k π)
      (fun t : ℝ => (pc γ : ℂ) + (t : ℂ) * exp (((2 * Real.pi / 3 : ℝ) : ℂ) * I))
      (exp (((2 * Real.pi / 3 : ℝ) : ℂ) * I)) δ ℓ
      (fun t ht => conv _ (okJ_im _ (by
        rw [pt_im]; rw [Set.uIcc_of_le hδℓ] at ht
        exact mul_ne_zero (lt_of_lt_of_le hδ0 ht.1).ne' hs1))),
    icongr0 (hJT γ q v M N k π) (hJ γ q v M k π)
      (fun s : ℝ => (w0 : ℂ) + (δ : ℂ) * exp (((2 * Real.pi / 3 : ℝ) : ℂ) * I) + (s : ℂ)) _ _
      (fun s _ => conv _ (okJ_im _ (by rw [pt2_im]; exact mul_ne_zero hδ0.ne' hs1))),
    icongr (hJT γ q v M N k π) (hJ γ q v M k π)
      (fun t : ℝ => (w0 : ℂ) + (t : ℂ) * exp (((2 * Real.pi / 3 : ℝ) : ℂ) * I))
      (exp (((2 * Real.pi / 3 : ℝ) : ℂ) * I)) 0 δ
      (fun t ht => conv _ (okJ_re _ (Or.inr ⟨
        by rw [pt_re, hθ1]; rw [Set.uIcc_of_le hδ0.le] at ht; linarith [ht.2, hw0δ],
        by rw [pt_re, hθ1]; rw [Set.uIcc_of_le hδ0.le] at ht; linarith [ht.1, hw0pc, hpc1]⟩))),
    icongr (hJT γ q v M N k π) (hJ γ q v M k π)
      (fun t : ℝ => (w0 : ℂ) + (t : ℂ) * exp (((-2 * Real.pi / 3 : ℝ) : ℂ) * I))
      (exp (((-2 * Real.pi / 3 : ℝ) : ℂ) * I)) 0 δ
      (fun t ht => conv _ (okJ_re _ (Or.inr ⟨
        by rw [pt_re, hθ2]; rw [Set.uIcc_of_le hδ0.le] at ht; linarith [ht.2, hw0δ],
        by rw [pt_re, hθ2]; rw [Set.uIcc_of_le hδ0.le] at ht; linarith [ht.1, hw0pc, hpc1]⟩))),
    icongr0 (hJT γ q v M N k π) (hJ γ q v M k π)
      (fun s : ℝ => (w0 : ℂ) + (δ : ℂ) * exp (((-2 * Real.pi / 3 : ℝ) : ℂ) * I) + (s : ℂ)) _ _
      (fun s _ => conv _ (okJ_im _ (by rw [pt2_im]; exact mul_ne_zero hδ0.ne' hs2))),
    icongr (hJT γ q v M N k π) (hJ γ q v M k π)
      (fun t : ℝ => (pc γ : ℂ) + (t : ℂ) * exp (((-2 * Real.pi / 3 : ℝ) : ℂ) * I))
      (exp (((-2 * Real.pi / 3 : ℝ) : ℂ) * I)) δ ℓ
      (fun t ht => conv _ (okJ_im _ (by
        rw [pt_im]; rw [Set.uIcc_of_le hδℓ] at ht
        exact mul_ne_zero (lt_of_lt_of_le hδ0 ht.1).ne' hs2))),
    icongr0 (hJT γ q v M N k π) (hJ γ q v M k π)
      (fun x : ℝ => (pc γ : ℂ) + (ℓ : ℂ) * exp (((-2 * Real.pi / 3 : ℝ) : ℂ) * I) - (x : ℂ)) _ _
      (fun x _ => conv _ (okJ_im _ (by rw [pt3_im]; exact mul_ne_zero hℓ0.ne' hs2)))]
    at hpoly
  try clear δ
  try clear hδ0
  try clear R
  try clear hθ1
  try clear hθ2
  try clear hs1
  try clear hs2
  try clear N
  try clear hpc1
  try clear w0
  try clear ℓ
  try clear hw0pc
  try clear hw0δ
  try clear hδℓ
  try clear hX
  try clear conv
  try clear hℓ0
  have hJcal : Jcal γ q M k π cS ρS v = ((σ / (2 * Real.pi) : ℝ) : ℂ) *
      ∮ z in C((cS : ℂ), ρS), hJ γ q v M k π z := by rw [← hσdef]; rfl
  try clear M
  try clear γ
  try clear π
  try clear cS
  try clear ρS
  try clear σ
  try clear hσdef
  try clear q
  have hJinf : Jinf ε k (-2 * ε) v = ((Real.exp (ε * v) / (2 * Real.pi) : ℝ) : ℂ) *
      ((∫ t in Set.Ioi (0 : ℝ), phiJ v k (((-2 * ε : ℝ) : ℂ) +
          (t : ℂ) * exp (((2 * Real.pi / 3 : ℝ) : ℂ) * I)) * exp (((2 * Real.pi / 3 : ℝ) : ℂ) * I)) -
        ∫ t in Set.Ioi (0 : ℝ), phiJ v k (((-2 * ε : ℝ) : ℂ) +
          (t : ℂ) * exp (((-2 * Real.pi / 3 : ℝ) : ℂ) * I)) *
            exp (((-2 * Real.pi / 3 : ℝ) : ℂ) * I)) := rfl
  rw [hJv ε k cJ (-2 * ε) v, div_eq_inv_mul, hJcal, hJinf, hcirc, hpoly]
  try clear cJ
  try clear hpoly
  try clear hcirc
  try clear hJcal
  try clear hJinf
  subst hw0def hℓdef
  try clear hw0def
  try clear hℓdef
  refine le_trans (assembleJ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    n1 n2 f1 f2 f3 c1 c2 f4 f5) ?_
  try clear f1
  try clear f2
  try clear f3
  try clear f4
  try clear f5
  try clear n1
  try clear n2
  try clear c1
  try clear c2
  rw [← hmdef]
  try clear hmdef
  have he : 0 ≤ Real.exp (-ε * v) / m := div_nonneg (Real.exp_pos _).le hm0.le
  try clear hm0
  calc _ = (B1 + B2 + B3 + B4 + 5 * B5) * (Real.exp (-ε * v) / m) := by ring
    _ ≤ (B1 + B2 + B3 + B4 + 5 * B5 + 1) * (Real.exp (-ε * v) / m) :=
        mul_le_mul_of_nonneg_right (by linarith only []) he
    _ = _ := by ring

end P31A2

open Complex MeasureTheory SpikedWishart.SoftEdge in
theorem solution (ε γ₀ c₀ : ℝ) (hε : 0 < ε) (hγ₀ : 1 ≤ γ₀) (hc₀ : 0 < c₀)
    (r k : ℕ) (hkr : k ≤ r) :
    ∀ V₀ : ℝ, ∃ C c M₀ : ℝ, 0 < C ∧ 0 < c ∧ 0 < M₀ ∧
      ∀ (M N : ℕ) (γ : ℝ) (π : Fin r → ℝ) (cS ρS cJ v : ℝ),
        M₀ ≤ M → r ≤ N → γ = Real.sqrt ((M : ℝ) / (N : ℝ)) → 1 ≤ γ → γ ≤ γ₀ →
        (∀ j : Fin r, (j : ℕ) < k → π j = pc γ) →
        (∀ j : Fin r, k ≤ (j : ℕ) → c₀ ≤ (π j)⁻¹ ∧ (π j)⁻¹ ≤ 1 + γ⁻¹ - c₀) →
        |cS| < ρS → cS + ρS < qM γ ε M →
        cJ < -ε → V₀ ≤ v →
        ‖Jcal γ (qM γ ε M) M k π cS ρS v / ZM γ (qM γ ε M) M k π - Jinf ε k cJ v‖ ≤
          C * Real.exp (-c * v) / (M : ℝ) ^ (1 / 3 : ℝ) := by
  exact P31A2.part_ii SpikedWishart.SoftEdge.circle_eq_polygonJ SpikedWishart.SoftEdge.J_near_ray SpikedWishart.SoftEdge.J_conn_piece SpikedWishart.SoftEdge.J_far_all P31Hd.hdecJ P31.fFn_cubic_taylor @P31E2.gFn_ratio_bound @P31J3.hJ_eq_hJT @P31J3.hJT_differentiableOn @P31J3.hJ_continuousOn SpikedWishart.SoftEdge.Jinf_vertex_shift SpikedWishart.SoftEdge.lemma_3_2 ε γ₀ c₀ hε hγ₀ hc₀ r k
