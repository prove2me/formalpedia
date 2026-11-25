-- Prove2me | solution 1 for UpperTheory.T3.levelPrimeN
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T09:20:24.973225+00:00
-- url     : https://prove2.me/submissions/0dc62eaf-e84a-4250-bec3-f53404b4090c

import Definitions.Def_Development_AutomorphicArithmetic_ShortNorms_ShortNorm
import Definitions.Def_Development_AutomorphicArithmetic_ShortNorms_levelPrimeN
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open GlobalTheory.Mem.An
namespace UpperTheory.T3
open Filter in

private theorem ev_log_le {a k : ℝ} (ha : 0 < a) (hk : 0 < k) (A D : ℝ) (hD : 0 < D) :
    ∀ᶠ x : ℝ in atTop, A + D * Real.log x ≤ k * x ^ a := by
  have h1 := (isLittleO_log_rpow_atTop ha).bound (show (0:ℝ) < k / (2 * (|D| + 1)) by positivity)
  have h2 := (tendsto_rpow_atTop ha).eventually_ge_atTop (2 * |A| / k)
  filter_upwards [h1, h2, eventually_gt_atTop (0:ℝ)] with x hx1 hx2 hx3
  have hxa : 0 < x ^ a := Real.rpow_pos_of_pos hx3 a
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hxa] at hx1
  have hD1 : 0 < |D| + 1 := by positivity
  have e1 : D * Real.log x ≤ |D| * |Real.log x| := by
    calc D * Real.log x ≤ |D * Real.log x| := le_abs_self _
      _ = |D| * |Real.log x| := abs_mul _ _
  have e2 : |D| * |Real.log x| ≤ |D| * (k / (2 * (|D| + 1)) * x ^ a) :=
    mul_le_mul_of_nonneg_left hx1 (abs_nonneg D)
  have e3 : |D| * (k / (2 * (|D| + 1)) * x ^ a) ≤ k / 2 * x ^ a := by
    have q : |D| * (k / (2 * (|D| + 1)) * x ^ a) = (|D| / (|D| + 1)) * (k / 2 * x ^ a) := by
      field_simp
    have r : |D| / (|D| + 1) ≤ 1 := by rw [div_le_one hD1]; linarith
    have s : 0 ≤ k / 2 * x ^ a := by positivity
    rw [q]
    nlinarith
  have e4 : A ≤ k / 2 * x ^ a := by
    have t1 : 2 * |A| / k * k = 2 * |A| := div_mul_cancel₀ _ hk.ne'
    have t2 := mul_le_mul_of_nonneg_right hx2 hk.le
    nlinarith [le_abs_self A]
  linarith
end UpperTheory.T3
end

set_option autoImplicit false
open GlobalTheory.Mem.An
open UpperTheory UpperTheory.T3
set_option maxHeartbeats 800000
namespace UpperTheory.T3
theorem _root_.solution :
    ShortNorm → ∀ eps : ℝ, 0 < eps → eps < 1 / 52 → ∀ cs CY : ℝ, 0 < cs → 0 < CY → ∃ x₀ : ℝ, ∀ x ≥ x₀, ∀ N d g₁ g₂ m : ℕ,
      ModAt x eps N d → 1 ≤ g₁ → 1 ≤ g₂ → Real.log g₁ ≤ CY * x ^ eps → Real.log g₂ ≤ CY * x ^ eps → x ^ ((1 : ℝ) / 3) ≤ m →
      ∀ V Ts : ℝ, 1 ≤ V → V ≤ x ^ (12 : ℝ) → 0 < Ts → cs * m * x ^ eps ≤ Real.log Ts →
      ∃ T : ℕ, T.Prime ∧ Ts < T ∧ (T : ℝ) ≤ (1 + 1 / V) * Ts ∧ NormOne d (N * (g₁ * g₂) ^ 2) T := by
  intro hSN eps heps heps1 cs CY hcs hCY
  unfold ShortNorm at hSN
  obtain ⟨A, c, c', hA, hc, hc', hmain⟩ := hSN
  have hK0 : 0 < c * Real.sqrt cs := mul_pos hc (Real.sqrt_pos.mpr hcs)
  have hK3 : 0 < c * Real.sqrt cs / 3 := by linarith
  have E1 := ev_log_le (a := 1 / 6 + eps / 2) (k := c * Real.sqrt cs) (by linarith) hK0 0 12 (by norm_num)
  have E2 := ev_log_le (a := (1:ℝ) / 12) (k := 1) (by norm_num) one_pos 0 1 one_pos
  have E3 := ev_log_le (a := 3 * eps / 10) (k := c * Real.sqrt cs / 3) (by linarith) hK3 9 1 one_pos
  have E4 := ev_log_le (a := 1 / 6 - eps / 2) (k := c * Real.sqrt cs / 3) (by linarith) hK3 (8 * CY) 1 one_pos
  have E5 := ev_log_le (a := 1 / 6 + eps / 2) (k := c * Real.sqrt cs / 3) (by linarith) hK3 (Real.log 4) 1 one_pos
  obtain ⟨x₀, hx₀⟩ := Filter.eventually_atTop.mp
    (E1.and (E2.and (E3.and (E4.and (E5.and (Filter.eventually_ge_atTop (1:ℝ)))))))
  refine ⟨x₀, fun x hx N d g₁ g₂ m hMod hg1 hg2 hlg1 hlg2 hm V Ts hV1 hVx hTs hlogT => ?_⟩
  obtain ⟨F1, F2, F3, F4, F5, hx1⟩ := hx₀ x hx
  unfold ModAt at hMod
  obtain ⟨hdp, hd4, hd100, hN0, hdN, hlogN⟩ := hMod
  have hxpos : 0 < x := by linarith
  have hV0 : 0 < V := by linarith
  have hlogx : 0 ≤ Real.log x := Real.log_nonneg hx1
  have rp : ∀ a b : ℝ, x ^ a * x ^ b = x ^ (a + b) := fun a b => (Real.rpow_add hxpos a b).symm
  have hx13 : 0 < x ^ ((1:ℝ) / 3) := Real.rpow_pos_of_pos hxpos _
  have hm0 : (0:ℝ) < m := lt_of_lt_of_le hx13 hm
  have hxe : 0 < x ^ eps := Real.rpow_pos_of_pos hxpos _
  have hlogT0 : 0 < Real.log Ts := lt_of_lt_of_le (mul_pos (mul_pos hcs hm0) hxe) hlogT
  have hTs1 : 1 < Ts := by
    by_contra hh
    push_neg at hh
    have := Real.log_nonpos hTs.le hh
    linarith
  have hsq : Real.sqrt cs * x ^ (1 / 6 + eps / 2) ≤ Real.sqrt (Real.log Ts) := by
    rw [Real.le_sqrt (mul_nonneg (Real.sqrt_nonneg _) (Real.rpow_pos_of_pos hxpos _).le) hlogT0.le]
    have e : (Real.sqrt cs * x ^ (1 / 6 + eps / 2)) ^ 2 = cs * (x ^ ((1:ℝ) / 3) * x ^ eps) := by
      rw [mul_pow, Real.sq_sqrt hcs.le, sq, rp, rp]
      congr 2
      ring
    rw [e]
    have t := mul_le_mul_of_nonneg_left hm (mul_pos hcs hxe).le
    linarith
  have hKs : c * Real.sqrt cs * x ^ (1 / 6 + eps / 2) ≤ c * Real.sqrt (Real.log Ts) := by
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left hsq hc.le
  have hd0 : (0:ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hN0' : (0:ℝ) < N := by exact_mod_cast hN0
  have hg10 : (0:ℝ) < g₁ := by exact_mod_cast (show 0 < g₁ by omega)
  have hg20 : (0:ℝ) < g₂ := by exact_mod_cast (show 0 < g₂ by omega)
  have hdN' := Nat.le_of_dvd hN0 hdN
  have hdleN : (d:ℝ) ≤ N := by exact_mod_cast hdN'
  have hlogd : Real.log d ≤ Real.log N := Real.log_le_log hd0 hdleN
  have hg0 : 0 < g₁ * g₂ := Nat.mul_pos (by omega) (by omega)
  have hsq1 : 1 ≤ (g₁ * g₂) ^ 2 := Nat.one_le_pow _ _ hg0
  have hM3 : 3 ≤ N * (g₁ * g₂) ^ 2 := by nlinarith
  have hM : Real.log (4 * (d:ℝ) * ((N * (g₁ * g₂) ^ 2 : ℕ) : ℝ) ^ 2)
      = Real.log 4 + Real.log d + 2 * (Real.log N + 2 * Real.log g₁ + 2 * Real.log g₂) := by
    have h4 : (4:ℝ) ≠ 0 := by norm_num
    push_cast
    rw [Real.log_mul (mul_ne_zero h4 hd0.ne')
      (pow_ne_zero _ (mul_ne_zero hN0'.ne' (pow_ne_zero _ (mul_ne_zero hg10.ne' hg20.ne'))))]
    rw [Real.log_mul h4 hd0.ne', Real.log_pow, Real.log_mul hN0'.ne' (pow_ne_zero _ (mul_ne_zero hg10.ne' hg20.ne')),
      Real.log_pow, Real.log_mul hg10.ne' hg20.ne']
    push_cast
    ring
  have hxe5 : 0 < x ^ (eps / 5) := Real.rpow_pos_of_pos hxpos _
  have hx12 : 0 < x ^ ((1:ℝ) / 12) := Real.rpow_pos_of_pos hxpos _
  have hx6 : 0 < x ^ ((1:ℝ) / 6) := Real.rpow_pos_of_pos hxpos _
  have q1 : Real.log x ^ 2 ≤ x ^ ((1:ℝ) / 6) := by
    have a1 : Real.log x ≤ x ^ ((1:ℝ) / 12) := by linarith
    rw [sq]
    calc Real.log x * Real.log x ≤ x ^ ((1:ℝ) / 12) * x ^ ((1:ℝ) / 12) := mul_le_mul a1 a1 hlogx hx12.le
      _ = x ^ ((1:ℝ) / 6) := by rw [rp]; norm_num
  have q3 : x ^ (eps / 5) * Real.log x ^ 2 ≤ x ^ (eps / 5) * x ^ ((1:ℝ) / 6) :=
    mul_le_mul_of_nonneg_left q1 hxe5.le
  have P0 : 0 < x ^ (eps / 5) * x ^ ((1:ℝ) / 6) := mul_pos hxe5 hx6
  have f3 : 9 ≤ c * Real.sqrt cs / 3 * x ^ (3 * eps / 10) := by linarith
  have q4 : 9 * (x ^ (eps / 5) * x ^ ((1:ℝ) / 6)) ≤ c * Real.sqrt cs / 3 * x ^ (1 / 6 + eps / 2) := by
    have e : x ^ (1 / 6 + eps / 2) = x ^ (3 * eps / 10) * (x ^ (eps / 5) * x ^ ((1:ℝ) / 6)) := by
      rw [rp, rp]
      congr 1
      ring
    rw [e]
    have t := mul_le_mul_of_nonneg_right f3 P0.le
    linarith
  have f4 : 8 * CY ≤ c * Real.sqrt cs / 3 * x ^ (1 / 6 - eps / 2) := by linarith
  have q5 : 8 * CY * x ^ eps ≤ c * Real.sqrt cs / 3 * x ^ (1 / 6 + eps / 2) := by
    have e : x ^ (1 / 6 + eps / 2) = x ^ (1 / 6 - eps / 2) * x ^ eps := by
      rw [rp]
      congr 1
      ring
    rw [e]
    have t := mul_le_mul_of_nonneg_right f4 hxe.le
    linarith
  have f5 : Real.log 4 ≤ c * Real.sqrt cs / 3 * x ^ (1 / 6 + eps / 2) := by linarith
  have hlogbound : Real.log (4 * (d:ℝ) * ((N * (g₁ * g₂) ^ 2 : ℕ) : ℝ) ^ 2) ≤ c * Real.sqrt (Real.log Ts) := by
    rw [hM]
    linarith
  have hVle : Real.log V ≤ c * Real.sqrt (Real.log Ts) := by
    have t : Real.log V ≤ Real.log (x ^ (12:ℝ)) := Real.log_le_log hV0 hVx
    rw [Real.log_rpow hxpos] at t
    linarith
  have hexp : Real.exp (-c * Real.sqrt (Real.log Ts)) ≤ 1 / V := by
    rw [neg_mul, Real.exp_neg, one_div]
    apply inv_anti₀ hV0
    calc V = Real.exp (Real.log V) := (Real.exp_log hV0).symm
      _ ≤ _ := Real.exp_le_exp.mpr hVle
  have hh1 : 1 / V ≤ 1 := by rw [div_le_one hV0]; exact hV1
  have key := hmain d (N * (g₁ * g₂) ^ 2) Ts (1 / V) hdp hd4 hd100 hM3 hTs1.le hlogbound hexp hh1
  have hMpos : (0:ℝ) < ((N * (g₁ * g₂) ^ 2 : ℕ) : ℝ) := by exact_mod_cast Nat.lt_of_lt_of_le (by norm_num) hM3
  have hbase : (0:ℝ) < 4 * (d:ℝ) * ((N * (g₁ * g₂) ^ 2 : ℕ) : ℝ) ^ 2 :=
    mul_pos (mul_pos (by norm_num) hd0) (pow_pos hMpos 2)
  have hpos : (0:ℝ) < c' * (1 / V) * Ts / ((4 * (d:ℝ) * ((N * (g₁ * g₂) ^ 2 : ℕ) : ℝ) ^ 2) ^ A * Real.log Ts) :=
    div_pos (mul_pos (mul_pos hc' (one_div_pos.mpr hV0)) hTs)
      (mul_pos (Real.rpow_pos_of_pos hbase A) hlogT0)
  have hcard : 0 < (normPrimes d (N * (g₁ * g₂) ^ 2) Ts (Ts * (1 + 1 / V))).card := by
    exact_mod_cast lt_of_lt_of_le hpos key
  obtain ⟨p, hp⟩ := Finset.card_pos.mp hcard
  simp only [normPrimes, Finset.mem_filter, Finset.mem_Ioc] at hp
  obtain ⟨⟨hlo, hhi⟩, hpp, hno⟩ := hp
  have hY : 0 ≤ Ts * (1 + 1 / V) := mul_nonneg hTs.le (by have := one_div_pos.mpr hV0; linarith)
  refine ⟨p, hpp, Nat.lt_of_floor_lt hlo, ?_, hno⟩
  have t := (Nat.le_floor_iff hY).mp hhi
  rw [mul_comm]
  exact t
end UpperTheory.T3
