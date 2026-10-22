-- Prove2me | solution 1 for Tegmark.orbit_stability_31
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T16:12:13.316316+00:00
-- url     : https://prove2.me/submissions/fbf1b309-9a74-4b63-97e1-10cd9d022c5d

import Mathlib
import Definitions.Def_Tegmark_sig
import Definitions.Def_Tegmark_phys
import Definitions.Def_Tegmark_ensemble
open Tegmark

theorem g71t_d1 (k L : ℝ) (n : ℕ) (x : ℝ) (hx : 0 < x) :
    HasDerivAt (effPot k L n)
      (-L ^ 2 / x ^ 3 + k * ((n:ℝ) - 2) * x ^ (2 - (n:ℝ) - 1)) x := by
  have h := ((hasDerivAt_const x (L ^ 2)).div ((hasDerivAt_pow 2 x).const_mul 2)
    (by positivity)).add
    ((Real.hasDerivAt_rpow_const (p := 2 - (n:ℝ)) (Or.inl hx.ne')).const_mul (-k))
  have hf : effPot k L n = ((fun _ => L ^ 2) / fun y => 2 * y ^ 2) + fun y => -k * y ^ (2 - (n:ℝ)) := by
    funext y; simp [effPot, newton]
  rw [hf]
  refine h.congr_deriv ?_
  have hx0 : x ≠ 0 := hx.ne'
  norm_num
  field_simp
  ring

theorem g71t_d2 (k L : ℝ) (n : ℕ) (x : ℝ) (hx : 0 < x) :
    HasDerivAt (fun y => -L ^ 2 / y ^ 3 + k * ((n:ℝ) - 2) * y ^ (2 - (n:ℝ) - 1))
      (3 * L ^ 2 / x ^ 4 + k * ((n:ℝ) - 2) * ((2 - (n:ℝ) - 1) * x ^ (2 - (n:ℝ) - 1 - 1))) x := by
  have h := ((hasDerivAt_const x (-L ^ 2)).div (hasDerivAt_pow 3 x)
    (by positivity)).add
    ((Real.hasDerivAt_rpow_const (p := 2 - (n:ℝ) - 1) (Or.inl hx.ne')).const_mul (k * ((n:ℝ) - 2)))
  refine h.congr_deriv ?_
  have hx0 : x ≠ 0 := hx.ne'
  norm_num
  field_simp

theorem g71t_dd (k L : ℝ) (n : ℕ) (r : ℝ) (hr : 0 < r) :
    deriv (fun x => deriv (effPot k L n) x) r
      = 3 * L ^ 2 / r ^ 4 + k * ((n:ℝ) - 2) * ((2 - (n:ℝ) - 1) * r ^ (2 - (n:ℝ) - 1 - 1)) := by
  have he : (fun x => deriv (effPot k L n) x) =ᶠ[nhds r]
      fun y => -L ^ 2 / y ^ 3 + k * ((n:ℝ) - 2) * y ^ (2 - (n:ℝ) - 1) := by
    filter_upwards [lt_mem_nhds hr] with x hx
    exact (g71t_d1 k L n x hx).deriv
  rw [he.deriv_eq]
  exact (g71t_d2 k L n r hr).deriv

theorem solution (n : ℕ) (_hn : 3 ≤ n) :
    HasStableOrbit n ↔ n = 3 := by
  constructor
  · rintro ⟨k, L, r, hk, hL, ⟨hr, h1⟩, h2⟩
    rw [(g71t_d1 k L n r hr).deriv] at h1
    rw [g71t_dd k L n r hr] at h2
    by_contra hn3
    have hn4 : (4:ℝ) ≤ n := by exact_mod_cast (show 4 ≤ n by omega)
    rw [Real.rpow_sub_one hr.ne', Real.rpow_sub_one hr.ne'] at h2
    rw [Real.rpow_sub_one hr.ne'] at h1
    set P := r ^ (2 - (n:ℝ)) with hP
    have hPp : 0 < P := Real.rpow_pos_of_pos hr _
    have hL2 : L ^ 2 = k * ((n:ℝ) - 2) * P * r ^ 2 := by
      field_simp at h1; nlinarith [h1]
    rw [hL2] at h2
    have : 3 * (k * (↑n - 2) * P * r ^ 2) / r ^ 4 + k * (↑n - 2) * ((2 - ↑n - 1) * (P / r / r))
        = k * ((n:ℝ) - 2) * (4 - n) * P / r ^ 2 := by
      field_simp; ring
    rw [this] at h2
    have : k * ((n:ℝ) - 2) * (4 - n) * P ≤ 0 := by
      have a : 0 ≤ k * ((n:ℝ) - 2) * P := by
        have : (0:ℝ) ≤ (n:ℝ) - 2 := by linarith
        positivity
      nlinarith
    have : k * ((n:ℝ) - 2) * (4 - n) * P / r ^ 2 ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg this (by positivity)
    linarith
  · rintro rfl
    refine ⟨1, 1, 1, one_pos, one_pos, ⟨one_pos, ?_⟩, ?_⟩
    · rw [(g71t_d1 1 1 3 1 one_pos).deriv]; norm_num
    · rw [g71t_dd 1 1 3 1 one_pos]; norm_num
