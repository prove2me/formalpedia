-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Next46.P21.conjugate_rectangle_unique
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-20T22:31:05.970624+00:00
-- url     : https://prove2.me/submissions/811431c4-a4f6-47b9-9c35-d5d1e1b40685

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P21
noncomputable section

open QAlgorithms.Papers.Independent.Next46.P21

open Set

open scoped ComplexConjugate

theorem g64a_qr (a : Zsqrtd 2) : quadraticReal a = (a.re : ℝ) + (a.im : ℝ) * Real.sqrt 2 := by
  simp [quadraticReal, Zsqrtd.toReal_apply]

theorem g64a_inj : Function.Injective quadraticReal :=
  Zsqrtd.toReal_injective (by norm_num) (by
    intro n hn
    have h1 : n.natAbs * n.natAbs = 2 := by
      have := congrArg Int.natAbs hn; simpa [Int.natAbs_mul] using this.symm
    have : n.natAbs ≤ 2 := by nlinarith
    interval_cases (n.natAbs) <;> omega)

theorem solution (x0 x1 y0 y1 : ℝ)
    (hx : x0 < x1) (hy : y0 < y1)
    (harea : (x1 - x0) * (y1 - y0) < 1) :
    (rectangleSolutions x0 x1 y0 y1).Subsingleton := by
  intro a ha b hb
  simp only [rectangleSolutions, Set.mem_ofPred_eq, Set.mem_Icc] at ha hb
  set d := a - b with hd
  have e1 : |quadraticReal d| ≤ x1 - x0 := by
    rw [hd, map_sub, abs_le]; constructor <;> linarith
  have e2 : |quadraticReal (star d)| ≤ y1 - y0 := by
    rw [hd, star_sub, map_sub, abs_le]; constructor <;> linarith
  have hprod : |quadraticReal d * quadraticReal (star d)| < 1 := by
    rw [abs_mul]
    calc |quadraticReal d| * |quadraticReal (star d)| ≤ (x1 - x0) * (y1 - y0) :=
          mul_le_mul e1 e2 (abs_nonneg _) (by linarith)
      _ < 1 := harea
  have hn : quadraticReal d * quadraticReal (star d) = ((d.re * d.re - 2 * d.im * d.im : ℤ) : ℝ) := by
    rw [g64a_qr, g64a_qr]
    have hs := Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num)
    simp only [Zsqrtd.re_star, Zsqrtd.im_star]; push_cast; linear_combination (-(d.im:ℝ)^2) * hs
  rw [hn] at hprod
  have hz : (d.re * d.re - 2 * d.im * d.im : ℤ) = 0 := by
    have : |(d.re * d.re - 2 * d.im * d.im : ℤ)| < 1 := by exact_mod_cast hprod
    rw [abs_lt] at this; omega
  have h0 : quadraticReal d * quadraticReal (star d) = 0 := by rw [hn, hz]; simp
  rcases mul_eq_zero.1 h0 with h | h
  · have : d = 0 := g64a_inj (by rw [h, map_zero])
    exact sub_eq_zero.1 this
  · have : star d = 0 := g64a_inj (by rw [h, map_zero])
    have : d = 0 := by simpa using this
    exact sub_eq_zero.1 this
