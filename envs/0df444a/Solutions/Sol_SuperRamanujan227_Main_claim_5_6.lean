-- Prove2me | solution 1 for SuperRamanujan227.Main.claim_5_6
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T03:33:16.547597+00:00
-- url     : https://prove2.me/submissions/c8aabd4b-7bcc-4e96-b07e-7ba4b8a89b47

import Mathlib
import Definitions.Def_SuperRamanujan227_Main_Spectra
import Definitions.Def_SuperRamanujan227_Main_Jacobi
import Theorems.Thm_SuperRamanujan227_Main_claim_5_5
import Theorems.Thm_SuperRamanujan227_Main_theorem_5_7

section
set_option autoImplicit false
open Polynomial

namespace SuperRamanujan227.Dev.C56

lemma rpow_sq_helper (x c : ℝ) (hx : 0 < x) : (x ^ 2) ^ c = x ^ (2 * c) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hx.le]; norm_num

/-- the rpow identity: K0 = RHS -/
lemma K_eq (n d : ℝ) (hn : 0 < n) (hd : 2 < d) :
    let A := n * (n * (d - 1) + 1)
    let C := n ^ 2 * d ^ 2 + 4 * n * (d - 1) + 4
    let a := n * (d - 2) + 2
    3 * (1 - (Real.sqrt (C * (4 * A)) / C) ^ 2) ^ ((2 : ℝ) / 3) * (2 * Real.sqrt (C * (4 * A))) ^ (-(1 : ℝ) / 3) =
      3 / (4 : ℝ) ^ ((1 : ℝ) / 3) * n ^ (-(2 : ℝ) / 3) *
        ((d - 2 + 2 / n) ^ ((4 : ℝ) / 3) /
          ((d - 1 + 1 / n) ^ ((1 : ℝ) / 6) * (d ^ 2 + 4 * (d - 1) / n + 4 / n ^ 2) ^ ((5 : ℝ) / 6))) := by
  intro A C a
  have hd1 : 0 < d - 1 := by linarith
  have hd2 : 0 < d - 2 := by linarith
  have hA : 0 < A := mul_pos hn (by have := mul_pos hn hd1; linarith)
  have hC : 0 < C := by have := mul_pos hn hd1; have : 0 < n ^ 2 * d ^ 2 := by positivity
                        simp only [C]; linarith
  have ha : 0 < a := by have := mul_pos hn hd2; simp only [a]; linarith
  have hCA : C - 4 * A = a ^ 2 := by simp only [A, C, a]; ring
  have h1 : 1 - (Real.sqrt (C * (4 * A)) / C) ^ 2 = a ^ 2 / C := by
    rw [div_pow, Real.sq_sqrt (by positivity)]
    field_simp
    linarith
  have hsq : Real.sqrt (C * (4 * A)) = 2 * (A * C) ^ ((1 : ℝ) / 2) := by
    rw [Real.sqrt_eq_rpow]
    rw [show C * (4 * A) = 2 ^ 2 * (A * C) by ring, Real.mul_rpow (by positivity) (by positivity),
      rpow_sq_helper 2 _ (by norm_num)]
    norm_num
  have hu : (d - 2 + 2 / n) = a / n := by simp only [a]; field_simp
  have hv : (d - 1 + 1 / n) = A / n ^ 2 := by simp only [A]; field_simp
  have hw : d ^ 2 + 4 * (d - 1) / n + 4 / n ^ 2 = C / n ^ 2 := by simp only [C]; field_simp
  rw [h1, hsq, hu, hv, hw]
  have hn2 : (0 : ℝ) < n ^ 2 := by positivity
  rw [Real.div_rpow (by positivity) hC.le, rpow_sq_helper a _ ha,
    Real.div_rpow ha.le hn.le, Real.div_rpow hA.le hn2.le, Real.div_rpow hC.le hn2.le,
    rpow_sq_helper n _ hn, rpow_sq_helper n _ hn,
    show (2 * (2 * (A * C) ^ ((1 : ℝ) / 2))) = 4 * (A * C) ^ ((1 : ℝ) / 2) by ring,
    Real.mul_rpow (by norm_num) (by positivity), ← Real.rpow_mul (by positivity),
    Real.mul_rpow hA.le hC.le]
  have e1 : n ^ (-(2 : ℝ) / 3) * n ^ ((1 : ℝ) / 3) * n ^ ((5 : ℝ) / 3) = n ^ ((4 : ℝ) / 3) := by
    rw [← Real.rpow_add hn, ← Real.rpow_add hn]; norm_num
  have p1 : 0 < n ^ ((4 : ℝ) / 3) := Real.rpow_pos_of_pos hn _
  have p2 : 0 < A ^ ((1 : ℝ) / 6) := Real.rpow_pos_of_pos hA _
  have p3 : 0 < C ^ ((5 : ℝ) / 6) := Real.rpow_pos_of_pos hC _
  have p4 : 0 < (4 : ℝ) ^ ((1 : ℝ) / 3) := Real.rpow_pos_of_pos (by norm_num) _
  have p5 : 0 < C ^ ((2 : ℝ) / 3) := Real.rpow_pos_of_pos hC _
  have x1 : (2 : ℝ) * (2 / 3) = 4 / 3 := by norm_num
  have x2 : (1 : ℝ) / 2 * (-1 / 3) = -((1 : ℝ) / 6) := by norm_num
  have x3 : (2 : ℝ) * (1 / 6) = 1 / 3 := by norm_num
  have x4 : (2 : ℝ) * (5 / 6) = 5 / 3 := by norm_num
  rw [x1, x2, x3, x4, Real.rpow_neg hA.le, Real.rpow_neg hC.le,
    show (-1 : ℝ) / 3 = -((1 : ℝ) / 3) by norm_num, Real.rpow_neg (by norm_num : (0:ℝ) ≤ 4)]
  have fC : C ^ ((5 : ℝ) / 6) = C ^ ((2 : ℝ) / 3) * C ^ ((1 : ℝ) / 6) := by
    rw [← Real.rpow_add hC]; norm_num
  have p6 : 0 < C ^ ((1 : ℝ) / 6) := Real.rpow_pos_of_pos hC _
  have p7 : 0 < n ^ ((1 : ℝ) / 3) := Real.rpow_pos_of_pos hn _
  have p8 : 0 < n ^ ((5 : ℝ) / 3) := Real.rpow_pos_of_pos hn _
  have p9 : 0 < n ^ (-(2 : ℝ) / 3) := Real.rpow_pos_of_pos hn _
  have p10 : 0 < a ^ ((4 : ℝ) / 3) := Real.rpow_pos_of_pos ha _
  rw [fC] at *
  field_simp
  rw [← Real.rpow_add hn, ← Real.rpow_add hn]; norm_num


lemma B_lt (n d : ℝ) (hn : 0 < n) (hd : 2 < d) :
    let A := n * (n * (d - 1) + 1)
    let C := n ^ 2 * d ^ 2 + 4 * n * (d - 1) + 4
    Real.sqrt (C * (4 * A)) / C < 2 * Real.sqrt (d - 1) / d := by
  intro A C
  have hd1 : 0 < d - 1 := by linarith
  have hd0 : 0 < d := by linarith
  have hA : 0 < A := mul_pos hn (by have := mul_pos hn hd1; linarith)
  have hC : 0 < C := by have := mul_pos hn hd1; have : 0 < n ^ 2 * d ^ 2 := by positivity
                        simp only [C]; linarith
  have key : (d - 1) * C - d ^ 2 * A = n * (d - 2) * (3 * d - 2) + 4 * (d - 1) := by
    simp only [A, C]; ring
  have kpos : 0 < n * (d - 2) * (3 * d - 2) + 4 * (d - 1) := by
    have : 0 < d - 2 := by linarith
    have : 0 < 3 * d - 2 := by linarith
    positivity
  have hL : 0 < 2 * Real.sqrt (d - 1) / d := by positivity
  rw [div_lt_iff₀ hC, Real.sqrt_lt' (by positivity)]
  have hL2 : (2 * Real.sqrt (d - 1) / d * C) ^ 2 = 4 * (d - 1) / d ^ 2 * C ^ 2 := by
    rw [mul_pow, div_pow, mul_pow, Real.sq_sqrt hd1.le]; ring
  rw [hL2, show C * (4 * A) = 4 * A * C by ring]
  rw [show 4 * (d - 1) / d ^ 2 * C ^ 2 = 4 * (d - 1) * C * C / d ^ 2 by ring, lt_div_iff₀ (by positivity)]
  nlinarith [mul_pos hC (show 0 < (d - 1) * C - d ^ 2 * A by rw [key]; exact kpos)]

lemma alg (n d z : ℝ) (hn : 0 < n) (hd : 2 < d)
    (h : let α := n * (d - 2) / 2
         let s := 2 * α + 1
         let ρ := 2 * n + 2 * α + 1
         let R := Real.sqrt ((ρ ^ 2 + 2 * s + 1) * (ρ ^ 2 - s ^ 2))
         let B := R / (ρ ^ 2 + 2 * s + 1)
         z < B - 3 * (1 - B ^ 2) ^ ((2 : ℝ) / 3) * (2 * R) ^ (-(1 : ℝ) / 3)) :
    2 * Real.sqrt (d - 1) / d - z >
      3 / (4 : ℝ) ^ ((1 : ℝ) / 3) * n ^ (-(2 : ℝ) / 3) *
        ((d - 2 + 2 / n) ^ ((4 : ℝ) / 3) /
          ((d - 1 + 1 / n) ^ ((1 : ℝ) / 6) * (d ^ 2 + 4 * (d - 1) / n + 4 / n ^ 2) ^ ((5 : ℝ) / 6))) := by
  have hK := K_eq n d hn hd
  have hB := B_lt n d hn hd
  dsimp only at h hK hB
  have e1 : (2 * n + 2 * (n * (d - 2) / 2) + 1) ^ 2 + 2 * (2 * (n * (d - 2) / 2) + 1) + 1 =
      n ^ 2 * d ^ 2 + 4 * n * (d - 1) + 4 := by ring
  have e2 : (2 * n + 2 * (n * (d - 2) / 2) + 1) ^ 2 - (2 * (n * (d - 2) / 2) + 1) ^ 2 =
      4 * (n * (n * (d - 1) + 1)) := by ring
  rw [e1, e2] at h
  rw [← hK]
  linarith

end SuperRamanujan227.Dev.C56

namespace SuperRamanujan227.Main
open SuperRamanujan227.Dev.C56

theorem chk_claim_5_6 (n d : ℕ) (hd : 3 ≤ d) (hn : 2 ≤ n) (hnd : Even (n * d)) :
    2 * Real.sqrt ((d : ℝ) - 1) / (d : ℝ) - kthLargestRoot (Q n d) 1 >
      3 / (4 : ℝ) ^ ((1 : ℝ) / 3) * (n : ℝ) ^ (-(2 : ℝ) / 3) *
        (((d : ℝ) - 2 + 2 / (n : ℝ)) ^ ((4 : ℝ) / 3) /
          (((d : ℝ) - 1 + 1 / (n : ℝ)) ^ ((1 : ℝ) / 6) *
            ((d : ℝ) ^ 2 + 4 * ((d : ℝ) - 1) / (n : ℝ) + 4 / (n : ℝ) ^ 2) ^ ((5 : ℝ) / 6))) := by
  obtain ⟨c, hc, hQ⟩ := claim_5_5 n d hn hd hnd
  have hnR : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hdR : (2 : ℝ) < d := by exact_mod_cast (by omega : 2 < d)
  have hα : -1 < (n : ℝ) * ((d : ℝ) - 2) / 2 := by
    have : 0 < (n : ℝ) * ((d : ℝ) - 2) := mul_pos hnR (by linarith)
    linarith
  have h57 := theorem_5_7 n (by omega) _ hα
  have hroots : kthLargestRoot (Q n d) 1 =
      kthLargestRoot (jacobiSym ((n : ℝ) * ((d : ℝ) - 2) / 2) n) 1 := by
    unfold kthLargestRoot
    rw [hQ, roots_C_mul _ hc]
  rw [hroots]
  exact alg (n : ℝ) (d : ℝ) _ hnR hdR h57

end SuperRamanujan227.Main
end

theorem solution : type_of% @SuperRamanujan227.Main.chk_claim_5_6 := @SuperRamanujan227.Main.chk_claim_5_6
