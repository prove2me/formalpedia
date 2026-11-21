-- Prove2me | solution 1 for RiemannMasullo.lattice_radial_weight_monomial_domination
-- status  : ACCEPTED   (prove)
-- author  : @dga471
-- created : 2026-11-21T03:18:02.008181+00:00
-- url     : https://prove2.me/submissions/5307e834-cc12-4dd2-8818-31680f848ce6

-- New supporting theorem for the discrete case of Masullo Appendix D.
import Mathlib

theorem solution (r j : ℕ) (a : Fin r → ℤ) :
    let v : EuclideanSpace ℝ (Fin r) := WithLp.toLp 2 (fun i => (a i:ℝ))
    (1+‖v‖)^j * (∏ i, (1+(a i:ℝ)^2)) ≤
      (((r:ℝ)+2)^j * 2^r) * ∏ i, |(a i:ℝ)|^(if a i=0 then 0 else j+2) := by
  classical
  dsimp only
  let v : EuclideanSpace ℝ (Fin r) := WithLp.toLp 2 (fun i => (a i:ℝ))
  let b := fun i => max (1:ℝ) |(a i:ℝ)|
  let B := ∏ i,b i
  have hb (i) : 1 ≤ b i := le_max_left _ _
  have hb0 (i) : 0 ≤ b i := by linarith [hb i]
  have hB : 1 ≤ B := Finset.one_le_prod (fun i _ => hb i)
  have hBi (i) : b i ≤ B := by
    have hrest : 1 ≤ ∏ k ∈ Finset.univ.erase i,b k := Finset.one_le_prod (fun k _ => hb k)
    dsimp only [B]
    rw [←Finset.mul_prod_erase Finset.univ b (Finset.mem_univ i)]
    simpa using mul_le_mul_of_nonneg_left hrest (hb0 i)
  have hcoord (i) : |(a i:ℝ)| ≤ B := (le_max_right _ _).trans (hBi i)
  have hnorm := EuclideanSpace.real_norm_sq_eq v
  have hs : ‖v‖^2 ≤ (r:ℝ)*B^2 := calc
    _ = ∑ i, (a i:ℝ)^2 := hnorm
    _ ≤ ∑ _ : Fin r, B^2 := Finset.sum_le_sum (fun i _ => by
      have h := mul_self_le_mul_self (abs_nonneg _) (hcoord i); nlinarith [sq_abs (a i:ℝ)])
    _ = _ := by simp
  have hscale : (r:ℝ) ≤ ((r:ℝ)+1)^2 := by nlinarith [sq_nonneg (r:ℝ)]
  have hn : ‖v‖ ≤ ((r:ℝ)+1)*B := by
    have h := mul_le_mul_of_nonneg_right hscale (sq_nonneg B)
    nlinarith [norm_nonneg v, mul_nonneg (by positivity : (0:ℝ) ≤ (r:ℝ)+1) (show 0 ≤ B by linarith)]
  have hrad : 1+‖v‖ ≤ ((r:ℝ)+2)*B := by nlinarith
  have hd : (∏ i, (1+(a i:ℝ)^2)) ≤ 2^r * B^2 := calc
    _ ≤ ∏ i, (2*(b i)^2) := by
      apply Finset.prod_le_prod (fun _ _ => by positivity)
      intro i _
      nlinarith [mul_self_le_mul_self (abs_nonneg _) (show |(a i:ℝ)| ≤ b i from le_max_right _ _),
        mul_self_le_mul_self (by norm_num : (0:ℝ) ≤ 1) (hb i),sq_abs (a i:ℝ)]
    _ = _ := by simp [Finset.prod_mul_distrib,Finset.prod_pow,B]
  have hmon (i) : (b i)^(j+2) = |(a i:ℝ)|^(if a i=0 then 0 else j+2) := by
    by_cases hi : a i = 0
    · simp [b,hi]
    · have ha : (1:ℤ) ≤ |a i| := by have := abs_pos.mpr hi; omega
      have hh : (1:ℝ) ≤ |(a i:ℝ)| := by exact_mod_cast ha
      simp [b,hi,max_eq_right hh]
  have hpow := pow_le_pow_left₀ (by positivity : 0 ≤ 1+‖v‖) hrad j
  calc
    _ ≤ (((r:ℝ)+2)*B)^j * (2^r*B^2) := mul_le_mul hpow hd (by positivity)
      (pow_nonneg (mul_nonneg (by positivity) (by linarith)) _)
    _ = (((r:ℝ)+2)^j*2^r)*B^(j+2) := by rw [mul_pow,pow_add]; ring
    _ = _ := by simp only [B,←Finset.prod_pow,hmon]
