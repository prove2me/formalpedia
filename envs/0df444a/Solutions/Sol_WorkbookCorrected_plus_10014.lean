-- Prove2me | solution 1 for WorkbookCorrected.plus_10014
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T14:11:04.482125+00:00
-- url     : https://prove2.me/submissions/3491f10f-b9cd-495b-ab05-387f692fa58d

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
private lemma step (x y t : ℝ) (ht : 0<t) (hy : 0<y)
    (hx : 1/t ≤ x) (h : y^2+y=x) : 1/(t+1) ≤ y := by
  have hp : 0<t+1 := by linarith
  have hsmall : (1/(t+1))^2+1/(t+1) ≤ 1/t := by
    apply (le_div_iff₀ ht).mpr
    have hi : 1-((1/(t+1))^2+1/(t+1))*t=1/(t+1)^2 := by field_simp; ring
    have hh : 0 ≤ 1/(t+1)^2 := by positivity
    nlinarith only [hi,hh]
  have hr : 0<1/(t+1) := by positivity
  by_contra hn
  have hd : 0<1/(t+1)-y := by linarith only [hn]
  have hh := mul_pos hd (show 0<1/(t+1)+y+1 by linarith only [hr,hy])
  nlinarith only [hh,hsmall,hx,h]
theorem solution (a : ℕ → ℝ) (h0 : a 1=1) (hp : ∀ n : ℕ, 1≤n → 0<a n)
    (h : ∀ n : ℕ, 1≤n → (a (n+1))^2+a (n+1)=a n) :
    ∀ n : ℕ, 1≤n → a n ≥ 1/(n:ℝ) := by
  intro n hn
  induction n,hn using Nat.le_induction with
  | base => norm_num [h0]
  | succ n hn ih =>
    have ht : (0:ℝ)<n := by exact_mod_cast (show 0<n by omega)
    have hh := step (a n) (a (n+1)) (n:ℝ) ht (hp (n+1) (by omega)) ih (h n hn)
    simpa only [Nat.cast_add,Nat.cast_one] using hh
example : (∀ (a : ℕ → ℝ) (h0 : a 1=1) (hp : ∀ n : ℕ, 1≤n → 0<a n)
    (h : ∀ n : ℕ, 1≤n → (a (n+1))^2+a (n+1)=a n),
    ∀ n : ℕ, 1≤n → a n ≥ 1/(n:ℝ)) := @solution
#print axioms solution
