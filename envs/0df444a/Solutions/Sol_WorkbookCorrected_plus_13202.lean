-- Prove2me | solution 1 for WorkbookCorrected.plus_13202
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T14:19:28.125173+00:00
-- url     : https://prove2.me/submissions/3a47c623-b2bd-4a14-aea7-6215ed0450ea

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
private lemma advance (t z : ℝ) (ht : 0<t) (hz : 6*t/(5*t+6)<z) :
    6*(t+1)/(5*(t+1)+6)<z+(z/t)^2 := by
  let g := 6*t/(5*t+6)
  have hg : 0<g := by dsimp [g]; positivity
  have hzp : 0<z := lt_trans hg hz
  have hd : g/t ≤ z/t := (div_le_div_iff_of_pos_right ht).mpr (le_of_lt hz)
  have hs : (g/t)^2 ≤ (z/t)^2 := (sq_le_sq₀ (by positivity) (by positivity)).mpr hd
  have hi : g+(g/t)^2-6*(t+1)/(5*(t+1)+6)=180/((5*t+6)^2*(5*t+11)) := by
    dsimp [g]
    field_simp
    <;> ring
  have hp : 0<180/((5*t+6)^2*(5*t+11)) := by positivity
  nlinarith only [hz,hs,hi,hp]
theorem solution (x : ℕ → ℝ) (hx : x 1=1/2)
    (h : ∀ n : ℕ, 1≤n → x (n+1)=x n+(x n/(n:ℝ))^2) :
    ∀ n : ℕ, 3≤n → x n > 6*(n:ℝ)/(5*(n:ℝ)+6) := by
  have h2 : x 2=3/4 := by rw [h 1 (by omega),hx]; norm_num
  have h3 : x 3=57/64 := by rw [h 2 (by omega),h2]; norm_num
  intro n hn
  induction n,hn using Nat.le_induction with
  | base => norm_num [h3]
  | succ n hn ih =>
    rw [h n (by omega)]
    have ht : (0:ℝ)<n := by exact_mod_cast (show 0<n by omega)
    simpa only [Nat.cast_add,Nat.cast_one] using advance (n:ℝ) (x n) ht ih
example : (∀ (x : ℕ → ℝ) (hx : x 1=1/2)
    (h : ∀ n : ℕ, 1≤n → x (n+1)=x n+(x n/(n:ℝ))^2),
    ∀ n : ℕ, 3≤n → x n > 6*(n:ℝ)/(5*(n:ℝ)+6)) := @solution
#print axioms solution
