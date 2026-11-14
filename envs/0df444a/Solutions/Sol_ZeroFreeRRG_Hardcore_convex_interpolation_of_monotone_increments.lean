-- Prove2me | solution 1 for ZeroFreeRRG.Hardcore.convex_interpolation_of_monotone_increments
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T06:33:29.141376+00:00
-- url     : https://prove2.me/submissions/125e8e1b-dd60-4a64-9e4a-2d8e7938f7ed

import Mathlib
set_option autoImplicit false
open Set

private def line (v : ℕ → ℝ) (n : ℕ) (x : ℝ) : ℝ :=
  v n + (x-(n:ℝ))*(v (n+1)-v n)

private noncomputable def interp (v : ℕ → ℝ) (x : ℝ) : ℝ := line v ⌊x⌋₊ x

private theorem affine_support (v : ℕ → ℝ)
    (hv : ∀ n, v (n+1)-v n ≤ v (n+2)-v (n+1))
    (x : ℝ) (hx : 0 ≤ x) (n : ℕ) : line v n x ≤ interp v x := by
  let m := ⌊x⌋₊
  have hm0 : (m:ℝ) ≤ x := Nat.floor_le hx
  have hm1 : x < (m:ℝ)+1 := Nat.lt_floor_add_one x
  have step (j : ℕ) : line v (j+1) x - line v j x =
      (x-((j:ℝ)+1))*((v (j+2)-v (j+1))-(v (j+1)-v j)) := by
    dsimp [line]
    push_cast
    ring
  have left : ∀ N n : ℕ, n ≤ N → (N:ℝ) ≤ x → line v n x ≤ line v N x := by
    intro N n hn
    induction N, hn using Nat.le_induction with
    | base => intro _; rfl
    | succ j hnj ih =>
      intro hJ
      have hj : (j:ℝ) ≤ x := by push_cast at hJ; linarith
      have hstep : line v j x ≤ line v (j+1) x := by
        have hprod := mul_nonneg (show 0 ≤ x-((j:ℝ)+1) by push_cast at hJ; linarith)
          (sub_nonneg.mpr (hv j))
        linarith [step j]
      exact (ih hj).trans hstep
  have right : ∀ N m' : ℕ, m' ≤ N → x ≤ (m':ℝ)+1 → line v N x ≤ line v m' x := by
    intro N m' hn
    induction N, hn using Nat.le_induction with
    | base => intro _; rfl
    | succ j hmj ih =>
      intro hm'
      have hstep : line v (j+1) x ≤ line v j x := by
        have hj : (m':ℝ) ≤ j := by exact_mod_cast hmj
        have hprod := mul_nonpos_of_nonpos_of_nonneg (show x-((j:ℝ)+1) ≤ 0 by linarith)
          (sub_nonneg.mpr (hv j))
        linarith [step j]
      exact hstep.trans (ih hm')
  change line v n x ≤ line v m x
  rcases le_total n m with hn | hn
  · exact left m n hn hm0
  · exact right n m hn hm1.le

theorem solution (v : ℕ → ℝ)
    (hv : ∀ n, v (n+1)-v n ≤ v (n+2)-v (n+1)) :
    ConvexOn ℝ (Ici 0) (fun x =>
      (1-x+(⌊x⌋₊:ℝ))*v ⌊x⌋₊ + (x-(⌊x⌋₊:ℝ))*v (⌊x⌋₊+1)) := by
  have hformula (x : ℝ) :
      (1-x+(⌊x⌋₊:ℝ))*v ⌊x⌋₊ + (x-(⌊x⌋₊:ℝ))*v (⌊x⌋₊+1) = interp v x := by
    dsimp [interp,line]
    ring
  simp_rw [hformula]
  refine ⟨convex_Ici 0, ?_⟩
  intro x hx y hy a b ha hb hab
  change 0 ≤ x at hx
  change 0 ≤ y at hy
  have hz : 0 ≤ a*x+b*y := add_nonneg (mul_nonneg ha hx) (mul_nonneg hb hy)
  let z := a*x+b*y
  let k := ⌊z⌋₊
  have hx' := affine_support v hv x hx k
  have hy' := affine_support v hv y hy k
  have hsum := add_le_add (mul_le_mul_of_nonneg_left hx' ha) (mul_le_mul_of_nonneg_left hy' hb)
  change interp v (a*x+b*y) ≤ a*interp v x+b*interp v y
  have heq : interp v (a*x+b*y) = a*line v k x+b*line v k y := by
    change line v k (a*x+b*y) = _
    dsimp [line]
    have haux := congrArg (fun w : ℝ => w*(v k-(k:ℝ)*(v (k+1)-v k))) hab
    nlinarith [haux]
  rw [heq]
  exact hsum
