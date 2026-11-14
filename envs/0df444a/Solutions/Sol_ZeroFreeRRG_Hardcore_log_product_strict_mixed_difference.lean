-- Prove2me | solution 1 for ZeroFreeRRG.Hardcore.log_product_strict_mixed_difference
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T07:28:06.13164+00:00
-- url     : https://prove2.me/submissions/8cf22bff-4ace-4abb-953e-5990d91697ab

import Mathlib
set_option autoImplicit false

/-- The log of one plus a nonnegative product is strictly supermodular. -/
private theorem strict_log_supermodular (t x x' y y' : ℝ) (ht : 0 < t)
    (hx : 0 ≤ x) (hxx : x < x') (hy : 0 ≤ y) (hyy : y < y') :
    Real.log (1+t*x'*y') + Real.log (1+t*x*y) >
      Real.log (1+t*x'*y) + Real.log (1+t*x*y') := by
  have hxp : 0 ≤ x' := by linarith
  have hyp : 0 ≤ y' := by linarith
  have hp1 : 0 < 1+t*x'*y' := by positivity
  have hp2 : 0 < 1+t*x*y := by positivity
  have hp3 : 0 < 1+t*x'*y := by positivity
  have hp4 : 0 < 1+t*x*y' := by positivity
  rw [← Real.log_mul (ne_of_gt hp1) (ne_of_gt hp2),
      ← Real.log_mul (ne_of_gt hp3) (ne_of_gt hp4)]
  apply Real.log_lt_log (mul_pos hp3 hp4)
  have h := mul_pos ht (mul_pos (sub_pos.mpr hxx) (sub_pos.mpr hyy))
  nlinarith

/-- Weak and strict logarithmic supermodularity. -/
private theorem logsuper (t x x' y y' : ℝ) (ht : 0 ≤ t)
    (hx : 0 ≤ x) (hxx : x ≤ x') (hy : 0 ≤ y) (hyy : y ≤ y') :
    Real.log (1+t*x'*y') + Real.log (1+t*x*y) ≥
      Real.log (1+t*x'*y) + Real.log (1+t*x*y') ∧
    (0 < t → x < x' → y < y' →
      Real.log (1+t*x'*y') + Real.log (1+t*x*y) >
        Real.log (1+t*x'*y) + Real.log (1+t*x*y')) := by
  have hxp : 0 ≤ x' := le_trans hx hxx
  have hyp : 0 ≤ y' := le_trans hy hyy
  have hp1 : 0 < 1+t*x'*y' := by positivity
  have hp2 : 0 < 1+t*x*y := by positivity
  have hp3 : 0 < 1+t*x'*y := by positivity
  have hp4 : 0 < 1+t*x*y' := by positivity
  constructor
  · rw [← Real.log_mul (ne_of_gt hp1) (ne_of_gt hp2),
        ← Real.log_mul (ne_of_gt hp3) (ne_of_gt hp4)]
    apply Real.log_le_log (mul_pos hp3 hp4)
    have h := mul_nonneg ht (mul_nonneg (sub_nonneg.mpr hxx) (sub_nonneg.mpr hyy))
    nlinarith
  · intro ht' hxx' hyy'
    exact strict_log_supermodular t x x' y y' ht' hx hxx' hy hyy'

open scoped BigOperators


private theorem prod_factor {ι : Type} [Fintype ι] [DecidableEq ι] (f : ι → ℝ)
    (i j : ι) (hij : i ≠ j) :
    (∏ a, f a) = f i * f j * ∏ a ∈ (Finset.univ.erase i).erase j, f a := by
  have hj : j ∈ (Finset.univ : Finset ι).erase i := by simp [Ne.symm hij]
  calc
    _ = f i * ∏ a ∈ (Finset.univ : Finset ι).erase i, f a :=
      (Finset.mul_prod_erase Finset.univ f (Finset.mem_univ i)).symm
    _ = f i * (f j * ∏ a ∈ (Finset.univ.erase i).erase j, f a) := by
      rw [Finset.mul_prod_erase _ f hj]
    _ = _ := by ring

private noncomputable def switch {ι : Type} [DecidableEq ι] (x y : ι → ℝ) (S : Finset ι) (i : ι) : ℝ :=
  if i ∈ S then y i else x i

private theorem rest_same {ι : Type} [Fintype ι] [DecidableEq ι]
    (x y : ι → ℝ) (S : Finset ι) (i j : ι) :
    (∏ a ∈ (Finset.univ.erase i).erase j, switch x y (insert i (insert j S)) a) =
      ∏ a ∈ (Finset.univ.erase i).erase j, switch x y S a := by
  apply Finset.prod_congr rfl
  intro a ha
  have ha1 : a ≠ i := (Finset.mem_erase.mp (Finset.mem_erase.mp ha).2).1
  have ha2 : a ≠ j := (Finset.mem_erase.mp ha).1
  simp [switch,ha1,ha2]

private theorem rest_same_one {ι : Type} [Fintype ι] [DecidableEq ι]
    (x y : ι → ℝ) (S : Finset ι) (i j : ι) :
    (∏ a ∈ (Finset.univ.erase i).erase j, switch x y (insert i S) a) =
      ∏ a ∈ (Finset.univ.erase i).erase j, switch x y S a := by
  apply Finset.prod_congr rfl
  intro a ha
  have ha1 : a ≠ i := (Finset.mem_erase.mp (Finset.mem_erase.mp ha).2).1
  simp [switch,ha1]

private theorem rest_same_two {ι : Type} [Fintype ι] [DecidableEq ι]
    (x y : ι → ℝ) (S : Finset ι) (i j : ι) :
    (∏ a ∈ (Finset.univ.erase i).erase j, switch x y (insert j S) a) =
      ∏ a ∈ (Finset.univ.erase i).erase j, switch x y S a := by
  apply Finset.prod_congr rfl
  intro a ha
  have ha2 : a ≠ j := (Finset.mem_erase.mp ha).1
  simp [switch,ha2]


theorem solution {ι : Type} [Fintype ι] [DecidableEq ι] (θ : ℝ) (hθ : 0 < θ)
    (x y : ι → ℝ) (hx : ∀ i, 0 ≤ x i) (hxy : ∀ i, x i ≤ y i)
    (i j : ι) (hij : i ≠ j) (hi : x i < y i) (hj : x j < y j)
    (hrest : ∀ a, a ≠ i → a ≠ j → 0 < x a) :
    Real.log (1+θ*∏ a, (if a ∈ ({i,j} : Finset ι) then y a else x a)) +
      Real.log (1+θ*∏ a, x a) >
    Real.log (1+θ*∏ a, (if a = i then y a else x a)) +
      Real.log (1+θ*∏ a, (if a = j then y a else x a)) := by
  let P := ∏ a ∈ (Finset.univ.erase i).erase j, x a
  have hP : 0 < P := by
    dsimp [P]
    apply Finset.prod_pos
    intro a ha
    have hai : a ≠ i := (Finset.mem_erase.mp (Finset.mem_erase.mp ha).2).1
    have haj : a ≠ j := (Finset.mem_erase.mp ha).1
    exact hrest a hai haj
  have hh := (logsuper (θ*P) (x i) (y i) (x j) (y j)
    (le_of_lt (mul_pos hθ hP)) (hx i) (hxy i) (hx j) (hxy j)).2
    (mul_pos hθ hP) hi hj
  have h00 := prod_factor x i j hij
  have h10 := prod_factor (fun a => if a = i then y a else x a) i j hij
  have h01 := prod_factor (fun a => if a = j then y a else x a) i j hij
  have h11 := prod_factor (fun a => if a ∈ ({i,j} : Finset ι) then y a else x a) i j hij
  have hrest10 : (∏ a ∈ (Finset.univ.erase i).erase j, (if a = i then y a else x a)) = P := by
    dsimp [P]
    apply Finset.prod_congr rfl
    intro a ha
    have hai : a ≠ i := (Finset.mem_erase.mp (Finset.mem_erase.mp ha).2).1
    simp [hai]
  have hrest01 : (∏ a ∈ (Finset.univ.erase i).erase j, (if a = j then y a else x a)) = P := by
    dsimp [P]
    apply Finset.prod_congr rfl
    intro a ha
    have haj : a ≠ j := (Finset.mem_erase.mp ha).1
    simp [haj]
  have hrest11 : (∏ a ∈ (Finset.univ.erase i).erase j, (if a ∈ ({i,j} : Finset ι) then y a else x a)) = P := by
    dsimp [P]
    apply Finset.prod_congr rfl
    intro a ha
    have hai : a ≠ i := (Finset.mem_erase.mp (Finset.mem_erase.mp ha).2).1
    have haj : a ≠ j := (Finset.mem_erase.mp ha).1
    simp [hai,haj]
  rw [hrest10] at h10
  rw [hrest01] at h01
  rw [hrest11] at h11
  simp [hij,Ne.symm hij] at h10 h01 h11
  simp only [Finset.mem_insert,Finset.mem_singleton]
  rw [h00,h10,h01,h11]
  dsimp [P] at hh
  dsimp [P]
  convert hh using 1 <;> congr 2 <;> ring
