-- Prove2me | solution 1 for SubstOverbooking.Structure.theorem1_submodular_iff_decreasingDifferences
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-07T07:29:17.245074+00:00
-- url     : https://prove2.me/submissions/45c55b6e-2966-457b-ad89-166f231ee3cd

import Mathlib
import Definitions.Def_SubstOverbooking_Structure_Setting
import Definitions.Def_Supermodularity_Monotonicity_SupermodularOn

open SubstOverbooking.Structure

private theorem mem_product {n : ℕ} (T : Fin n → Set ℝ) (x : Fin n → ℝ) :
    x ∈ Set.pi Set.univ T ↔ ∀ k, x k ∈ T k := by simp

private theorem update_mem {n : ℕ} (T : Fin n → Set ℝ) (x : Fin n → ℝ)
    (hx : x ∈ Set.pi Set.univ T) (i : Fin n) (t : ℝ) (ht : t ∈ T i) :
    Function.update x i t ∈ Set.pi Set.univ T := by
  classical
  rw [mem_product] at hx ⊢
  intro k
  by_cases h : k = i
  · subst k; simpa using ht
  · simpa [Function.update_of_ne h] using hx k

private theorem marginal {n : ℕ} (T : Fin n → Set ℝ)
    (f : (Fin n → ℝ) → ℝ) (hdd : DecreasingDifferencesOn f (Set.pi Set.univ T))
    (i : Fin n) (t : ℝ) (ht : t ∈ T i) :
    ∀ (s : Finset (Fin n)) (x y : Fin n → ℝ),
      x ∈ Set.pi Set.univ T → y ∈ Set.pi Set.univ T →
      x ≤ y → x i = y i → (∀ k, k ∉ s → x k = y k) → x i ≤ t →
      f (Function.update y i t) - f y ≤ f (Function.update x i t) - f x := by
  classical
  intro s
  induction s using Finset.induction_on with
  | empty =>
    intro x y hx hy hxy hi he hxt
    have e : x = y := funext (fun k => he k (by simp))
    simp [e]
  | @insert j s hjs ih =>
    intro x y hx hy hxy hi he hxt
    let y' := Function.update y j (x j)
    have hy' : y' ∈ Set.pi Set.univ T := update_mem T y hy j (x j) ((mem_product T x).mp hx j)
    have hxy' : x ≤ y' := by
      intro k
      by_cases h : k = j
      · subst k; simp [y']
      · simpa [y', Function.update_of_ne h] using hxy k
    have hi' : x i = y' i := by
      by_cases h : i = j
      · subst i; simp [y']
      · simpa [y', Function.update_of_ne h] using hi
    have he' : ∀ k, k ∉ s → x k = y' k := by
      intro k hk
      by_cases h : k = j
      · subst k; simp [y']
      · simpa [y', Function.update_of_ne h] using he k (by simp [hk, h])
    have H := ih x y' hx hy' hxy' hi' he' hxt
    by_cases hij : i = j
    · have ey : y' = y := by
        ext k
        by_cases h : k = j
        · subst k; simpa [y', hij] using hi
        · simp [y', Function.update_of_ne h]
      simpa [ey] using H
    have ey : Function.update y' j (y j) = y := by
      ext k
      by_cases h : k = j
      · subst k; simp
      · simp [y', Function.update_of_ne h]
    have eij : Function.update (Function.update y' i t) j (y j) = Function.update y i t := by
      rw [Function.update_comm hij, ey]
    have D := hdd y' hy' i j hij t (y j) (by simpa [hi'] using hxt)
      (by simpa [y'] using hxy j) (update_mem T y' hy' i t ht)
      (update_mem T y' hy' j (y j) ((mem_product T y).mp hy j))
      (update_mem T _ (update_mem T y' hy' i t ht) j (y j) ((mem_product T y).mp hy j))
    rw [ey, eij] at D
    linarith

private theorem lattice_inequality {n : ℕ} (T : Fin n → Set ℝ)
    (f : (Fin n → ℝ) → ℝ) (hdd : DecreasingDifferencesOn f (Set.pi Set.univ T)) :
    ∀ (s : Finset (Fin n)) (x y : Fin n → ℝ),
      x ∈ Set.pi Set.univ T → y ∈ Set.pi Set.univ T →
      (∀ k, k ∉ s → x k ≤ y k) →
      f (x ⊔ y) + f (x ⊓ y) ≤ f x + f y := by
  classical
  intro s
  induction s using Finset.induction_on with
  | empty =>
    intro x y hx hy he
    have hxy : x ≤ y := fun k => he k (by simp)
    simp [sup_eq_right.mpr hxy, inf_eq_left.mpr hxy, add_comm]
  | @insert j s hjs ih =>
    intro x y hx hy he
    by_cases hj : x j ≤ y j
    · apply ih x y hx hy
      intro k hk
      by_cases h : k = j
      · subst k; exact hj
      · exact he k (by simp [hk, h])
    have hyj : y j ≤ x j := le_of_lt (lt_of_not_ge hj)
    let x' := Function.update x j (y j)
    have hx' : x' ∈ Set.pi Set.univ T := update_mem T x hx j (y j) ((mem_product T y).mp hy j)
    have H := ih x' y hx' hy (by
      intro k hk
      by_cases h : k = j
      · subst k; simp [x']
      · simpa [x', Function.update_of_ne h] using he k (by simp [hk, h]))
    have hs : x' ⊔ y ∈ Set.pi Set.univ T := by
      rw [mem_product]
      intro k
      rcases le_total (x' k) (y k) with h | h
      · simpa [sup_eq_right.mpr h] using (mem_product T y).mp hy k
      · simpa [sup_eq_left.mpr h] using (mem_product T x').mp hx' k
    have D := marginal T f hdd j (x j) ((mem_product T x).mp hx j)
      Finset.univ x' (x' ⊔ y) hx' hs le_sup_left
      (by simp [x']) (by simp) (by simpa [x'] using hyj)
    have e1 : Function.update x' j (x j) = x := by
      ext k
      by_cases h : k = j
      · subst k; simp
      · simp [x', Function.update_of_ne h]
    have e2 : Function.update (x' ⊔ y) j (x j) = x ⊔ y := by
      ext k
      by_cases h : k = j
      · subst k; simp [Pi.sup_apply, sup_eq_left.mpr hyj]
      · simp [x', Pi.sup_apply, Function.update_of_ne h]
    have e3 : x' ⊓ y = x ⊓ y := by
      ext k
      by_cases h : k = j
      · subst k; simp [x', Pi.inf_apply, inf_eq_right.mpr hyj]
      · simp [x', Pi.inf_apply, Function.update_of_ne h]
    rw [e1, e2] at D
    rw [e3] at H
    linarith

theorem solution {n : ℕ} (T : Fin n → Set ℝ)
    (f : (Fin n → ℝ) → ℝ) :
    Supermodularity.Monotonicity.SupermodularOn (fun s => - f s) (Set.pi Set.univ T) ↔
      DecreasingDifferencesOn f (Set.pi Set.univ T) := by
  classical
  constructor
  · intro h s hs i j hij si sj hi hj hsi hsj hsij
    have H := h hsi hsj
    have es : Function.update s i si ⊔ Function.update s j sj =
        Function.update (Function.update s i si) j sj := by
      ext k
      by_cases hki : k = i
      · subst k; simp [Pi.sup_apply, Function.update_of_ne hij, sup_eq_left.mpr hi]
      by_cases hkj : k = j
      · subst k; simp [Pi.sup_apply, Function.update_of_ne hij.symm, sup_eq_right.mpr hj]
      · simp [Pi.sup_apply, Function.update_of_ne hki, Function.update_of_ne hkj]
    have ei : Function.update s i si ⊓ Function.update s j sj = s := by
      ext k
      by_cases hki : k = i
      · subst k; simp [Pi.inf_apply, Function.update_of_ne hij, inf_eq_right.mpr hi]
      by_cases hkj : k = j
      · subst k; simp [Pi.inf_apply, Function.update_of_ne hij.symm, inf_eq_left.mpr hj]
      · simp [Pi.inf_apply, Function.update_of_ne hki, Function.update_of_ne hkj]
    rw [es, ei] at H
    linarith
  · intro h x hx y hy
    have H := lattice_inequality T f h Finset.univ x y hx hy (by simp)
    linarith

#print axioms solution
