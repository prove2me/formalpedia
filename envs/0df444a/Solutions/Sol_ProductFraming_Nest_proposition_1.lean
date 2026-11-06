-- Prove2me | solution 1 for ProductFraming.Nest.proposition_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-05T06:53:55.885699+00:00
-- url     : https://prove2.me/submissions/163a92c4-ac6f-4251-8eff-722e8c5a8378

import Mathlib
import Definitions.Def_ProductFraming_Nest_Model
import Definitions.Def_ProductFraming_Nest_Algorithm

open Finset ProductFraming.Nest

namespace PFNProp1Aux

lemma U_nonneg {n : ℕ} (p : ℕ) (r : Fin n → ℝ) (P : Fin n → Finset (Fin n) → ℝ) (x : ℕ) :
    0 ≤ U p r P x := by
  unfold U G
  have hmem : (∅ : Finset (Fin n)) ∈ univ.filter (fun S : Finset (Fin n) => S.card ≤ x * p) := by
    simp
  have := Finset.le_sup' (R r P) hmem
  simpa [R] using this

/-- Downward induction from `y` to `1`. -/
lemma down {y : ℕ} (Q : ℕ → Prop) (h0 : 1 ≤ y → Q y)
    (hs : ∀ x, 1 ≤ x → x < y → Q (x + 1) → Q x) : ∀ x, 1 ≤ x → x ≤ y → Q x := by
  have : ∀ d x, x + d = y → 1 ≤ x → Q x := by
    intro d
    induction d with
    | zero => intro x hx h1; subst hx; exact h0 (by simpa using h1)
    | succ d ih =>
      intro x hx h1
      exact hs x h1 (by omega) (ih (x + 1) (by omega) (by omega))
  intro x h1 h2
  exact this (y - x) x (by omega) h1

variable {n : ℕ} {p : ℕ} {r : Fin n → ℝ} {P : Fin n → Finset (Fin n) → ℝ} {y : ℕ}
  {S : ℕ → Finset (Fin n)}

lemma run_mono (hS : IsNestRun p r P y S) {j x : ℕ} (hj : 1 ≤ j) (hjx : j ≤ x) (hxy : x ≤ y) :
    S j ⊆ S x := by
  have : ∀ d, ∀ x, x = j + d → x ≤ y → S j ⊆ S x := by
    intro d
    induction d with
    | zero => intro x hx _; subst hx; exact subset_refl _
    | succ d ih =>
      intro x hx hxy
      have h1 := ih (j + d) rfl (by omega)
      have h2 := (hS.2 (j + d) (by omega) (by omega)).1
      subst hx
      exact h1.trans h2
  exact this (x - j) x (by omega) hxy

lemma mem_consideration (i : Fin n) (x : ℕ) :
    i ∈ consideration (nestFraming y S) x ↔ ∃ j, 1 ≤ j ∧ j ≤ x ∧ j ≤ y ∧ i ∈ S j := by
  unfold consideration
  rw [Finset.mem_filter]
  simp only [mem_univ, true_and]
  unfold nestFraming
  split_ifs with h
  · have hmem := min'_mem _ h
    simp only [mem_filter, mem_Icc] at hmem
    constructor
    · rintro ⟨_, h2⟩
      exact ⟨_, hmem.1.1, h2, hmem.1.2, hmem.2⟩
    · rintro ⟨j, hj1, hjx, hjy, hij⟩
      have hle : ((Icc 1 y).filter (fun x => i ∈ S x)).min' h ≤ j :=
        min'_le _ _ (by simp [mem_filter, mem_Icc]; exact ⟨⟨hj1, hjy⟩, hij⟩)
      exact ⟨hmem.1.1, le_trans hle hjx⟩
  · constructor
    · rintro ⟨h1, _⟩; omega
    · rintro ⟨j, hj1, _, hjy, hij⟩
      exact absurd ⟨j, by simp [mem_filter, mem_Icc]; exact ⟨⟨hj1, hjy⟩, hij⟩⟩ h

lemma consideration_eq (hS : IsNestRun p r P y S) {x : ℕ} (hx : 1 ≤ x) (hy : 1 ≤ y) :
    consideration (nestFraming y S) x = S (min x y) := by
  ext i
  rw [mem_consideration]
  constructor
  · rintro ⟨j, hj1, hjx, hjy, hij⟩
    exact run_mono hS hj1 (le_min hjx hjy) (min_le_right _ _) hij
  · intro hi
    exact ⟨min x y, le_min hx hy, min_le_left _ _, min_le_right _ _, hi⟩

lemma run_card (hS : IsNestRun p r P y S) :
    ∀ x, 1 ≤ x → x ≤ y → (S x).card = min (S y).card (x * p) := by
  apply down (y := y) (fun x => (S x).card = min (S y).card (x * p))
  · intro _; exact (min_eq_left hS.1.1).symm
  · intro x hx hxy ih
    rw [(hS.2 x hx hxy).2.1, ih]
    have : x * p ≤ (x + 1) * p := Nat.mul_le_mul_right p (by omega)
    omega

lemma run_ratio (hS : IsNestRun p r P y S) :
    ∀ x, 1 ≤ x → x ≤ y → R r P (S y) / ((S y).card : ℝ) ≤ R r P (S x) / ((S x).card : ℝ) := by
  apply down (y := y) (fun x => R r P (S y) / ((S y).card : ℝ) ≤ R r P (S x) / ((S x).card : ℝ))
  · intro _; exact le_refl _
  · intro x hx hxy ih
    exact le_trans ih (hS.2 x hx hxy).2.2

end PFNProp1Aux

open PFNProp1Aux in
theorem solution (n m p : ℕ) (hm : 1 ≤ m) (hp : 1 ≤ p) (r : Fin n → ℝ)
    (P : Fin n → Finset (Fin n) → ℝ) (hP : IsChoiceModel P) (lam : ℕ → ℝ) (hlam : IsPageLaw m lam) :
    ∀ y ∈ Icc 1 m, ∀ S : ℕ → Finset (Fin n), IsNestRun p r P y S →
      U p r P y / (y : ℝ) * Emin m lam (y : ℝ) ≤ VNest m r P lam y S := by
  intro y hy S hS
  rw [mem_Icc] at hy
  have hypos : (0 : ℝ) < y := by exact_mod_cast hy.1
  have hU0 := U_nonneg p r P y
  have hRy : R r P (S y) = U p r P y := hS.1.2
  -- the key per-consumer bound: `(U(y)/y) z ≤ R(S(z))` for `z ∈ [1, y]`
  have hkey : ∀ z, 1 ≤ z → z ≤ y → U p r P y / (y : ℝ) * (z : ℝ) ≤ R r P (S z) := by
    intro z hz1 hzy
    have hcard := run_card hS z hz1 hzy
    have hrat := run_ratio hS z hz1 hzy
    set c := (S y).card with hc
    by_cases hc0 : c = 0
    · have hSy : S y = ∅ := card_eq_zero.mp hc0
      have hzp : 1 ≤ z * p := by simpa using Nat.mul_le_mul hz1 hp
      have hSz : S z = ∅ := card_eq_zero.mp (by rw [hcard, hc0]; simp)
      rw [← hRy, hSy, hSz]
      simp [R]
    · have hzp : 1 ≤ z * p := by simpa using Nat.mul_le_mul hz1 hp
      have ha0 : 0 < (S z).card := by rw [hcard]; omega
      have hcR : (0 : ℝ) < c := by exact_mod_cast Nat.pos_of_ne_zero hc0
      have haR : (0 : ℝ) < (S z).card := by exact_mod_cast ha0
      -- `z |S(y)| ≤ |S(z)| y` in ℕ
      have hnat : z * c ≤ (S z).card * y := by
        rw [hcard]
        have hcy : c ≤ y * p := hS.1.1
        rcases le_total c (z * p) with h | h
        · rw [min_eq_left h]; rw [mul_comm]; exact Nat.mul_le_mul_left c hzy
        · rw [min_eq_right h]
          calc z * c ≤ z * (y * p) := Nat.mul_le_mul_left z hcy
            _ = z * p * y := by ring
      have hreal : (z : ℝ) * c ≤ ((S z).card : ℝ) * y := by exact_mod_cast hnat
      rw [hRy, div_le_div_iff₀ hcR haR] at hrat
      rw [div_mul_eq_mul_div, div_le_iff₀ hypos]
      have h1 : U p r P y * z * c ≤ U p r P y * ((S z).card * y) := by
        rw [mul_assoc]; exact mul_le_mul_of_nonneg_left hreal hU0
      have h2 : U p r P y * ((S z).card : ℝ) * y ≤ R r P (S z) * c * y :=
        mul_le_mul_of_nonneg_right hrat hypos.le
      have h3 : U p r P y * z * c ≤ R r P (S z) * y * c := by nlinarith
      exact le_of_mul_le_mul_right h3 hcR
  unfold VNest V Emin
  rw [mul_sum]
  apply sum_le_sum
  intro x hx
  have hx1 := (mem_Icc.mp hx).1
  rw [consideration_eq hS hx1 hy.1]
  have hmin : min (x : ℝ) (y : ℝ) = ((min x y : ℕ) : ℝ) := by push_cast; rfl
  rw [hmin, mul_left_comm]
  apply mul_le_mul_of_nonneg_left _ (hlam.1 x hx)
  exact hkey (min x y) (le_min hx1 hy.1) (min_le_right _ _)
