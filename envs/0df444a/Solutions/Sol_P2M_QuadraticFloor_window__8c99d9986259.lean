-- Prove2me | solution 1 for P2M_QuadraticFloor_window__8c99d9986259
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:57:54.856373+00:00
-- url     : https://prove2.me/submissions/501f73b8-784a-49c1-8e56-7146e7709e73

module
public import Definitions.Def_QuadraticFloor_HalfPeriod
public import Definitions.Def_QuadraticFloor_SquareClass
public import Theorems.Thm_QuadraticFloor_cast_add_of_dvd
public import Theorems.Thm_QuadraticFloor_kap_disc
public import Theorems.Thm_P2M_QuadraticFloor_eta_eq__74b5fa8b45c2
public import Theorems.Thm_P2M_QuadraticFloor_root_count__8bce20a9a3c2
public import Theorems.Thm_QuadraticFloor_odd_of_ne_two


set_option autoImplicit true
@[expose] public section
public section
open QuadraticFloor
open Finset
variable {p : ℕ} [hp : Fact p.Prime]
namespace QuadraticFloor
theorem _root_.solution (hp2 : p ≠ 2) {A : ℕ} (hA : Odd A) (hpA : ¬ p ∣ A) {B C : ℤ}
    (hBC : Admissible A B C) {d : ℕ} (hdD : (d : ℤ) = B ^ 2 - 4 * A * C) (hd4A : d < 4 * A)
    (hd8 : d % 8 = if Even C then 1 else 5) :
    floorSum A B C p - (C.negOnePow : ℤ) =
      2 * ∑ x ∈ (Icc 1 (4 * A * p)).filter (fun x => x % (8 * A) = d), eta p x := by
  have hAB : Even ((A : ℤ) + B) := by
    have h1 : Odd (A : ℤ) := by exact_mod_cast hA
    exact h1.add_odd hBC.1
  have hpA' : ¬ (p : ℤ) ∣ (A : ℤ) := by exact_mod_cast hpA
  rw [root_count' hp2 C hAB hpA', ← hdD]
  have hterm : ∀ j : ℕ, (C.negOnePow : ℤ) * legendreSym p ((d : ℤ) + 8 * A * j) =
      eta p (d + 8 * A * j) := by
    intro j
    rw [eta_eq' hp2, show ((d + 8 * A * j : ℕ) : ZMod 8) = (d : ZMod 8) by
      rw [show d + 8 * A * j = d + 8 * (A * j) by ring]; exact cast_add_of_dvd _ _ _ (dvd_mul_right _ _),
      kap_disc hd8]
    push_cast; ring
  have hreindex : ∑ j ∈ range ((p + 1) / 2), eta p (d + 8 * A * j) =
      ∑ x ∈ (Icc 1 (4 * A * p)).filter (fun x => x % (8 * A) = d), eta p x := by
    have hA0 : 0 < A := hA.pos
    have h8A : 0 < 8 * A := by omega
    have hd1 : 1 ≤ d := by
      have := hBC.2.2.1; omega
    obtain ⟨m, hm⟩ := odd_of_ne_two hp2
    refine sum_nbij' (fun j => d + 8 * A * j) (fun x => x / (8 * A)) ?_ ?_ ?_ ?_ ?_
    · intro j hj
      rw [mem_range] at hj
      rw [mem_filter, mem_Icc]
      refine ⟨⟨by omega, ?_⟩, ?_⟩
      · have hj' : 2 * j ≤ p - 1 := by omega
        have : 8 * A * j ≤ 4 * A * (p - 1) := by
          rw [show 8 * A * j = 4 * A * (2 * j) by ring]; exact Nat.mul_le_mul_left _ hj'
        have h2 : 4 * A * (p - 1) + 4 * A = 4 * A * p := by
          rw [← Nat.mul_add_one]; congr 1; omega
        omega
      · rw [Nat.add_mul_mod_self_left]; exact Nat.mod_eq_of_lt (by omega)
    · intro x hx
      rw [mem_filter, mem_Icc] at hx
      rw [mem_range]
      obtain ⟨⟨-, hx2⟩, hx3⟩ := hx
      have hdiv := Nat.mod_add_div x (8 * A)
      rw [hx3] at hdiv
      have : 8 * A * (x / (8 * A)) < 4 * A * p := by omega
      have : 4 * A * (2 * (x / (8 * A))) < 4 * A * p := by
        rw [show 4 * A * (2 * (x / (8 * A))) = 8 * A * (x / (8 * A)) by ring]; exact this
      have := Nat.lt_of_mul_lt_mul_left this
      omega
    · intro j _
      rw [Nat.add_mul_div_left _ _ h8A, Nat.div_eq_of_lt (by omega), zero_add]
    · intro x hx
      rw [mem_filter, mem_Icc] at hx
      have hdiv := Nat.mod_add_div x (8 * A)
      rw [hx.2] at hdiv
      exact hdiv
    · intro j _; rfl
  rw [← hreindex, ← sum_congr rfl fun j _ => hterm j, mul_add, mul_one, add_sub_cancel_left,
    mul_sum, mul_sum, mul_sum]
  exact sum_congr rfl fun j _ => by ring
end QuadraticFloor
