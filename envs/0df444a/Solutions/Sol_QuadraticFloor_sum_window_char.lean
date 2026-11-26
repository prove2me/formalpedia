-- Prove2me | solution 1 for QuadraticFloor.sum_window_char
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:58:58.100494+00:00
-- url     : https://prove2.me/submissions/623d4c53-27ff-42b1-995a-8bdea11b7e2e

module
public import Definitions.Def_QuadraticFloor_HalfPeriod
public import Definitions.Def_QuadraticFloor_SquareClass
public import Theorems.Thm_QuadraticFloor_psi_neg_one
public import Theorems.Thm_QuadraticFloor_sum_eta_psi_c8
public import Theorems.Thm_QuadraticFloor_sum_eta_psi_even
public import Theorems.Thm_QuadraticFloor_chi4_add
public import Theorems.Thm_QuadraticFloor_chi4_reflect
public import Theorems.Thm_QuadraticFloor_eta_mul_chi4_sq
public import Theorems.Thm_QuadraticFloor_ite_of_neg
public import Theorems.Thm_QuadraticFloor_ite_of_pos


set_option autoImplicit true
@[expose] public section
public section
open QuadraticFloor
open Finset
variable {p : ℕ} [hp : Fact p.Prime]
variable {A : ℕ}
namespace QuadraticFloor
theorem _root_.solution (hp2 : p ≠ 2) (hA : Odd A) (hpA : ¬ p ∣ A) (ψ : DirichletCharacter ℂ A)
    (k : ℂ) :
    ∑ x ∈ Icc 1 (4 * A * p), (eta p x : ℂ) * ψ (x : ZMod A) *
      (1 + (ZMod.χ₄ (x : ZMod 4) : ℂ) + k * ((ZMod.χ₈ (x : ZMod 8) : ℂ) + (ZMod.χ₈' (x : ZMod 8) : ℂ)))
      = ∑ x ∈ Icc 1 (4 * A * p), vartheta p ψ x := by
  have h8 := sum_eta_psi_c8 hp2 hA hpA ψ (fun y => (ZMod.χ₈ y : ℂ)) (by
    intro y; have : ZMod.χ₈ (y + 4) = -ZMod.χ₈ y := by revert y; decide
    simp [this])
  have h8' := sum_eta_psi_c8 hp2 hA hpA ψ (fun y => (ZMod.χ₈' y : ℂ)) (by
    intro y; have : ZMod.χ₈' (y + 4) = -ZMod.χ₈' y := by revert y; decide
    simp [this])
  have hsplit : ∀ x ∈ Icc 1 (4 * A * p), (eta p x : ℂ) * ψ (x : ZMod A) *
      (1 + (ZMod.χ₄ (x : ZMod 4) : ℂ) + k * ((ZMod.χ₈ (x : ZMod 8) : ℂ) + (ZMod.χ₈' (x : ZMod 8) : ℂ)))
      = (eta p x : ℂ) * ψ (x : ZMod A) * 1 +
        (eta p x : ℂ) * ψ (x : ZMod A) * (ZMod.χ₄ (x : ZMod 4) : ℂ) +
        k * ((eta p x : ℂ) * ψ (x : ZMod A) * (ZMod.χ₈ (x : ZMod 8) : ℂ) +
          (eta p x : ℂ) * ψ (x : ZMod A) * (ZMod.χ₈' (x : ZMod 8) : ℂ)) := by
    intro x _; ring
  rw [sum_congr rfl hsplit, sum_add_distrib, sum_add_distrib, ← mul_sum, sum_add_distrib]
  beta_reduce at h8 h8'
  rw [h8, h8', add_zero, mul_zero, add_zero]
  rcases psi_neg_one ψ with hψ | hψ
  · -- `ψ` even: the term with `χ_{-4}` vanishes
    have hper : ∀ x, (fun x : ℕ => (ZMod.χ₄ (x : ZMod 4) : ℂ)) (x + 4 * A * p) =
        (fun x : ℕ => (ZMod.χ₄ (x : ZMod 4) : ℂ)) x := by
      intro x
      beta_reduce
      rw [chi4_add]
    have href : ∀ x ≤ 8 * A * p, (fun x : ℕ => (ZMod.χ₄ (x : ZMod 4) : ℂ)) (8 * A * p - x) =
        -1 * (fun x : ℕ => (ZMod.χ₄ (x : ZMod 4) : ℂ)) x := by
      intro x hx
      beta_reduce
      rw [chi4_reflect A p hx]
      push_cast; ring
    have h4 := sum_eta_psi_even hp2 hA ψ (fun x => (ZMod.χ₄ (x : ZMod 4) : ℂ)) (-1)
      hper href (by rw [hψ]; ring)
    beta_reduce at h4
    rw [h4, add_zero]
    apply sum_congr rfl
    intro x _
    unfold vartheta
    have : ψ (-1) ≠ -1 := by rw [hψ]; norm_num
    rw [ite_of_neg this, mul_one, eta_mul_chi4_sq]
  · -- `ψ` odd: the term with `1` vanishes
    have h1 := sum_eta_psi_even hp2 hA ψ (fun _ => (1 : ℂ)) 1
      (fun x => rfl) (fun x _ => by rw [one_mul]) (by rw [hψ]; ring)
    beta_reduce at h1
    rw [h1, zero_add]
    apply sum_congr rfl
    intro x _
    unfold vartheta
    rw [ite_of_pos hψ]
    ring
end QuadraticFloor
