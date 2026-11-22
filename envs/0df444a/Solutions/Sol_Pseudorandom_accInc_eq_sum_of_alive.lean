-- Prove2me | solution 1 for Pseudorandom.accInc_eq_sum_of_alive
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:00:30.214945+00:00
-- url     : https://prove2.me/submissions/bd017ae7-1f1d-4793-8202-da64028bf727

module
public import Definitions.Def_RequestProject_Pseudorandom_Bernstein
public import Definitions.Def_GJKKL_Vendor_Freedman

set_option autoImplicit true
@[expose] public section
public section
open Pseudorandom
open Finset
variable {α : Type*} [Fintype α] {n : ℕ}
variable {P : Fin n → α → ℝ} {X : ℕ → (Fin n → α) → ℝ} {G : ℕ → (Fin n → α) → Prop}
namespace Pseudorandom
theorem _root_.solution {ω : Fin n → α} (hall : ∀ i : Fin n, G i ω) :
    ∀ k, k ≤ n → accInc P X G k ω =
      ∑ i ∈ univ.filter (fun i : Fin n => (i : ℕ) < k), condAbsInc P X i ω
  | 0, _ => by simp [accInc]
  | k + 1, hk => by
    have hal : Alive G k ω := fun j hj => hall ⟨j, by omega⟩
    simp only [accInc, dif_pos (show k < n by omega), if_pos hal]
    rw [solution hall k (by omega)]
    have : (univ.filter fun i : Fin n => (i : ℕ) < k + 1) =
        insert ⟨k, by omega⟩ (univ.filter fun i : Fin n => (i : ℕ) < k) := by
      ext i; simp only [mem_filter, mem_univ, true_and, mem_insert, Fin.ext_iff]; omega
    rw [this, sum_insert (by simp)]
    ring
end Pseudorandom
