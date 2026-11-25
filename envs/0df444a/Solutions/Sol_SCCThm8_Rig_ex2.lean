-- Prove2me | solution 1 for SCCThm8.Rig.ex2
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:54:12.937793+00:00
-- url     : https://prove2.me/submissions/74578c32-01f0-4a0e-9242-c973b13c6a62

module
public import Definitions.Def_SCCThm8_Defs
public import Definitions.Def_SCCThm8_Rigidity
public import Theorems.Thm_SCCThm8_Rig_exists_kset

set_option autoImplicit true
@[expose] public section
public section
open SCCThm8
open Finset
open SCCThm8.Rig
variable {n : ℕ}
variable {G : Type*} [Group G] {k : ℕ} {F : Finset (Fin (3 * k)) → G}
  {d : Fin (3 * k) → Fin (3 * k) → G}
namespace SCCThm8.Rig
theorem _root_.solution (hk : 2 ≤ k) {i j l : Fin (3 * k)} (hij : i ≠ j) (hil : i ≠ l) (hjl : j ≠ l) :
    ∃ A : Finset (Fin (3 * k)), A.card = k ∧ i ∈ A ∧ j ∉ A ∧ l ∉ A := by
  obtain ⟨A, hA, hs, ht⟩ := exists_kset (k := k) {i} {j, l} (by simp [hij, hil]) (by simp; omega)
    (by rw [card_pair hjl]; omega)
  exact ⟨A, hA, hs (by simp), disjoint_right.mp ht (by simp), disjoint_right.mp ht (by simp)⟩
end SCCThm8.Rig
