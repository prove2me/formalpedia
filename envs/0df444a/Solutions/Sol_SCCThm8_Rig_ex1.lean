-- Prove2me | solution 1 for SCCThm8.Rig.ex1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:52:29.254433+00:00
-- url     : https://prove2.me/submissions/6c46b9bb-9e49-4f19-93e8-fb78ba4f48b3

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
theorem _root_.solution (hk : 2 ≤ k) {i j : Fin (3 * k)} (hij : i ≠ j) :
    ∃ A : Finset (Fin (3 * k)), A.card = k ∧ i ∈ A ∧ j ∉ A := by
  obtain ⟨A, hA, hs, ht⟩ := exists_kset (k := k) {i} {j} (by simpa using hij) (by simp; omega)
    (by simp; omega)
  exact ⟨A, hA, hs (by simp), disjoint_right.mp ht (by simp)⟩
end SCCThm8.Rig
