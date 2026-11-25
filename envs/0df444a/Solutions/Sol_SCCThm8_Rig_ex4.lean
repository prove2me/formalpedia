-- Prove2me | solution 1 for SCCThm8.Rig.ex4
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:54:15.131124+00:00
-- url     : https://prove2.me/submissions/e5e9084a-4e58-44fd-a391-534f71788e8e

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
theorem _root_.solution (hk : 2 ≤ k) {i i' j j' : Fin (3 * k)} (h1 : i ≠ i') (h2 : i ≠ j) (h3 : i ≠ j')
    (h4 : i' ≠ j) (h5 : i' ≠ j') (h6 : j ≠ j') :
    ∃ A : Finset (Fin (3 * k)), A.card = k ∧ i ∈ A ∧ i' ∈ A ∧ j ∉ A ∧ j' ∉ A := by
  obtain ⟨A, hA, hs, ht⟩ := exists_kset (k := k) {i, i'} {j, j'} (by simp [h2.symm, h3.symm, h4.symm, h5.symm])
    (by rw [card_pair h1]; omega) (by rw [card_pair h6]; omega)
  exact ⟨A, hA, hs (by simp), hs (by simp), disjoint_right.mp ht (by simp),
    disjoint_right.mp ht (by simp)⟩
end SCCThm8.Rig
