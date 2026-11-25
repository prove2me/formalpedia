-- Prove2me | solution 1 for SCCThm8.Rig.d_two
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:55:12.793432+00:00
-- url     : https://prove2.me/submissions/90f7cbc1-36c2-4759-add7-d1a89e7e37af

module
public import Definitions.Def_SCCThm8_Defs
public import Definitions.Def_SCCThm8_Rigidity
public import Theorems.Thm_SCCThm8_Rig_mem_sw
public import Theorems.Thm_SCCThm8_Rig_card_sw
public import Theorems.Thm_SCCThm8_Rig_sw_sw_comm
public import Theorems.Thm_SCCThm8_Rig_ex4

set_option autoImplicit true
@[expose] public section
public section
open SCCThm8
open Finset
open SCCThm8.Rig
variable {n : ℕ}
variable {G : Type*} [Group G] {k : ℕ} {F : Finset (Fin (3 * k)) → G}
  {d : Fin (3 * k) → Fin (3 * k) → G}
variable (hk : 2 ≤ k)
  (hs : ∀ A : Finset (Fin (3 * k)), A.card = k → ∀ i j, i ∈ A → j ∉ A → F (sw A i j) = d i j * F A)
include hk hs
namespace SCCThm8.Rig
theorem _root_.solution {i i' j j' : Fin (3 * k)} (h1 : i ≠ i') (h2 : i ≠ j) (h3 : i ≠ j')
    (h4 : i' ≠ j) (h5 : i' ≠ j') (h6 : j ≠ j') :
    d i' j' * d i j = d i' j * d i j' := by
  obtain ⟨A, hA, hi, hi', hj, hj'⟩ := ex4 hk h1 h2 h3 h4 h5 h6
  have e1 := hs (sw A i j) (card_sw hA hi hj) i' j' (mem_sw.mpr (Or.inr ⟨h1.symm, hi'⟩))
    (by rw [mem_sw]; rintro (h | ⟨_, h⟩); exact h6 h.symm; exact hj' h)
  have e2 := hs (sw A i j') (card_sw hA hi hj') i' j (mem_sw.mpr (Or.inr ⟨h1.symm, hi'⟩))
    (by rw [mem_sw]; rintro (h | ⟨_, h⟩); exact h6 h; exact hj h)
  rw [sw_sw_comm h4 h5, e2, hs A hA i j hi hj, hs A hA i j' hi hj', ← mul_assoc,
    ← mul_assoc] at e1
  exact mul_right_cancel e1.symm
end SCCThm8.Rig
