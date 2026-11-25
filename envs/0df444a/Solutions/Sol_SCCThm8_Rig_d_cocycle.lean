-- Prove2me | solution 1 for SCCThm8.Rig.d_cocycle
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:55:45.692029+00:00
-- url     : https://prove2.me/submissions/a78fee1b-436c-49c6-b430-232e84341dad

module
public import Definitions.Def_SCCThm8_Defs
public import Definitions.Def_SCCThm8_Rigidity
public import Theorems.Thm_SCCThm8_Rig_mem_sw
public import Theorems.Thm_SCCThm8_Rig_card_sw
public import Theorems.Thm_SCCThm8_Rig_sw_sw_trans
public import Theorems.Thm_SCCThm8_Rig_ex2

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
theorem _root_.solution {i j l : Fin (3 * k)} (hij : i ≠ j) (hil : i ≠ l) (hjl : j ≠ l) :
    d i l = d j l * d i j := by
  obtain ⟨A, hA, hi, hj, hl⟩ := ex2 hk hij hil hjl
  have h2 := hs (sw A i j) (card_sw hA hi hj) j l (mem_sw.mpr (Or.inl rfl))
    (by rw [mem_sw]; rintro (h | ⟨_, h⟩); exact hjl h.symm; exact hl h)
  rw [sw_sw_trans hj, hs A hA i l hi hl, hs A hA i j hi hj, ← mul_assoc] at h2
  exact mul_right_cancel h2
end SCCThm8.Rig
