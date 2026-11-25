-- Prove2me | solution 1 for SCCThm8.Rig.d_inv
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:55:51.573729+00:00
-- url     : https://prove2.me/submissions/52b8ea88-66fd-4a44-ad69-38e33ae03d99

module
public import Definitions.Def_SCCThm8_Defs
public import Definitions.Def_SCCThm8_Rigidity
public import Theorems.Thm_SCCThm8_Rig_mem_sw
public import Theorems.Thm_SCCThm8_Rig_card_sw
public import Theorems.Thm_SCCThm8_Rig_sw_sw_back
public import Theorems.Thm_SCCThm8_Rig_ex1

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
theorem _root_.solution {i j : Fin (3 * k)} (hij : i ≠ j) : d j i * d i j = 1 := by
  obtain ⟨A, hA, hi, hj⟩ := ex1 hk hij
  have h2 := hs (sw A i j) (card_sw hA hi hj) j i (mem_sw.mpr (Or.inl rfl))
    (by rw [mem_sw]; rintro (h | ⟨h, _⟩); exact hij h; exact h rfl)
  rw [sw_sw_back hi hj, hs A hA i j hi hj] at h2
  calc d j i * d i j = (d j i * (d i j * F A)) * (F A)⁻¹ := by group
    _ = 1 := by rw [← h2]; group
end SCCThm8.Rig
