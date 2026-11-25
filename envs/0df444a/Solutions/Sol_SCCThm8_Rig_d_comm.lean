-- Prove2me | solution 1 for SCCThm8.Rig.d_comm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:56:51.584479+00:00
-- url     : https://prove2.me/submissions/6cf557f3-b6e0-42f6-8112-3157693ee883

module
public import Definitions.Def_SCCThm8_Defs
public import Definitions.Def_SCCThm8_Rigidity
public import Theorems.Thm_SCCThm8_Rig_card_compl_fin
public import Theorems.Thm_SCCThm8_Rig_d_inv
public import Theorems.Thm_SCCThm8_Rig_d_cocycle
public import Theorems.Thm_SCCThm8_Rig_d_two

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
theorem _root_.solution {a b c : Fin (3 * k)} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    Commute (d a b) (d b c) := by
  obtain ⟨i, hi⟩ : ({a, b, c} : Finset (Fin (3 * k)))ᶜ.Nonempty := by
    rw [← card_pos, card_compl_fin]
    have := card_le_three (a := a) (b := b) (c := c)
    omega
  simp only [mem_compl, mem_insert, mem_singleton, not_or] at hi
  obtain ⟨hia, hib, hic⟩ := hi
  have h5 := d_two hk hs (i := i) (i' := a) (j := c) (j' := b) hia hic hib hac hab hbc.symm
  rw [d_cocycle hk hs hab hac hbc, d_cocycle hk hs hic hib hbc.symm] at h5
  have h3 := d_inv hk hs hbc
  have e : d a b = d b c * d a b * d c b := by
    have : d a b * d i c = (d b c * d a b * d c b) * d i c := by rw [h5]; group
    exact mul_right_cancel this
  show d a b * d b c = d b c * d a b
  nth_rewrite 1 [e]
  calc d b c * d a b * d c b * d b c = d b c * d a b * (d c b * d b c) := by group
    _ = d b c * d a b := by rw [h3, mul_one]
end SCCThm8.Rig
