-- Prove2me | solution 1 for SCCThm8.commute_psi
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:57:49.83315+00:00
-- url     : https://prove2.me/submissions/cbd451d1-d829-45f3-ad7e-b3b210547ad5

module
public import Definitions.Def_SCCThm8_PowerRigidity
public import Definitions.Def_SCCThm8_Counting
public import Definitions.Def_SCCThm8_Degeneration
public import Definitions.Def_SCCThm8_PowerDegeneration

set_option autoImplicit true
@[expose] public section
public section
open SCCThm8
open Finset
namespace SCCThm8
theorem _root_.solution {G : Type*} [Group G] {n : ℕ} {x : G} (g : Fin n → G)
    (h : ∀ i, Commute x (g i)) (e : Fin n → ℤ) : Commute x (psi g e) :=
  Commute.list_prod_right _ _ (fun y hy => by
    obtain ⟨i, -, rfl⟩ := List.mem_map.1 hy
    exact (h i).zpow_right _)
end SCCThm8
