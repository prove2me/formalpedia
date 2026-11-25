-- Prove2me | solution 1 for SCCThm8.psi_add
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:52:15.979305+00:00
-- url     : https://prove2.me/submissions/caef8985-5a2f-4b7c-91a5-bbf7ff4a1c2d

module
public import Definitions.Def_SCCThm8_Defs
public import Definitions.Def_SCCThm8_Counting
public import Theorems.Thm_SCCThm8_list_prod_map_mul_of_commute

set_option autoImplicit true
@[expose] public section
public section
open SCCThm8
open Finset
namespace SCCThm8
theorem _root_.solution {G : Type*} [Group G] {n : ℕ} (g : Fin n → G)
    (hc : ∀ i j, Commute (g i) (g j)) (e e' : Fin n → ℤ) :
    psi g (e + e') = psi g e * psi g e' := by
  unfold psi
  simp only [Pi.add_apply, zpow_add]
  exact list_prod_map_mul_of_commute _ (fun i => g i ^ e i) (fun i => g i ^ e' i)
    (fun i j => (hc i j).zpow_zpow _ _)
end SCCThm8
