-- Prove2me | solution 1 for SCCThm8.PRig.prodP_update
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:56:44.931614+00:00
-- url     : https://prove2.me/submissions/c7cf3d30-8e38-4fa2-a790-db1b294d93eb

module
public import Definitions.Def_SCCThm8_Defs
public import Definitions.Def_SCCThm8_Rigidity
public import Definitions.Def_SCCThm8_PowerRigidity

set_option autoImplicit true
@[expose] public section
public section
open SCCThm8
open Finset
open SCCThm8.PRig
open Rig Function
namespace SCCThm8.PRig
theorem _root_.solution {n m : ℕ} {H : Type*} [CommGroup H] (g' : Fin m → Fin n → H)
    (A : Fin m → Finset (Fin n)) (j : Fin m) (Y : Finset (Fin n)) :
    ∏ j', ∏ x ∈ update A j Y j', g' j' x =
      (∏ x ∈ Y, g' j x) * (∏ x ∈ A j, g' j x)⁻¹ * ∏ j', ∏ x ∈ A j', g' j' x := by
  rw [← mul_prod_erase univ (fun j' => ∏ x ∈ update A j Y j', g' j' x) (mem_univ j),
    ← mul_prod_erase univ (fun j' => ∏ x ∈ A j', g' j' x) (mem_univ j)]
  have : ∏ j' ∈ univ.erase j, ∏ x ∈ update A j Y j', g' j' x =
      ∏ j' ∈ univ.erase j, ∏ x ∈ A j', g' j' x := by
    apply prod_congr rfl
    intro j' hj'
    rw [update_of_ne (ne_of_mem_erase hj')]
  simp only [update_self]
  rw [this]
  group
end SCCThm8.PRig
