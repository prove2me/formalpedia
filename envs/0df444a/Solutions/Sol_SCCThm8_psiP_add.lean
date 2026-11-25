-- Prove2me | solution 1 for SCCThm8.psiP_add
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:58:40.12196+00:00
-- url     : https://prove2.me/submissions/c4b3aa51-9da2-4d35-8d7a-13045595e24f

module
public import Definitions.Def_SCCThm8_PowerRigidity
public import Definitions.Def_SCCThm8_Counting
public import Definitions.Def_SCCThm8_Degeneration
public import Definitions.Def_SCCThm8_PowerDegeneration
public import Theorems.Thm_SCCThm8_commute_psi
public import Theorems.Thm_SCCThm8_list_prod_map_mul_of_commute
public import Theorems.Thm_SCCThm8_psi_add


set_option autoImplicit true
@[expose] public section
public section
open SCCThm8
open Finset
namespace SCCThm8
theorem _root_.solution {G : Type*} [Group G] {m n : ℕ} (g : Fin m → Fin n → G)
    (hc : ∀ j i j' i', Commute (g j i) (g j' i')) (e e' : Fin m → Fin n → ℤ) :
    psiP g (e + e') = psiP g e * psiP g e' := by
  unfold psiP
  have h : ∀ j, psi (g j) ((e + e') j) = psi (g j) (e j) * psi (g j) (e' j) := fun j =>
    psi_add (g j) (fun i i' => hc j i j i') (e j) (e' j)
  simp only [h]
  exact list_prod_map_mul_of_commute _ (fun j => psi (g j) (e j)) (fun j => psi (g j) (e' j))
    (fun j j' => commute_psi (g j') (fun i' => (commute_psi (g j) (fun i => hc j' i' j i)
      (e j)).symm) (e' j'))
end SCCThm8
