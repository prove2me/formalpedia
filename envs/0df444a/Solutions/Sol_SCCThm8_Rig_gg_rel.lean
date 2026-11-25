-- Prove2me | solution 1 for SCCThm8.Rig.gg_rel
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:56:49.490807+00:00
-- url     : https://prove2.me/submissions/83668be6-6b3d-4e91-840d-19227d9a5565

module
public import Definitions.Def_SCCThm8_Defs
public import Definitions.Def_SCCThm8_Rigidity
public import Theorems.Thm_SCCThm8_Rig_d_inv
public import Theorems.Thm_SCCThm8_Rig_d_cocycle

set_option autoImplicit true
@[expose] public section
public section
open SCCThm8
open Finset
open SCCThm8.Rig
variable {n : ℕ}
variable {G : Type*} [Group G] {k : ℕ}
variable {F : Finset (Fin (3 * k)) → G} {d : Fin (3 * k) → Fin (3 * k) → G} (hk : 2 ≤ k)
  (hs : ∀ A : Finset (Fin (3 * k)), A.card = k → ∀ i j, i ∈ A → j ∉ A → F (sw A i j) = d i j * F A)
include hk hs
namespace SCCThm8.Rig
theorem _root_.solution (o : Fin (3 * k)) {i j : Fin (3 * k)} (hij : i ≠ j) :
    d i j = gg d o j * (gg d o i)⁻¹ := by
  by_cases hi : i = o
  · subst hi; simp [gg, Ne.symm hij]
  by_cases hj : j = o
  · subst hj; simp only [gg, hi, ite_true, ite_false, one_mul]
    exact eq_inv_of_mul_eq_one_right (d_inv hk hs hij)
  simp only [gg, hi, hj, ite_false]
  rw [d_cocycle hk hs (Ne.symm hi) (Ne.symm hj) hij]
  group
end SCCThm8.Rig
