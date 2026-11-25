-- Prove2me | solution 1 for SCCThm8.Rig.gg_comm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:58:16.479635+00:00
-- url     : https://prove2.me/submissions/80342281-270a-4954-b6d0-82d405645a59

module
public import Definitions.Def_SCCThm8_Defs
public import Definitions.Def_SCCThm8_Rigidity
public import Theorems.Thm_SCCThm8_Rig_d_comm
public import Theorems.Thm_SCCThm8_Rig_gg_rel

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
theorem _root_.solution (o i j : Fin (3 * k)) : Commute (gg d o i) (gg d o j) := by
  by_cases hij : i = j
  · subst hij; exact Commute.refl _
  by_cases hi : i = o
  · subst hi; simp only [gg, ite_true]; exact Commute.one_left _
  by_cases hj : j = o
  · subst hj; simp only [gg, ite_true]; exact Commute.one_right _
  have e : gg d o j = d i j * gg d o i := by rw [gg_rel hk hs o hij]; group
  rw [e]
  refine Commute.mul_right ?_ (Commute.refl _)
  simp only [gg, hi, ite_false]
  exact d_comm hk hs (Ne.symm hi) (Ne.symm hj) hij
end SCCThm8.Rig
