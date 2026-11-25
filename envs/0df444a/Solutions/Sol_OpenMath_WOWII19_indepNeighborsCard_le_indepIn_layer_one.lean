-- Prove2me | solution 1 for OpenMath.WOWII19.indepNeighborsCard_le_indepIn_layer_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:39:06.142027+00:00
-- url     : https://prove2.me/submissions/86e98a7c-409e-4148-8ee8-a6237f0605f3

module
public import Definitions.Def_OpenMath_Common
public import Mathlib.Algebra.Order.Floor.Ring
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import Definitions.Def_OpenMath_WOWII19
public import Theorems.Thm_OpenMath_WOWII19_le_indepIn
public import Theorems.Thm_OpenMath_exists_indep_neighbors


set_option autoImplicit true
@[expose] public section
public section
set_option linter.unusedSectionVars false
open OpenMath OpenMath.WOWII19
open SimpleGraph Finset OpenMath
variable {α : Type*} [Fintype α] [DecidableEq α]
variable {G : SimpleGraph α}
namespace OpenMath.WOWII19
theorem _root_.solution (v : α) :
    indepNeighborsCard G v ≤ indepIn G (layer G v 1) := by
  obtain ⟨S, hSadj, hSind, hScard⟩ := exists_indep_neighbors G v
  rw [← hScard]
  apply le_indepIn _ hSind
  intro x hx
  simp [layer, dist_eq_one_iff_adj, hSadj x hx]
end OpenMath.WOWII19
