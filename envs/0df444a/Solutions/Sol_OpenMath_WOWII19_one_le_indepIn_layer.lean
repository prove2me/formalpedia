-- Prove2me | solution 1 for OpenMath.WOWII19.one_le_indepIn_layer
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:39:04.049183+00:00
-- url     : https://prove2.me/submissions/dd33b446-adbb-42bd-b23b-412f2dc15602

module
public import Definitions.Def_OpenMath_Common
public import Mathlib.Algebra.Order.Floor.Ring
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import Definitions.Def_OpenMath_WOWII19
public import Theorems.Thm_OpenMath_WOWII19_le_indepIn
public import Theorems.Thm_OpenMath_dist_getVert_of_geodesic
public import Theorems.Thm_OpenMath_exists_dist_eq_ecc


set_option autoImplicit true
@[expose] public section
public section
set_option linter.unusedSectionVars false
open OpenMath OpenMath.WOWII19
open SimpleGraph Finset OpenMath
variable {α : Type*} [Fintype α] [DecidableEq α]
variable {G : SimpleGraph α}
namespace OpenMath.WOWII19
theorem _root_.solution (h : G.Connected) (v : α) {i : ℕ} (hi : i ≤ ecc G v) :
    1 ≤ indepIn G (layer G v i) := by
  obtain ⟨z, hz⟩ := exists_dist_eq_ecc h v
  obtain ⟨p, hp⟩ := h.exists_walk_length_eq_dist v z
  have hd := (dist_getVert_of_geodesic h p hp (i := i) (by omega)).1
  have := le_indepIn (G := G) (s := {p.getVert i}) (T := layer G v i)
    (by simp [layer, hd]) (by simp)
  simpa using this
end OpenMath.WOWII19
