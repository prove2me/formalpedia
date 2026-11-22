-- Prove2me | solution 1 for PebblingLean.GraphIso.map_move
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T05:52:47.169513+00:00
-- url     : https://prove2.me/submissions/25b9f221-bf7f-4176-a92f-df8be2dee776

module
public import Definitions.Def_LeanPool_PebblingLean_Basic
public import Mathlib.Tactic.Bound.Init
public import Definitions.Def_LeanPool_PebblingLean_GraphIso
public import Theorems.Thm_PebblingLean_Pebbling_moveDistribution_apply_from
public import Theorems.Thm_PebblingLean_Pebbling_moveDistribution_apply_of_ne
public import Theorems.Thm_PebblingLean_Pebbling_moveDistribution_apply_to
public import Theorems.Thm_PebblingLean_Pebbling_size_zero
attribute [local simp] PebblingLean.Pebbling.moveDistribution_apply_from
attribute [local simp] PebblingLean.Pebbling.moveDistribution_apply_of_ne
attribute [local simp] PebblingLean.Pebbling.moveDistribution_apply_to
attribute [local simp] PebblingLean.Pebbling.size_zero



set_option autoImplicit true
@[expose] public section
public section
open PebblingLean
universe u v
open PebblingLean.GraphIso
variable {V : Type u} {W : Type v} {G : Graph V} {H : Graph W}
namespace PebblingLean.GraphIso
theorem _root_.solution [DecidableEq V] [DecidableEq W]
    (iso : GraphIso G H) {D E : Pebbling V}
    (hmove : Pebbling.Move G D E) :
    Pebbling.Move H (iso.mapDistribution D) (iso.mapDistribution E) := by
  rcases hmove with ⟨u, v, huv, hD, rfl⟩
  have huv_ne : u ≠ v := by
    intro h
    subst v
    exact (G.loopless u) huv
  have hvu_ne : v ≠ u := fun h => huv_ne h.symm
  have heuv_ne : iso.toEquiv u ≠ iso.toEquiv v := fun h => huv_ne (iso.toEquiv.injective h)
  have hevu_ne : iso.toEquiv v ≠ iso.toEquiv u := fun h => heuv_ne h.symm
  refine ⟨iso.toEquiv u, iso.toEquiv v, (iso.adj_iff.mp huv), ?_, ?_⟩
  · simpa [mapDistribution] using hD
  · funext w
    by_cases hwu : w = iso.toEquiv u
    · simp_all
    · by_cases hwv : w = iso.toEquiv v
      · simp_all
      · have hsymm_u : iso.toEquiv.symm w ≠ u := by
          intro h
          exact hwu (by
            calc
              w = iso.toEquiv (iso.toEquiv.symm w) := by simp
              _ = iso.toEquiv u := by rw [h])
        have hsymm_v : iso.toEquiv.symm w ≠ v := by
          intro h
          exact hwv (by
            calc
              w = iso.toEquiv (iso.toEquiv.symm w) := by simp
              _ = iso.toEquiv v := by rw [h])
        simp [mapDistribution, Pebbling.moveDistribution, hwu, hwv, hsymm_u, hsymm_v]
end PebblingLean.GraphIso
