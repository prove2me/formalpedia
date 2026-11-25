-- Prove2me | solution 1 for SpectralBounds.exists_coloring_of_low_degree
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T12:23:41.988975+00:00
-- url     : https://prove2.me/submissions/4efabbbd-13d0-4a5c-809d-e2270ab30eb6

module
public import Mathlib
public import Definitions.Def_SpectralLib_SpectralBounds

set_option autoImplicit true
@[expose] public section
public section
open Finset SimpleGraph
open SpectralBounds
variable {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V)
  [DecidableRel G.Adj] (hA : (G.adjMatrix ℝ).IsHermitian)
open Matrix
omit [Nonempty V]
namespace SpectralBounds
theorem _root_.solution (m : ℕ)
    (h : ∀ S : Finset V, S.Nonempty → ∃ v ∈ S, #(G.neighborFinset v ∩ S) ≤ m)
    (S : Finset V) : ∃ f : V → Fin (m + 1), ∀ u ∈ S, ∀ w ∈ S, G.Adj u w → f u ≠ f w := by
  induction S using Finset.strongInduction with
  | H S ih =>
  rcases S.eq_empty_or_nonempty with rfl | hS
  · exact ⟨fun _ => 0, by simp⟩
  obtain ⟨v, hv, hdeg⟩ := h S hS
  obtain ⟨f, hf⟩ := ih (S.erase v) (erase_ssubset hv)
  have hcard : #(({u ∈ G.neighborFinset v | u ∈ S}).image f) < #(univ : Finset (Fin (m + 1))) :=
    by
      rw [card_univ, Fintype.card_fin]
      exact lt_of_le_of_lt (card_image_le.trans hdeg) (Nat.lt_succ_self m)
  obtain ⟨c, -, hc⟩ := exists_mem_notMem_of_card_lt_card hcard
  refine ⟨Function.update f v c, fun u hu w hw huw => ?_⟩
  have key : ∀ y ∈ S, G.Adj v y → c ≠ f y := by
    intro y hy hvy hcy
    exact hc (mem_image.2 ⟨y, by simp [hy, hvy], hcy.symm⟩)
  by_cases huv : u = v
  · subst huv
    have hwv : w ≠ u := huw.ne.symm
    simpa [hwv] using key w hw huw
  by_cases hwv : w = v
  · subst hwv
    simpa [huv] using (key u hu huw.symm).symm
  simpa [huv, hwv] using hf u (mem_erase.2 ⟨huv, hu⟩) w (mem_erase.2 ⟨hwv, hw⟩) huw
end SpectralBounds
