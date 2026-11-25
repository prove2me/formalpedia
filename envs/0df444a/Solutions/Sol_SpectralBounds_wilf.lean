-- Prove2me | solution 1 for SpectralBounds.wilf
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T12:36:45.049541+00:00
-- url     : https://prove2.me/submissions/87268036-1ce0-4506-89e9-fbf48e013f08

module
public import Mathlib
public import Definitions.Def_SpectralLib_SpectralBounds
public import Theorems.Thm_SpectralBounds_exists_low_degree
public import Theorems.Thm_SpectralBounds_exists_coloring_of_low_degree

set_option autoImplicit true
@[expose] public section
public section
open Finset SimpleGraph
open SpectralBounds
variable {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V)
  [DecidableRel G.Adj] (hA : (G.adjMatrix ℝ).IsHermitian)
open Matrix
namespace SpectralBounds
theorem _root_.solution : G.Colorable (⌊⨆ i, hA.eigenvalues i⌋₊ + 1) := by
  obtain ⟨f, hf⟩ := exists_coloring_of_low_degree G ⌊⨆ i, hA.eigenvalues i⌋₊
    (fun S hS => by
      obtain ⟨v, hv, hdeg⟩ := exists_low_degree G hA S hS
      exact ⟨v, hv, Nat.le_floor hdeg⟩) univ
  exact ⟨Coloring.mk f fun {u w} huw => hf u (mem_univ u) w (mem_univ w) huw⟩
end SpectralBounds
