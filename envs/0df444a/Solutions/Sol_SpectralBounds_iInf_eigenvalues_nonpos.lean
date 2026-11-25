-- Prove2me | solution 1 for SpectralBounds.iInf_eigenvalues_nonpos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T12:30:38.233802+00:00
-- url     : https://prove2.me/submissions/5a65969c-06e2-4601-a6f0-256dea20ef47

module
public import Mathlib
public import Definitions.Def_SpectralLib_SpectralBounds
public import Theorems.Thm_SpectralBounds_iInf_le_quadForm

set_option autoImplicit true
@[expose] public section
public section
open Finset SimpleGraph
open SpectralBounds
variable {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V)
  [DecidableRel G.Adj] (hA : (G.adjMatrix ℝ).IsHermitian)
open Matrix
namespace SpectralBounds
theorem _root_.solution : (⨅ i, hA.eigenvalues i) ≤ 0 := by
  obtain ⟨v⟩ := ‹Nonempty V›
  have h := iInf_le_quadForm hA (Pi.single v 1)
  simpa using h
end SpectralBounds
