-- Prove2me | solution 1 for SpectralBounds.dotProduct_adjMatrix_mulVec_comm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T12:23:34.562459+00:00
-- url     : https://prove2.me/submissions/ec00d219-fa21-4bc1-810c-1d7b1ff635df

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
omit [DecidableEq V] [Nonempty V]
namespace SpectralBounds
theorem _root_.solution (x z : V → ℝ) :
    x ⬝ᵥ (G.adjMatrix ℝ *ᵥ z) = z ⬝ᵥ (G.adjMatrix ℝ *ᵥ x) := by
  rw [dotProduct_mulVec, ← mulVec_transpose, transpose_adjMatrix, dotProduct_comm]
end SpectralBounds
