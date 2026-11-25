-- Prove2me | solution 1 for SpectralBounds.quadForm_eq_zero_of_indep
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T12:19:18.099119+00:00
-- url     : https://prove2.me/submissions/7e231be6-e32d-4879-a364-a839b6c4a06b

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
theorem _root_.solution (z : V → ℝ) (hz : ∀ u v, G.Adj u v → z u = 0 ∨ z v = 0) :
    z ⬝ᵥ (G.adjMatrix ℝ *ᵥ z) = 0 := by
  simp only [dotProduct, mulVec, mul_sum]
  refine sum_eq_zero fun v _ => sum_eq_zero fun u _ => ?_
  classical
  rw [adjMatrix_apply]
  split_ifs with h
  · rcases hz v u h with h | h <;> simp [h]
  · simp
end SpectralBounds
