-- Prove2me | solution 1 for SpectralBounds.iInf_le_quadForm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T12:24:47.682653+00:00
-- url     : https://prove2.me/submissions/3e06a046-8acb-4469-a31d-4ee42f03be68

module
public import Mathlib
public import Definitions.Def_SpectralLib_SpectralBounds
public import Theorems.Thm_SpectralBounds_exists_quadForm_eq

set_option autoImplicit true
@[expose] public section
public section
open Finset SimpleGraph
open SpectralBounds
variable {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V)
  [DecidableRel G.Adj] (hA : (G.adjMatrix ℝ).IsHermitian)
variable {W : Type*} [Fintype W] [DecidableEq W] {M : Matrix W W ℝ}
open Matrix
namespace SpectralBounds
theorem _root_.solution (hM : M.IsHermitian) (x : W → ℝ) :
    (⨅ i, hM.eigenvalues i) * (x ⬝ᵥ x) ≤ x ⬝ᵥ (M *ᵥ x) := by
  obtain ⟨y, h1, h2⟩ := exists_quadForm_eq hM x
  rw [h1, h2, mul_sum]
  gcongr with i
  exact ciInf_le (Set.finite_range _).bddBelow i
end SpectralBounds
