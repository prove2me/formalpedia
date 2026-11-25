-- Prove2me | solution 1 for SpectralBounds.quadForm_le_iSup
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T12:24:48.780203+00:00
-- url     : https://prove2.me/submissions/807581bf-e075-4f92-b4c0-618e46d25663

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
    x ⬝ᵥ (M *ᵥ x) ≤ (⨆ i, hM.eigenvalues i) * (x ⬝ᵥ x) := by
  obtain ⟨y, h1, h2⟩ := exists_quadForm_eq hM x
  rw [h1, h2, mul_sum]
  gcongr with i
  exact le_ciSup (Set.finite_range _).bddAbove i
end SpectralBounds
