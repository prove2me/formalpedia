-- Prove2me | solution 1 for SpectralBounds.exists_low_degree
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T12:30:27.635152+00:00
-- url     : https://prove2.me/submissions/0d3fdebe-ed20-4a4b-8b67-42b82e323361

module
public import Mathlib
public import Definitions.Def_SpectralLib_SpectralBounds
public import Theorems.Thm_SpectralBounds_quadForm_le_iSup

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
theorem _root_.solution (S : Finset V) (hS : S.Nonempty) :
    ∃ v ∈ S, (#(G.neighborFinset v ∩ S) : ℝ) ≤ ⨆ i, hA.eigenvalues i := by
  set x : V → ℝ := fun w => if w ∈ S then 1 else 0
  have h := quadForm_le_iSup hA x
  have hxx : x ⬝ᵥ x = #S := by simp [x, dotProduct]
  have hq : x ⬝ᵥ (G.adjMatrix ℝ *ᵥ x) = ∑ v ∈ S, (#(G.neighborFinset v ∩ S) : ℝ) := by
    simp [x, dotProduct]
  rw [hxx, hq] at h
  refine exists_le_of_sum_le hS ?_
  simpa [mul_comm] using h
end SpectralBounds
