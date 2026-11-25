-- Prove2me | solution 1 for SpectralBounds.iInf_eigenvalues_le_neg_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T12:30:39.885657+00:00
-- url     : https://prove2.me/submissions/4a2d4cf9-d755-4cc3-a940-70c6a10564d3

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
omit [Nonempty V]
namespace SpectralBounds
theorem _root_.solution (hE : G.edgeSet.Nonempty) :
    (⨅ i, hA.eigenvalues i) ≤ -1 := by
  obtain ⟨e, he⟩ := hE
  induction e using Sym2.ind with
  | _ u v =>
  rw [mem_edgeSet] at he
  have huv : u ≠ v := he.ne
  have h := iInf_le_quadForm hA (Pi.single u 1 - Pi.single v 1)
  simp [mulVec_sub, dotProduct_sub, sub_dotProduct, huv, huv.symm, he, he.symm] at h
  linarith
end SpectralBounds
