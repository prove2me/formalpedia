-- Prove2me | solution 1 for SpectralBounds.average_degree_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T12:30:25.878193+00:00
-- url     : https://prove2.me/submissions/d439bfc9-8b4d-404b-977b-1ef34b8c9bb5

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
namespace SpectralBounds
theorem _root_.solution :
    2 * (#G.edgeFinset : ℝ) / Fintype.card V ≤ ⨆ i, hA.eigenvalues i := by
  have h := quadForm_le_iSup hA (fun _ : V => (1 : ℝ))
  have hxx : (fun _ : V => (1 : ℝ)) ⬝ᵥ (fun _ : V => (1 : ℝ)) = Fintype.card V := by
    simp [dotProduct]
  have hq : (fun _ : V => (1 : ℝ)) ⬝ᵥ (G.adjMatrix ℝ *ᵥ fun _ : V => (1 : ℝ)) =
      2 * (#G.edgeFinset : ℝ) := by
    simp only [dotProduct, adjMatrix_mulVec_apply, sum_const, one_mul,
      card_neighborFinset_eq_degree, nsmul_eq_mul, mul_one]
    exact_mod_cast G.sum_degrees_eq_twice_card_edges
  rw [hxx, hq] at h
  have hn : (0 : ℝ) < Fintype.card V := by exact_mod_cast Fintype.card_pos
  rwa [div_le_iff₀ hn]
end SpectralBounds
