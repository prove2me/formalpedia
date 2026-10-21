-- Prove2me | solution 1 for SpectralSparsify.Decomp.eq_13_vol_union
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T20:25:17.810463+00:00
-- url     : https://prove2.me/submissions/bc34077b-8f77-48e6-b512-c13b7653ee6b

import Mathlib
import Definitions.Def_SpectralSparsify_Decomp_vol

set_option autoImplicit false
open SpectralSparsify.Decomp

theorem solution {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (B S R : Finset V) (hSB : S ⊆ B) (hRB : R ⊆ B \ S)
    (hR : vol G R ≤ vol G (B \ S) / 2) (α : ℝ) (hα : vol G S = α * vol G B) :
    vol G (R ∪ S) ≤ (1 + α) / 2 * vol G B := by
  have hdisj : Disjoint R S := by
    rw [Finset.disjoint_left]
    intro a ha haS
    exact (Finset.mem_sdiff.mp (hRB ha)).2 haS
  have h1 : vol G (R ∪ S) = vol G R + vol G S := by
    unfold vol; rw [Finset.sum_union hdisj]
  have h2 : vol G (B \ S) = vol G B - vol G S := by
    unfold vol
    have := Finset.sum_sdiff (f := fun i => (G.degree i : ℝ)) hSB
    linarith
  rw [h1]
  rw [h2] at hR
  nlinarith [hα, hR]
