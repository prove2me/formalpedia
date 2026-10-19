-- Prove2me | solution 1 for QAlgorithms.Papers.RoadmapX01.separable_partialTransposeFirst_posSemidef
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T20:14:19.977652+00:00
-- url     : https://prove2.me/submissions/e2b1b906-bc94-4b5a-9c1f-a9c1418e1cf6

import Definitions.Def_QAlgorithms_Defs_BipartiteSeparability
import Mathlib.Analysis.Matrix.Order

open scoped ComplexOrder
open QAlgorithms.Entanglement

private lemma partialTranspose_sum {I J K : Type*} (s : Finset K)
    (f : K → Matrix (I × J) (I × J) ℂ) :
    partialTransposeFirst (∑ k ∈ s, f k) = ∑ k ∈ s, partialTransposeFirst (f k) := by
  ext p q
  simp [partialTransposeFirst, Matrix.sum_apply]

private lemma partialTranspose_weighted_tensor {I J : Type*} (r : ℂ)
    (A : Matrix I I ℂ) (B : Matrix J J ℂ) :
    partialTransposeFirst (r • Matrix.kronecker A B) =
      r • Matrix.kronecker A.transpose B := rfl

theorem solution
    {I J : Type*} [Fintype I] [Fintype J] [Nonempty I] [Nonempty J]
    [DecidableEq I] [DecidableEq J]
    (rho : Matrix (I × J) (I × J) ℂ)
    (hrho : QAlgorithms.IsDensityMatrix rho)
    (hsep : QAlgorithms.Entanglement.IsSeparableDensity rho) :
    (QAlgorithms.Entanglement.partialTransposeFirst rho).PosSemidef := by
  classical
  obtain ⟨q, w, A, B, hw, _, hAB, rfl⟩ := hsep
  rw [partialTranspose_sum]
  apply Matrix.posSemidef_sum
  intro k _
  rw [partialTranspose_weighted_tensor]
  apply Matrix.PosSemidef.smul
  · exact (hAB k).1.1.transpose.kronecker (hAB k).2.1
  · exact_mod_cast hw k
