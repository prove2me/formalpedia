-- Prove2me | solution 1 for WildeQIT.Packing.lemma_A_0_1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T14:53:39.456706+00:00
-- url     : https://prove2.me/submissions/08ba4449-8109-4064-83dc-0af2b18ac778

import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.PosDef

open Matrix
open scoped ComplexOrder

theorem solution {n : Type} [Fintype n] (M N : Matrix n n ℂ) (hM : M.PosSemidef) (hN : N.PosSemidef) : (M + N).PosSemidef ∧ (M * N * M).PosSemidef ∧ (N * M * N).PosSemidef := by
  refine ⟨hM.add hN, ?_, ?_⟩
  · have h := hN.conjTranspose_mul_mul_same M
    rwa [hM.isHermitian.eq] at h
  · have h := hM.conjTranspose_mul_mul_same N
    rwa [hN.isHermitian.eq] at h
