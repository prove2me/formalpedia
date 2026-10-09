-- Prove2me | solution 1 for OCB2012.prob_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @Alien60
-- created : 2026-10-08T23:14:12.289864+00:00
-- url     : https://prove2.me/submissions/50d47dc5-eab0-43c1-a59f-5f7d8e20f879

import Mathlib
import Definitions.Def_PeresTerno_kraus_basics
import Definitions.Def_OCB2012_defs

open Matrix
open scoped Kronecker ComplexOrder

namespace OCB2012Sol

lemma trace_mul_nonneg_of_psd {n : Type*} [Fintype n] [DecidableEq n] {A B : Matrix n n ℂ}
    (hA : A.PosSemidef) (hB : B.PosSemidef) : 0 ≤ (A * B).trace := by
  open MatrixOrder in
  obtain ⟨C, rfl⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hB.nonneg
  rw [star_eq_conjTranspose, ← Matrix.mul_assoc, trace_mul_cycle]
  exact (hA.mul_mul_conjTranspose_same C).trace_nonneg

end OCB2012Sol

theorem solution {a1 a2 b1 b2 : Type*} [Fintype a1] [Fintype a2]
    [Fintype b1] [Fintype b2] [DecidableEq a1] [DecidableEq a2] [DecidableEq b1] [DecidableEq b2]
    (W : Matrix ((a1 × a2) × (b1 × b2)) ((a1 × a2) × (b1 × b2)) ℂ) (hW : W.PosSemidef)
    (MA : Matrix (a1 × a2) (a1 × a2) ℂ) (hA : MA.PosSemidef)
    (MB : Matrix (b1 × b2) (b1 × b2) ℂ) (hB : MB.PosSemidef) :
    0 ≤ OCB2012.prob W MA MB :=
  OCB2012Sol.trace_mul_nonneg_of_psd hW (hA.kronecker hB)
