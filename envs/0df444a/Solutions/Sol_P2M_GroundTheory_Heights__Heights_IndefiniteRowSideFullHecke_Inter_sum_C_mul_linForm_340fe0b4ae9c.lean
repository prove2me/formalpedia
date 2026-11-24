-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_sum_C_mul_linForm_340fe0b4ae9c
-- status  : ACCEPTED   (prove)
-- author  : @sockpaprika
-- created : 2026-11-24T04:28:06.543812+00:00
-- url     : https://prove2.me/submissions/c4e8efab-51a2-4940-be9d-4a06bdbd68c2

import Mathlib
open MvPolynomial
variable {Φ : Type} [Field Φ]


theorem solution {τ ρ : Type} [Fintype τ] [Fintype ρ] (c : ρ → Φ) (ν : ρ → τ → Φ) :
    ∑ a, C (c a) * ∑ q, C (ν a q) * (X q : MvPolynomial τ Φ) = ∑ q, C (∑ a, c a * ν a q) * X q := by
  simp only [Finset.mul_sum, map_sum, Finset.sum_mul, map_mul, mul_assoc]
  exact Finset.sum_comm
