-- Prove2me | solution 1 for PelagicFF.quantum_amplitudes
-- status  : ACCEPTED   (prove)
-- author  : @dargilboa
-- created : 2026-11-15T09:03:30.361047+00:00
-- url     : https://prove2.me/submissions/ef253d5e-1f9d-4e51-9107-a185e2025881

import Mathlib
import Definitions.Def_PelagicFF_PFF
import Definitions.Def_PelagicFF_hadamardN

open OAI.Cotype

namespace PelagicFF

/-- The Walsh character in exponent form: `χ_y(x) = (−1)^{#{i | xᵢ ∧ yᵢ}}`. -/
private theorem character_eq_neg_one_pow {n : ℕ} (y x : Fin n → Bool) :
    character y x = (-1 : ℝ) ^ (Finset.univ.filter (fun i => x i && y i)).card := by
  rw [← Finset.prod_const, Finset.prod_filter, character]
  refine Finset.prod_congr rfl (fun i _ => ?_)
  cases y i <;> cases x i <;> simp [sign]

end PelagicFF

open PelagicFF in
theorem solution (n : ℕ) (f g : BoolFn n) (y : Fin n → Bool) :
    (hadamardN n).mulVec ((signDiag g).mulVec (phaseState f)) y =
      ((OAI.Cotype.fourier (fun x => sign (f x) * sign (g x)) y : ℝ) : ℂ) := by
  -- the normalisation: `2^{-n/2} · 2^{-n/2} = 2^{-n}`
  have hcc : ((Real.sqrt (2 ^ n))⁻¹ : ℂ) * ((Real.sqrt (2 ^ n))⁻¹ : ℂ) = ((2 : ℂ) ^ n)⁻¹ := by
    rw [← mul_inv, ← Complex.ofReal_mul, Real.mul_self_sqrt (by positivity)]
    push_cast
    rfl
  have hcard : (Fintype.card (Fin n → Bool) : ℝ) = 2 ^ n := by simp
  -- `U_g` acts entrywise
  have hdiag : (signDiag g).mulVec (phaseState f) =
      fun x => (sign (g x) : ℂ) * phaseState f x := by
    funext x
    simp [signDiag, Matrix.mulVec_diagonal]
  rw [hdiag]
  simp only [Matrix.mulVec, dotProduct, hadamardN, phaseState, OAI.Cotype.fourier, average,
    smul_eq_mul, hcard, character_eq_neg_one_pow]
  push_cast
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  linear_combination
    ((-1 : ℂ) ^ (Finset.univ.filter (fun i => x i && y i)).card * (sign (g x) : ℂ) *
      (sign (f x) : ℂ)) * hcc
