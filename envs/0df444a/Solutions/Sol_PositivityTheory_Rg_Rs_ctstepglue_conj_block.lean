-- Prove2me | solution 1 for PositivityTheory.Rg.Rs.ctstepglue.conj_block
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T05:21:50.267526+00:00
-- url     : https://prove2.me/submissions/b1da8e2e-472e-4703-8a32-3214527d109e

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ResidualSpectrum_ExponentialNegativity_ConstantTermSteps_ConjBlock

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Rs PositivityTheory.Rg.Rs.ctstepglue
open Matrix
namespace PositivityTheory.Rg.Rs.ctstepglue
theorem _root_.solution {R : Type*} [CommRing R] {n : ℕ} (r : ℕ) (b : GL (Fin n) R)
    (hb : (b : Matrix (Fin n) (Fin n) R).BlockTriangular id) (d : Fin n → Rˣ)
    (hd : ∀ i j : Fin n, ((i : ℕ) < r ↔ (j : ℕ) < r) → d i = d j) :
    ∃ Y : Matrix (Fin n) (Fin n) R, (∀ i j : Fin n, ¬((i : ℕ) < r ∧ r ≤ (j : ℕ)) → Y i j = 0) ∧
      (b : Matrix (Fin n) (Fin n) R) * diagonal (fun i => (d i : R)) =
        (1 + Y) * (diagonal (fun i => (d i : R)) * (b : Matrix (Fin n) (Fin n) R)) := by
  classical
  set D : Matrix (Fin n) (Fin n) R := diagonal fun i => (d i : R) with hD
  set Di : Matrix (Fin n) (Fin n) R := diagonal fun i => (((d i)⁻¹ : Rˣ) : R) with hDi'
  set B : Matrix (Fin n) (Fin n) R := (b : Matrix (Fin n) (Fin n) R) with hB
  set Bi : Matrix (Fin n) (Fin n) R := ((b⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) with hBi'
  have hDi : Di * D = 1 := by
    rw [hD, hDi', diagonal_mul_diagonal]
    convert diagonal_one (n := Fin n) (α := R) using 2
    simp
  have hBi : Bi * B = 1 := by
    rw [hBi', hB, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hbi : Bi.BlockTriangular id := by
    rw [hBi', Matrix.coe_units_inv]
    exact Matrix.blockTriangular_inv_of_blockTriangular hb
  set Z : Matrix (Fin n) (Fin n) R := B * D - D * B with hZdef
  have hZ : ∀ i j : Fin n, ¬((i : ℕ) < r ∧ r ≤ (j : ℕ)) → Z i j = 0 := by
    intro i j h
    rw [hZdef, Matrix.sub_apply, hD, mul_diagonal, diagonal_mul]
    by_cases hij : j < i
    · rw [hb hij]; ring
    · have hij' : (i : ℕ) ≤ j := by rw [Fin.lt_def] at hij; omega
      rw [hd i j ⟨fun hi => by by_contra hj; exact h ⟨hi, by omega⟩, fun hj => by omega⟩]
      ring
  refine ⟨Z * Bi * Di, ?_, ?_⟩
  · intro i j h
    have hZB : (Z * Bi) i j = 0 := by
      rw [mul_apply]
      refine Finset.sum_eq_zero fun k _ => ?_
      by_cases hk : (i : ℕ) < r ∧ r ≤ (k : ℕ)
      · have hj : (j : ℕ) < r := by
          by_contra hj; exact h ⟨hk.1, by omega⟩
        rw [hbi (show j < k by rw [Fin.lt_def]; omega), mul_zero]
      · rw [hZ i k hk, zero_mul]
    rw [hDi', mul_diagonal, hZB, zero_mul]
  · have e1 : B * D = D * B + Z := by rw [hZdef]; abel
    rw [e1, add_mul, one_mul, Matrix.mul_assoc (Z * Bi) Di, ← Matrix.mul_assoc Di D B, hDi,
      Matrix.one_mul, Matrix.mul_assoc Z Bi B, hBi, Matrix.mul_one]
end PositivityTheory.Rg.Rs.ctstepglue
