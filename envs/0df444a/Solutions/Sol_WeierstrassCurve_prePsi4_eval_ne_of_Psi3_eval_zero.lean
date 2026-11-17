-- Prove2me | solution 1 for WeierstrassCurve.prePsi4_eval_ne_of_Psi3_eval_zero
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T19:04:19.71771+00:00
-- url     : https://prove2.me/submissions/5ad16269-79f8-4bd2-91a7-1b9c82962319

import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic
import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Degree
import Mathlib.NumberTheory.EllipticDivisibilitySequence
import Mathlib.Tactic
import Definitions.Def_KeystoneResultantCerts
import Definitions.Def_WardSomos

/-! Proofs of the lemmas stated in `Theorems.Thm_DivisionPolynomial_ResultantNonsingularity` and their helpers. -/

open Polynomial

open scoped Polynomial

open FLT.EDS

namespace WeierstrassCurve

noncomputable section

variable {k : Type*} [Field k]

/-- `b_relation` in distributed-C form. -/
private lemma bRelC (W : WeierstrassCurve k) :
    C W.b₂ * C W.b₆ - (C W.b₄) ^ 2 - C 4 * C W.b₈ = (0 : k[X]) := by
  have h0 : W.b₂ * W.b₆ - W.b₄ ^ 2 - 4 * W.b₈ = 0 := by
    have hb := W.b_relation; linear_combination -hb
  have := congrArg (fun z : k => (C z : k[X])) h0
  simpa [map_sub, map_mul, map_pow] using this

/-- Resultant/Bezout certificate `A·Ψ₃ + B·preΨ₄ = C(Δ⁴)` (CAS-extracted, uses `b_relation`). -/
private lemma bezout_Ψ₃_preΨ₄ (W : WeierstrassCurve k) :
    divisionBezoutThree W * W.Ψ₃ + divisionBezoutFour W * W.preΨ₄
      = C (W.Δ ^ 4) := by
  have hb := bRelC W
  linear_combination (norm :=
    (simp only [divisionBezoutThreeTerm0, divisionBezoutThreeTerm1, divisionBezoutThreeTerm2, divisionBezoutThreeTerm3, divisionBezoutThreeTerm4, divisionBezoutThreeTerm5, divisionBezoutThreeTerm6, divisionBezoutThreeTerm7, divisionBezoutThreeTerm8, divisionBezoutThree, divisionBezoutFourTerm0, divisionBezoutFourTerm1, divisionBezoutFourTerm2, divisionBezoutFourTerm3, divisionBezoutFourTerm4, divisionBezoutFourTerm5, divisionBezoutFour, WeierstrassCurve.Ψ₃, WeierstrassCurve.preΨ₄, WeierstrassCurve.Δ,
      map_neg, map_mul, map_add, map_sub, map_pow, map_ofNat, map_one,
      Polynomial.C_mul, Polynomial.C_add, Polynomial.C_sub, Polynomial.C_pow,
      Polynomial.C_neg, Polynomial.C_1]; ring1))
    (((30 : k[X]) * (C W.b₂) ^ 6 * (C W.b₄) * (C W.b₈) ^ 3
          + (3 : k[X]) * (C W.b₂) ^ 6 * (C W.b₆) ^ 2 * (C W.b₈) ^ 2
          - (477 : k[X]) * (C W.b₂) ^ 5 * (C W.b₄) ^ 2 * (C W.b₆) * (C W.b₈) ^ 2
          - (6 : k[X]) * (C W.b₂) ^ 5 * (C W.b₄) * (C W.b₆) ^ 3 * (C W.b₈)
          + (C W.b₂) ^ 5 * (C W.b₆) ^ 5
          - (114 : k[X]) * (C W.b₂) ^ 5 * (C W.b₆) * (C W.b₈) ^ 3
          + (384 : k[X]) * (C W.b₂) ^ 4 * (C W.b₄) ^ 4 * (C W.b₈) ^ 2
          + (2912 : k[X]) * (C W.b₂) ^ 4 * (C W.b₄) ^ 3 * (C W.b₆) ^ 2 * (C W.b₈)
          + (C W.b₂) ^ 4 * (C W.b₄) ^ 2 * (C W.b₆) ^ 4
          - (1242 : k[X]) * (C W.b₂) ^ 4 * (C W.b₄) ^ 2 * (C W.b₈) ^ 3
          + (2628 : k[X]) * (C W.b₂) ^ 4 * (C W.b₄) * (C W.b₆) ^ 2 * (C W.b₈) ^ 2
          - (56 : k[X]) * (C W.b₂) ^ 4 * (C W.b₆) ^ 4 * (C W.b₈)
          + (408 : k[X]) * (C W.b₂) ^ 4 * (C W.b₈) ^ 4
          - (4864 : k[X]) * (C W.b₂) ^ 3 * (C W.b₄) ^ 5 * (C W.b₆) * (C W.b₈)
          - (6560 : k[X]) * (C W.b₂) ^ 3 * (C W.b₄) ^ 4 * (C W.b₆) ^ 3
          + (10544 : k[X]) * (C W.b₂) ^ 3 * (C W.b₄) ^ 3 * (C W.b₆) * (C W.b₈) ^ 2
          - (25252 : k[X]) * (C W.b₂) ^ 3 * (C W.b₄) ^ 2 * (C W.b₆) ^ 3 * (C W.b₈)
          - (162 : k[X]) * (C W.b₂) ^ 3 * (C W.b₄) * (C W.b₆) ^ 5
          + (5184 : k[X]) * (C W.b₂) ^ 3 * (C W.b₄) * (C W.b₆) * (C W.b₈) ^ 3
          - (1667 : k[X]) * (C W.b₂) ^ 3 * (C W.b₆) ^ 3 * (C W.b₈) ^ 2
          + (2048 : k[X]) * (C W.b₂) ^ 2 * (C W.b₄) ^ 7 * (C W.b₈)
          + (16768 : k[X]) * (C W.b₂) ^ 2 * (C W.b₄) ^ 6 * (C W.b₆) ^ 2
          - (8030 : k[X]) * (C W.b₂) ^ 2 * (C W.b₄) ^ 5 * (C W.b₈) ^ 2
          - (5484 : k[X]) * (C W.b₂) ^ 2 * (C W.b₄) ^ 4 * (C W.b₆) ^ 2 * (C W.b₈)
          + (78624 : k[X]) * (C W.b₂) ^ 2 * (C W.b₄) ^ 3 * (C W.b₆) ^ 4
          + (21392 : k[X]) * (C W.b₂) ^ 2 * (C W.b₄) ^ 3 * (C W.b₈) ^ 3
          - (84711 : k[X]) * (C W.b₂) ^ 2 * (C W.b₄) ^ 2 * (C W.b₆) ^ 2 * (C W.b₈) ^ 2
          + (70956 : k[X]) * (C W.b₂) ^ 2 * (C W.b₄) * (C W.b₆) ^ 4 * (C W.b₈)
          - (23520 : k[X]) * (C W.b₂) ^ 2 * (C W.b₄) * (C W.b₈) ^ 4
          + (2187 : k[X]) * (C W.b₂) ^ 2 * (C W.b₆) ^ 6
          - (13276 : k[X]) * (C W.b₂) ^ 2 * (C W.b₆) ^ 2 * (C W.b₈) ^ 3
          - (14336 : k[X]) * (C W.b₂) * (C W.b₄) ^ 8 * (C W.b₆)
          + (40960 : k[X]) * (C W.b₂) * (C W.b₄) ^ 6 * (C W.b₆) * (C W.b₈)
          - (131328 : k[X]) * (C W.b₂) * (C W.b₄) ^ 5 * (C W.b₆) ^ 3
          - (72789 : k[X]) * (C W.b₂) * (C W.b₄) ^ 4 * (C W.b₆) * (C W.b₈) ^ 2
          + (284688 : k[X]) * (C W.b₂) * (C W.b₄) ^ 3 * (C W.b₆) ^ 3 * (C W.b₈)
          - (347733 : k[X]) * (C W.b₂) * (C W.b₄) ^ 2 * (C W.b₆) ^ 5
          + (3416 : k[X]) * (C W.b₂) * (C W.b₄) ^ 2 * (C W.b₆) * (C W.b₈) ^ 3
          + (139968 : k[X]) * (C W.b₂) * (C W.b₄) * (C W.b₆) ^ 3 * (C W.b₈) ^ 2
          - (83106 : k[X]) * (C W.b₂) * (C W.b₆) ^ 5 * (C W.b₈)
          + (121520 : k[X]) * (C W.b₂) * (C W.b₆) * (C W.b₈) ^ 4
          + (4096 : k[X]) * (C W.b₄) ^ 10
          - (16384 : k[X]) * (C W.b₄) ^ 8 * (C W.b₈)
          + (55296 : k[X]) * (C W.b₄) ^ 7 * (C W.b₆) ^ 2
          + (58975 : k[X]) * (C W.b₄) ^ 6 * (C W.b₈) ^ 2
          - (216810 : k[X]) * (C W.b₄) ^ 5 * (C W.b₆) ^ 2 * (C W.b₈)
          + (279936 : k[X]) * (C W.b₄) ^ 4 * (C W.b₆) ^ 4
          - (154252 : k[X]) * (C W.b₄) ^ 4 * (C W.b₈) ^ 3
          + (577584 : k[X]) * (C W.b₄) ^ 3 * (C W.b₆) ^ 2 * (C W.b₈) ^ 2
          - (905418 : k[X]) * (C W.b₄) ^ 2 * (C W.b₆) ^ 4 * (C W.b₈)
          + (235984 : k[X]) * (C W.b₄) ^ 2 * (C W.b₈) ^ 4
          + (590490 : k[X]) * (C W.b₄) * (C W.b₆) ^ 6
          - (635040 : k[X]) * (C W.b₄) * (C W.b₆) ^ 2 * (C W.b₈) ^ 3
          + (297432 : k[X]) * (C W.b₆) ^ 4 * (C W.b₈) ^ 2
          - (153664 : k[X]) * (C W.b₈) ^ 5)) * hb

/-- On an elliptic curve, `Ψ₃` and `preΨ₄` have no common root. -/
theorem _root_.solution (W : WeierstrassCurve k) [W.IsElliptic] {x : k}
    (hc3 : W.Ψ₃.eval x = 0) : (W.preΨ 4).eval x ≠ 0 := by
  rw [show W.preΨ 4 = W.preΨ₄ from by simpa using W.preΨ'_four ▸ rfl]
  intro hd4
  have hb := congrArg (fun p : k[X] => p.eval x) (bezout_Ψ₃_preΨ₄ W)
  simp only [eval_add, eval_mul, eval_C, eval_pow, eval_sub, eval_neg, eval_ofNat, eval_X,
    hc3, hd4, mul_zero, zero_mul, add_zero] at hb
  have hΔ4 : W.Δ ^ 4 = 0 := by linear_combination -hb
  exact (W.isUnit_Δ.ne_zero) (pow_eq_zero_iff (by norm_num) |>.mp hΔ4)

end

end WeierstrassCurve
