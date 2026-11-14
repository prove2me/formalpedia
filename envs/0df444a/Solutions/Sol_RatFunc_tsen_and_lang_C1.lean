-- Prove2me | solution 1 for RatFunc.tsen_and_lang_C1
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-14T01:56:39.419838+00:00
-- url     : https://prove2.me/submissions/191d7739-b002-4b37-8417-60d17667eb61

import Mathlib
import Definitions.Def_RPLib_S4_Tsen

set_option autoImplicit false

theorem solution
    (k : Type*) [Field k] [IsAlgClosed k] (L : Type*) [Field L] [Algebra (RatFunc k) L]
    [Algebra.IsAlgebraic (RatFunc k) L] :
    (∀ (n : ℕ) (f : MvPolynomial (Fin n) L), f.totalDegree < n → MvPolynomial.constantCoeff f = 0 →
        ∃ x : Fin n → L, x ≠ 0 ∧ MvPolynomial.eval x f = 0) ∧
      ∀ (K : Type*) (E : Type*) [Field K] [Field E] [Algebra K E] [Algebra.IsAlgebraic K E],
        (∀ (n : ℕ) (f : MvPolynomial (Fin n) K), f.totalDegree < n → MvPolynomial.constantCoeff f = 0 →
            ∃ x : Fin n → K, x ≠ 0 ∧ MvPolynomial.eval x f = 0) →
          (∀ (n : ℕ) (f : MvPolynomial (Fin n) E), f.totalDegree < n → MvPolynomial.constantCoeff f = 0 →
              ∃ x : Fin n → E, x ≠ 0 ∧ MvPolynomial.eval x f = 0) ∧
            (Module.Finite K E → Function.Surjective (Algebra.norm K : E → K)) := by
  refine ⟨RamanujanPetersson.Tsen.tsen k L, fun K E _ _ _ _ hK => ⟨?_, fun hfin => ?_⟩⟩
  · exact RamanujanPetersson.Tsen.IsC1.of_algebraic (K := K) (L := E) hK
  · have : FiniteDimensional K E := hfin
    exact RamanujanPetersson.Tsen.IsC1.norm_surjective (K := K) (L := E) hK
