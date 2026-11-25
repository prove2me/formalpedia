-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_SchurSignCoefficient_coeff_aeval_diagonal_0e15d31de021
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T04:53:03.3648+00:00
-- url     : https://prove2.me/submissions/d90c1f1d-2e7c-49c2-a999-efbae4f2c27f

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_StatementsTop
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PSchurSignCoefficient

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open GroundTheory.Heights₂.Heights.RestTerms
open MvPolynomial Finset
noncomputable section
namespace GroundTheory.Heights₂.Heights.RestTerms
namespace SchurSignCoefficient
theorem _root_.solution {N : ℕ} (c : Fin N → ℚ)
    (P : MvPolynomial (Fin N) ℚ) (e : Fin N →₀ ℕ) :
    coeff e (aeval (fun i : Fin N => C (c i) * X i) P) = (∏ i, c i ^ e i) * coeff e P := by
  induction P using MvPolynomial.induction_on' with
  | monomial u a =>
    have hmon : aeval (fun i : Fin N => C (c i) * X i) (monomial u a) =
        monomial u (a * ∏ i, c i ^ u i) := by
      rw [aeval_monomial, monomial_eq, Finsupp.prod_fintype _ _ (by simp),
        Finsupp.prod_fintype _ _ (by simp)]
      simp only [mul_pow, Finset.prod_mul_distrib, algebraMap_eq, C_mul, ← C_pow, ← map_prod]
      ring
    rw [hmon, coeff_monomial, coeff_monomial]
    split_ifs with hue
    · subst hue; ring
    · simp
  | add p q hp hq => rw [map_add, coeff_add, coeff_add, hp, hq, mul_add]
end SchurSignCoefficient
end GroundTheory.Heights₂.Heights.RestTerms
