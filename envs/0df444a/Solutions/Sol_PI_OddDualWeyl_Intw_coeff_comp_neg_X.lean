-- Prove2me | solution 1 for PI.OddDualWeyl.Intw.coeff_comp_neg_X
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:05:02.891218+00:00
-- url     : https://prove2.me/submissions/32579b2b-ca2a-412d-9a68-2bce8fd1e992

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_OddDualWeylJacobian_JacRev
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_OddDualWeylJacobian_TransvectionMulApply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial Matrix
noncomputable section
open PI PI.OddDualWeyl
open PI.OddDualWeyl.Intw
variable {A : Type*} [CommRing A] {n : ℕ}
namespace PI.OddDualWeyl.Intw
theorem _root_.solution (p : Polynomial A) (m : ℕ) :
    (p.comp (-Polynomial.X)).coeff m = (-1) ^ m * p.coeff m := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => rw [Polynomial.add_comp, Polynomial.coeff_add, hp, hq, Polynomial.coeff_add, mul_add]
  | monomial e a =>
    have hX : (-Polynomial.X : Polynomial A) ^ e = Polynomial.C ((-1) ^ e) * Polynomial.X ^ e := by
      rw [neg_pow]
      simp
    rw [← Polynomial.C_mul_X_pow_eq_monomial, Polynomial.mul_comp, Polynomial.C_comp,
      Polynomial.X_pow_comp, hX, ← mul_assoc, ← Polynomial.C_mul, Polynomial.coeff_C_mul_X_pow,
      Polynomial.coeff_C_mul_X_pow]
    split_ifs with hm
    · subst hm
      ring
    · simp
end PI.OddDualWeyl.Intw
