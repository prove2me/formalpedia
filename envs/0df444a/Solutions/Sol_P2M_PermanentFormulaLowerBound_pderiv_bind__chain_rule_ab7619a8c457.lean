-- Prove2me | solution 1 for P2M_PermanentFormulaLowerBound_pderiv_bind__chain_rule_ab7619a8c457
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:12.090475+00:00
-- url     : https://prove2.me/submissions/3fd5f61d-b4ce-4f4b-b074-5cb7bbc69072

import Mathlib
import Definitions.Def_Permanent

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentFormulaLowerBound
universe u v w
open scoped BigOperators Kronecker Matrix IntermediateField.algebraAdjoinAdjoin
variable {ι : Type u} {κ : Type v} {F : Type w}
namespace PermanentFormulaLowerBound
theorem _root_.solution [CommSemiring F] [Fintype ι]
    (g : ι → MvPolynomial κ F) (H : MvPolynomial ι F) (j : κ) :
    MvPolynomial.pderiv j (MvPolynomial.bind₁ g H) =
      ∑ i : ι,
        MvPolynomial.bind₁ g (MvPolynomial.pderiv i H) *
          MvPolynomial.pderiv j (g i) := by
  classical
  induction H using MvPolynomial.induction_on with
  | C c => simp
  | add p q hp hq => simp [Finset.sum_add_distrib, add_mul, hp, hq]
  | mul_X p i hp =>
      rw [map_mul, MvPolynomial.bind₁_X_right,
        MvPolynomial.pderiv_mul, hp]
      simp_rw [MvPolynomial.pderiv_mul, map_add, map_mul,
        MvPolynomial.bind₁_X_right, MvPolynomial.pderiv_X,
        Pi.single_apply, add_mul]
      rw [Finset.sum_add_distrib]
      simp [Finset.mul_sum, mul_assoc, mul_comm]
end PermanentFormulaLowerBound
