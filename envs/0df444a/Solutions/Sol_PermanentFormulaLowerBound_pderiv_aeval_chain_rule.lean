-- Prove2me | solution 1 for PermanentFormulaLowerBound.pderiv_aeval_chain_rule
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:12.090475+00:00
-- url     : https://prove2.me/submissions/675d0dcf-bafe-4575-bd4b-f5b32be78cfb

import Mathlib
import Definitions.Def_Permanent
import Theorems.Thm_P2M_PermanentFormulaLowerBound_pderiv_bind__chain_rule_ab7619a8c457

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
    MvPolynomial.pderiv j (MvPolynomial.aeval g H) =
      ∑ i : ι,
        MvPolynomial.aeval g (MvPolynomial.pderiv i H) *
          MvPolynomial.pderiv j (g i) := by
  simpa only [MvPolynomial.aeval_eq_bind₁] using
    pderiv_bind₁_chain_rule g H j
end PermanentFormulaLowerBound
