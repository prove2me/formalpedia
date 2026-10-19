-- Prove2me | solution 1 for PermanentFormulaLowerBound.totalDegree_pderiv_lt_of_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:12.090475+00:00
-- url     : https://prove2.me/submissions/5a9f807a-8641-4562-8f17-fede7d3b4bc8

import Mathlib
import Definitions.Def_Permanent
import Theorems.Thm_PermanentFormulaLowerBound_totalDegree_succ_le_of_mem_pderiv_support

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentFormulaLowerBound
universe u v w
open scoped BigOperators Kronecker Matrix IntermediateField.algebraAdjoinAdjoin
variable {ι : Type u} {κ : Type v} {F : Type w}
namespace PermanentFormulaLowerBound
theorem _root_.solution [CommSemiring F]
    (p : MvPolynomial ι F) (i : ι)
    (hp : MvPolynomial.pderiv i p ≠ 0) :
    (MvPolynomial.pderiv i p).totalDegree < p.totalDegree := by
  classical
  obtain ⟨m, hm⟩ := MvPolynomial.support_nonempty.mpr hp
  have hpositive : 0 < p.totalDegree :=
    lt_of_lt_of_le (Nat.zero_lt_succ _)
      (totalDegree_succ_le_of_mem_pderiv_support p i hm)
  rw [MvPolynomial.totalDegree_eq]
  apply (Finset.sup_lt_iff hpositive).mpr
  intro m hm
  exact Nat.lt_of_succ_le (totalDegree_succ_le_of_mem_pderiv_support p i hm)
end PermanentFormulaLowerBound
