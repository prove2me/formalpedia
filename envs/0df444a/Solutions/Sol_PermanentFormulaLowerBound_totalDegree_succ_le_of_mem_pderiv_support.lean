-- Prove2me | solution 1 for PermanentFormulaLowerBound.totalDegree_succ_le_of_mem_pderiv_support
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:12.090475+00:00
-- url     : https://prove2.me/submissions/4432790a-9c00-4147-b89e-d3f010a67b14

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
theorem _root_.solution [CommSemiring F]
    (p : MvPolynomial ι F) (i : ι) {m : ι →₀ ℕ}
    (hm : m ∈ (MvPolynomial.pderiv i p).support) :
    Multiset.card (Finsupp.toMultiset m) + 1 ≤ p.totalDegree := by
  classical
  have hmcoeff : MvPolynomial.coeff m (MvPolynomial.pderiv i p) ≠ 0 :=
    MvPolynomial.mem_support_iff.mp hm
  have hparent : m + Finsupp.single i 1 ∈ p.support := by
    apply MvPolynomial.mem_support_iff.mpr
    intro hzero
    apply hmcoeff
    rw [MvPolynomial.coeff_pderiv, hzero, zero_mul]
  have hdegree := MvPolynomial.le_totalDegree hparent
  rw [Finsupp.card_toMultiset]
  change m.sum (fun _ e => e) + 1 ≤ p.totalDegree
  simpa [Finsupp.sum_add_index'] using hdegree
end PermanentFormulaLowerBound
