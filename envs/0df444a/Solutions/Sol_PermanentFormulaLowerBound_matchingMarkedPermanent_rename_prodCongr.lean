-- Prove2me | solution 1 for PermanentFormulaLowerBound.matchingMarkedPermanent_rename_prodCongr
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:13.787743+00:00
-- url     : https://prove2.me/submissions/5230598f-7f59-4f33-a492-6604a5724302

import Mathlib
import Definitions.Def_Permanent
import Theorems.Thm_PermanentFormulaLowerBound_permanentPolynomial_rename_prodCongr
import Theorems.Thm_PermanentFormulaLowerBound_matchingVariableEquiv_relabel_commutes

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentFormulaLowerBound
universe u v w
open scoped BigOperators Kronecker Matrix IntermediateField.algebraAdjoinAdjoin
namespace PermanentFormulaLowerBound
theorem _root_.solution
    {n : ℕ} {Y : Type u}
    (d₀ d : Y ↪ Fin n × Fin n)
    (r c : Equiv.Perm (Fin n))
    (he : ∀ y : Y, Equiv.prodCongr r c (d₀ y) = d y) :
    MvPolynomial.renameEquiv ℂ
        (Equiv.sumCongr (Equiv.refl Y)
          (matchingOutsideRelabelEquiv d₀ d
            (Equiv.prodCongr r c) he))
        (matchingMarkedPermanent d₀) =
      matchingMarkedPermanent d := by
  classical
  have hcomm := matchingVariableEquiv_relabel_commutes d₀ d
    (Equiv.prodCongr r c) he
  unfold matchingMarkedPermanent
  rw [← AlgEquiv.trans_apply, MvPolynomial.renameEquiv_trans, hcomm,
    ← MvPolynomial.renameEquiv_trans, AlgEquiv.trans_apply,
    permanentPolynomial_rename_prodCongr]
end PermanentFormulaLowerBound
