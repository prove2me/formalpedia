-- Prove2me | solution 1 for QEC.Coding.ReedMuller.reedMullerCode_dimension_eq_binomialUpTo
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T11:23:35.212923+00:00
-- url     : https://prove2.me/submissions/59e975bb-57e0-420f-9a28-ce685757e615

import Definitions.Def_QEC_Coding_Core_Definitions
import Definitions.Def_QEC_Coding_ReedMuller_Base
import Theorems.Thm_QEC_Coding_ReedMuller_reedMullerCode_dimension_eq_card_squarefree
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_toOperator
attribute [local simp] QEC.Coding.ChainComplexData.pureZLogicalQuotientEquivMiddleHomology_mk
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_toOperator


section
noncomputable section
namespace QEC
namespace Coding
namespace ReedMuller
open scoped BigOperators
private theorem card_squarefreeMonomial_eq_binomialUpTo (m r : Nat) :
    Fintype.card (SquarefreeMonomial m r) = binomialUpTo m r := by
  classical
  rw [Fintype.card_subtype]
  change ((Finset.univ : Finset (Finset (Fin m))).filter fun support =>
      support.card ≤ r).card = _
  let supports := (Finset.univ : Finset (Fin m)).powerset
  have hall : (Finset.univ : Finset (Finset (Fin m))) = supports := by
    ext support
    simp [supports]
  rw [hall]
  calc
    (supports.filter fun support => support.card ≤ r).card =
        (supports.filter fun support =>
          support.card ∈ Finset.Icc 0 r).card := by
      congr 1
      ext support
      simp
    _ = ∑ i ∈ Finset.Icc 0 r,
        (supports.filter fun support => support.card = i).card := by
      symm
      exact Finset.sum_card_fiberwise_eq_card_filter
        supports (Finset.Icc 0 r) Finset.card
    _ = ∑ i ∈ Finset.Icc 0 r, Nat.choose m i := by
      apply Finset.sum_congr rfl
      intro i _hi
      rw [← Finset.powersetCard_eq_filter, Finset.card_powersetCard]
      simp
    _ = binomialUpTo m r := rfl
end ReedMuller
end Coding
end QEC
end
end

set_option autoImplicit false
noncomputable section
open QEC
open QEC.Coding
open QEC.Coding.ReedMuller
open scoped BigOperators
namespace QEC.Coding.ReedMuller
theorem _root_.solution (r m : Nat) :
    Dimension (reedMullerCode r m) = binomialUpTo m r := by
  rw [reedMullerCode_dimension_eq_card_squarefree,
    card_squarefreeMonomial_eq_binomialUpTo]
end QEC.Coding.ReedMuller
