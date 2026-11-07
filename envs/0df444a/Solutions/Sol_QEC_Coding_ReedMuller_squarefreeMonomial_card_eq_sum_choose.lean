-- Prove2me | solution 1 for QEC.Coding.ReedMuller.squarefreeMonomial_card_eq_sum_choose
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T15:13:20.442721+00:00
-- url     : https://prove2.me/submissions/33946c60-562b-4e09-a7b6-ee54fbaaac42

import Definitions.Def_QEC_Coding_Core_Definitions
import Definitions.Def_QEC_Coding_ReedMuller_Base
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
theorem _root_.solution (m r : Nat) :
    Fintype.card (SquarefreeMonomial m r) =
      ∑ i ∈ Finset.Icc 0 r, Nat.choose m i := by
  simpa [binomialUpTo] using card_squarefreeMonomial_eq_binomialUpTo m r
end QEC.Coding.ReedMuller
