-- Prove2me | solution 1 for QEC.Semantics.FiniteKrausFamily.indexedConditionWithScalar_complete_diagonal_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T11:33:50.044984+00:00
-- url     : https://prove2.me/submissions/bab9a76b-c4c3-48e0-bfb4-38b5db4cf4d7

import Definitions.Def_QEC_Semantics_Channels_KrausKnillLaflamme
import Definitions.Def_QEC_Semantics_Channels_ChoiKraus
import Definitions.Def_QEC_Semantics_ErrorCorrection_KLRecovery
import Theorems.Thm_QEC_Semantics_FiniteKrausFamily_indexedProjectorConditionWithScalar_complete_diagonal_sum
import Theorems.Thm_QEC_Semantics_FiniteKrausFamily_indexedProjectorConditionWithScalar_of_indexedConditionWithScalar


set_option autoImplicit false
universe u v w
open QEC
open QEC.Semantics
open scoped BigOperators ComplexOrder
noncomputable section
open QEC.Semantics.FiniteKrausFamily
variable {ι : Type v} [Fintype ι]
variable {κ : Type w} [Fintype κ]
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [FiniteQuantumSystem H]
namespace QEC.Semantics.FiniteKrausFamily
theorem _root_.solution
    {E : FiniteKrausFamily ι H H} {C : QuantumCode H}
    {scalar : ι → ι → Complex}
    (hE : E.Complete)
    (hKL : IndexedKnillLaflammeConditionWithScalar E C scalar) :
    (∑ i : ι, scalar i i) • C.projector = C.projector :=
  indexedProjectorConditionWithScalar_complete_diagonal_sum hE
    (indexedProjectorConditionWithScalar_of_indexedConditionWithScalar hKL)
end QEC.Semantics.FiniteKrausFamily
