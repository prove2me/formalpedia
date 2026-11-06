-- Prove2me | solution 1 for QEC.Semantics.FiniteKrausFamily.sameSpaceKnillLaflammeCriterion_exists_indexed_scalar_complete_diagonal_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T19:44:06.134558+00:00
-- url     : https://prove2.me/submissions/c35a51d0-63c2-4fae-a3d6-fa33fa47d4ae

import Definitions.Def_QEC_Semantics_Channels_KrausKnillLaflamme
import Definitions.Def_QEC_Semantics_Channels_ChoiKraus
import Definitions.Def_QEC_Semantics_ErrorCorrection_KLRecovery
import Theorems.Thm_QEC_Semantics_FiniteKrausFamily_indexedConditionWithScalar_complete_diagonal_sum
import Theorems.Thm_QEC_Semantics_FiniteKrausFamily_sameSpaceKnillLaflammeCriterion_iff_exists_indexed_scalar


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
    (E : FiniteKrausFamily ι H H) (C : QuantumCode H)
    (hE : E.Complete)
    (hKL : E.sameSpaceKnillLaflammeCriterion C) :
    ∃ scalar : ι → ι → Complex,
      IndexedKnillLaflammeConditionWithScalar E C scalar ∧
        (∑ i : ι, scalar i i) • C.projector = C.projector := by
  rcases (E.sameSpaceKnillLaflammeCriterion_iff_exists_indexed_scalar C).1 hKL with
    ⟨scalar, hscalar⟩
  exact ⟨scalar, hscalar,
    indexedConditionWithScalar_complete_diagonal_sum hE hscalar⟩
end QEC.Semantics.FiniteKrausFamily
