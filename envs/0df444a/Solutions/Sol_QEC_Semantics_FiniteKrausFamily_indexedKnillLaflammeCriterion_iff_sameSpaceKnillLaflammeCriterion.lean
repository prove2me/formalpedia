-- Prove2me | solution 1 for QEC.Semantics.FiniteKrausFamily.indexedKnillLaflammeCriterion_iff_sameSpaceKnillLaflammeCriterion
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T11:35:12.901683+00:00
-- url     : https://prove2.me/submissions/ea7c229b-48b3-4575-9547-2b58ff8f8d58

import Definitions.Def_QEC_Semantics_Channels_Kraus
import Definitions.Def_QEC_Semantics_ErrorCorrection_KnillLaflamme
import Definitions.Def_QEC_Semantics_Channels_KrausKnillLaflamme
import Theorems.Thm_QEC_Semantics_FiniteKrausFamily_indexedConditionWithScalar_of_matrixConditionWithScalar
import Theorems.Thm_QEC_Semantics_FiniteKrausFamily_matrixConditionWithScalar_of_indexedConditionWithScalar

set_option autoImplicit false
universe u v
open QEC
open QEC.Semantics
noncomputable section
open QEC.Semantics.FiniteKrausFamily
variable {ι : Type v} [Fintype ι]
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [FiniteQuantumSystem H]
namespace QEC.Semantics.FiniteKrausFamily
theorem _root_.solution
    (E : FiniteKrausFamily ι H H) (C : QuantumCode H) :
    IndexedKnillLaflammeCriterion E C ↔ E.sameSpaceKnillLaflammeCriterion C := by
  constructor
  · rintro ⟨scalar, hscalar⟩
    exact ⟨sameSpaceScalar E scalar,
      matrixConditionWithScalar_of_indexedConditionWithScalar hscalar⟩
  · rintro ⟨scalar, hscalar⟩
    exact ⟨fun i j => scalar (E.operator i) (E.operator j),
      indexedConditionWithScalar_of_matrixConditionWithScalar hscalar⟩
end QEC.Semantics.FiniteKrausFamily
