-- Prove2me | solution 1 for QEC.Semantics.FiniteKrausFamily.indexedKnillLaflammeCriterion_iff_indexedProjectorEquation
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T11:33:05.798826+00:00
-- url     : https://prove2.me/submissions/31c347b0-81b4-45ea-ace3-870232ba24eb

import Definitions.Def_QEC_Semantics_Channels_Kraus
import Definitions.Def_QEC_Semantics_ErrorCorrection_KnillLaflamme
import Definitions.Def_QEC_Semantics_Channels_KrausKnillLaflamme
import Theorems.Thm_QEC_Semantics_FiniteKrausFamily_indexedProjectorConditionWithScalar_of_indexedConditionWithScalar
import Theorems.Thm_QEC_Semantics_FiniteKrausFamily_indexedConditionWithScalar_of_indexedProjectorConditionWithScalar

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
    IndexedKnillLaflammeCriterion E C ↔
      IndexedKnillLaflammeProjectorEquation E C := by
  constructor
  · rintro ⟨scalar, hscalar⟩
    exact ⟨scalar,
      indexedProjectorConditionWithScalar_of_indexedConditionWithScalar hscalar⟩
  · rintro ⟨scalar, hscalar⟩
    exact ⟨scalar,
      indexedConditionWithScalar_of_indexedProjectorConditionWithScalar hscalar⟩
end QEC.Semantics.FiniteKrausFamily
