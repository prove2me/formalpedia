-- Prove2me | solution 1 for QEC.Semantics.FiniteKrausFamily.indexedConditionWithScalar_iff_indexedProjectorConditionWithScalar
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T19:43:50.577194+00:00
-- url     : https://prove2.me/submissions/5ab504a6-08e4-4d06-bc68-6336aacd62d2

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
    (E : FiniteKrausFamily ι H H) (C : QuantumCode H)
    (scalar : ι → ι → Complex) :
    IndexedKnillLaflammeConditionWithScalar E C scalar ↔
      IndexedKnillLaflammeProjectorConditionWithScalar E C scalar := by
  constructor
  · exact indexedProjectorConditionWithScalar_of_indexedConditionWithScalar
  · exact indexedConditionWithScalar_of_indexedProjectorConditionWithScalar
end QEC.Semantics.FiniteKrausFamily
