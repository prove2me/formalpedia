-- Prove2me | solution 1 for QEC.Semantics.FiniteKrausFamily.sameSpaceKnillLaflammeCriterion_iff_indexedProjectorEquation
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T11:37:41.096504+00:00
-- url     : https://prove2.me/submissions/663bd4cd-d377-4a7a-8810-d96df6c4b2c7

import Definitions.Def_QEC_Semantics_Channels_Kraus
import Definitions.Def_QEC_Semantics_ErrorCorrection_KnillLaflamme
import Definitions.Def_QEC_Semantics_Channels_KrausKnillLaflamme
import Theorems.Thm_QEC_Semantics_FiniteKrausFamily_indexedKnillLaflammeCriterion_iff_indexedProjectorEquation
import Theorems.Thm_QEC_Semantics_FiniteKrausFamily_indexedKnillLaflammeCriterion_iff_sameSpaceKnillLaflammeCriterion

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
    E.sameSpaceKnillLaflammeCriterion C ↔
      IndexedKnillLaflammeProjectorEquation E C := by
  rw [← indexedKnillLaflammeCriterion_iff_sameSpaceKnillLaflammeCriterion]
  exact indexedKnillLaflammeCriterion_iff_indexedProjectorEquation E C
end QEC.Semantics.FiniteKrausFamily
