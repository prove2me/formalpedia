-- Prove2me | solution 1 for QEC.Semantics.FiniteKrausFamily.indexedKnillLaflammeCriterion_iff_projectorEquation
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T19:44:01.461514+00:00
-- url     : https://prove2.me/submissions/2f3d90ce-70df-474b-b25e-15e1bc50c62c

import Definitions.Def_QEC_Semantics_Channels_Kraus
import Definitions.Def_QEC_Semantics_ErrorCorrection_KnillLaflamme
import Definitions.Def_QEC_Semantics_Channels_KrausKnillLaflamme
import Theorems.Thm_QEC_Semantics_FiniteKrausFamily_indexedKnillLaflammeCriterion_iff_sameSpaceKnillLaflammeCriterion
import Theorems.Thm_QEC_Semantics_FiniteKrausFamily_sameSpaceKnillLaflammeCriterion_iff_projectorEquation

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
      KnillLaflammeProjectorEquation C E.sameSpaceErrorSet := by
  rw [indexedKnillLaflammeCriterion_iff_sameSpaceKnillLaflammeCriterion]
  exact sameSpaceKnillLaflammeCriterion_iff_projectorEquation E C
end QEC.Semantics.FiniteKrausFamily
