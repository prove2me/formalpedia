-- Prove2me | solution 1 for QEC.Semantics.FiniteKrausFamily.sameSpaceKnillLaflammeCriterion_iff_exists_indexed_scalar
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T11:37:40.377725+00:00
-- url     : https://prove2.me/submissions/8cb6e232-77b3-4b5c-aec8-f53ab2223727

import Definitions.Def_QEC_Semantics_Channels_Kraus
import Definitions.Def_QEC_Semantics_ErrorCorrection_KnillLaflamme
import Definitions.Def_QEC_Semantics_Channels_KrausKnillLaflamme
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
      ∃ scalar : ι → ι → Complex,
        ∀ i j : ι,
          ∀ x : H, x ∈ C.carrier →
            ∀ y : H, y ∈ C.carrier →
              inner Complex (E.operator i x) (E.operator j y) =
                scalar i j * inner Complex x y :=
  (indexedKnillLaflammeCriterion_iff_sameSpaceKnillLaflammeCriterion E C).symm
end QEC.Semantics.FiniteKrausFamily
