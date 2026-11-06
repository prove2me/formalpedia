-- Prove2me | solution 1 for QEC.Semantics.FiniteKrausFamily.scale_sameSpaceKnillLaflammeCriterion
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T19:43:54.665367+00:00
-- url     : https://prove2.me/submissions/c756af20-18c0-4153-8c16-12d7b565627a

import Definitions.Def_QEC_Semantics_Channels_Kraus
import Definitions.Def_QEC_Semantics_ErrorCorrection_KnillLaflamme
import Definitions.Def_QEC_Semantics_Channels_KrausKnillLaflamme
import Theorems.Thm_QEC_Semantics_FiniteKrausFamily_scale_indexedKnillLaflammeConditionWithScalar
import Theorems.Thm_QEC_Semantics_FiniteKrausFamily_sameSpaceKnillLaflammeCriterion_iff_exists_indexed_scalar

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
    (amp : ι → Complex)
    (h : E.sameSpaceKnillLaflammeCriterion C) :
    (E.scale amp).sameSpaceKnillLaflammeCriterion C := by
  rcases (E.sameSpaceKnillLaflammeCriterion_iff_exists_indexed_scalar C).1 h with
    ⟨scalar, hscalar⟩
  exact
    ((E.scale amp).sameSpaceKnillLaflammeCriterion_iff_exists_indexed_scalar C).2
      ⟨fun i j => star (amp i) * amp j * scalar i j,
        scale_indexedKnillLaflammeConditionWithScalar E C amp hscalar⟩
end QEC.Semantics.FiniteKrausFamily
