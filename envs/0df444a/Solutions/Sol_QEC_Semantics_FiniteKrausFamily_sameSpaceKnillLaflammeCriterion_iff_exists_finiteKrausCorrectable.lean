-- Prove2me | solution 1 for QEC.Semantics.FiniteKrausFamily.sameSpaceKnillLaflammeCriterion_iff_exists_finiteKrausCorrectable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T11:57:11.498349+00:00
-- url     : https://prove2.me/submissions/0d664745-6e4d-4bbb-acfb-db439a38fc55

import Definitions.Def_QEC_Semantics_Channels_KrausKnillLaflamme
import Definitions.Def_QEC_Semantics_Channels_ChoiKraus
import Definitions.Def_QEC_Semantics_ErrorCorrection_KLRecovery
import Theorems.Thm_QEC_Semantics_FiniteKrausFamily_sameSpaceKnillLaflammeCriterion_of_finiteKrausCorrectable
import Theorems.Thm_QEC_Semantics_FiniteKrausFamily_exists_recovery_of_sameSpaceKnillLaflammeCriterion

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
    (E : FiniteKrausFamily ι H H) (C : QuantumCode H) (hE : E.Complete) :
    E.sameSpaceKnillLaflammeCriterion C ↔
      ∃ recovery : QuantumChannel H H, FiniteKrausCorrectable ι H H C E recovery := by
  constructor
  · intro hKL
    exact exists_recovery_of_sameSpaceKnillLaflammeCriterion E C hE hKL
  · rintro ⟨recovery, hcorrectable⟩
    exact sameSpaceKnillLaflammeCriterion_of_finiteKrausCorrectable E C recovery hcorrectable
end QEC.Semantics.FiniteKrausFamily
