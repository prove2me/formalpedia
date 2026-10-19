-- Prove2me | solution 1 for SoficGroups.SourceTopLevelCompression.sourceLocalPrefixTranspositionGroup_lef_of_source_finite_models
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:01.668904+00:00
-- url     : https://prove2.me/submissions/3803e721-f617-44dd-a546-f84554f9464f

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_exists_soficApproximation_size_tendsto
import Theorems.Thm_SoficGroups_ninePrefixElementaryGroup_countable
import Theorems.Thm_SoficGroups_lef_of_expanding_centralizer_models

set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.SourceTopLevelCompression
open Filter
namespace SoficGroups.SourceTopLevelCompression
theorem _root_.solution
    (hmodels :
      ∀ A : SoficGroups.SoficApproximation
          (SoficGroups.prefixElementaryGroup SoficGroups.ninePrefixCode),
        Tendsto (fun n => (A.model n).size) atTop atTop →
          ∀ F : Finset
              (SoficGroups.ThompsonPrefixInsertion.localPrefixTranspositionGroup
                  SoficGroups.ThompsonPrefixLocal.sourceLocalWord),
            Nonempty (SoficGroups.ExpandingCentralizerFiniteModel
              (SoficGroups.ThompsonPrefixInsertion.localPrefixTranspositionGroup
                  SoficGroups.ThompsonPrefixLocal.sourceLocalWord) F))
    (hsource : SoficGroups.Sofic
      (SoficGroups.prefixElementaryGroup SoficGroups.ninePrefixCode)) :
    SoficGroups.LEF
      (SoficGroups.ThompsonPrefixInsertion.localPrefixTranspositionGroup
        SoficGroups.ThompsonPrefixLocal.sourceLocalWord) := by
  letI : SoficGroups.Sofic
      (SoficGroups.prefixElementaryGroup SoficGroups.ninePrefixCode) :=
    hsource
  letI : Countable
      (SoficGroups.prefixElementaryGroup SoficGroups.ninePrefixCode) :=
    SoficGroups.ninePrefixElementaryGroup_countable
  obtain ⟨A, hA⟩ := SoficGroups.exists_soficApproximation_size_tendsto
    (SoficGroups.prefixElementaryGroup SoficGroups.ninePrefixCode)
  exact SoficGroups.lef_of_expanding_centralizer_models (hmodels A hA)
end SoficGroups.SourceTopLevelCompression
