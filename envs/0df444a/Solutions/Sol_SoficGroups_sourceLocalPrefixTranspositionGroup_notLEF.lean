-- Prove2me | solution 1 for SoficGroups.sourceLocalPrefixTranspositionGroup_notLEF
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:01.668904+00:00
-- url     : https://prove2.me/submissions/48a77920-2ab5-4972-a38b-b39dbb11ded3

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_ThompsonFFiniteQuotient_finite_group_commute_of_thompsonF_two_relations
import Theorems.Thm_SoficGroups_ThompsonFTwoRelatorLEF_not_lef_of_thompsonF_two_relations
import Theorems.Thm_SoficGroups_ThompsonFLocalWitness_source_relator_one
import Theorems.Thm_SoficGroups_ThompsonFLocalWitness_source_relator_two
import Theorems.Thm_SoficGroups_ThompsonFLocalWitness_source_generators_not_commute

set_option autoImplicit true
noncomputable section
open SoficGroups
namespace SoficGroups
theorem _root_.solution :
    ¬ LEF
      (ThompsonPrefixInsertion.localPrefixTranspositionGroup
        ThompsonPrefixLocal.sourceLocalWord) := by
  apply ThompsonFTwoRelatorLEF.not_lef_of_thompsonF_two_relations
    ThompsonFLocalWitness.sourceGeneratorA
    ThompsonFLocalWitness.sourceGeneratorB
    ThompsonFLocalWitness.source_relator_one
    ThompsonFLocalWitness.source_relator_two
    ThompsonFLocalWitness.source_generators_not_commute
  intro n x y hfirst hsecond
  exact ThompsonFFiniteQuotient.finite_group_commute_of_thompsonF_two_relations
    x y hfirst hsecond
end SoficGroups
