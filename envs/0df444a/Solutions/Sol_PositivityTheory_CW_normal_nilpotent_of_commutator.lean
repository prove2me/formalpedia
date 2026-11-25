-- Prove2me | solution 1 for PositivityTheory.CW.normal_nilpotent_of_commutator
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:03:47.914999+00:00
-- url     : https://prove2.me/submissions/8a92b1d5-4875-4376-9f93-955f89190c65

import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_CasselmanWallach_FunctionalCalculusLaws
import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_CasselmanWallach_CommutatorAdjointHolds
import Theorems.Thm_PositivityTheory_CW_GradedNormalNilpotent_main

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Finset ReciprocityTheory.ChartRestriction.DS Polynomial
open PositivityTheory PositivityTheory.CW
namespace PositivityTheory.CW
theorem _root_.solution : A1 → A2 → A3 → A4 → CommutatorAdjointModLower → A5 := by
  intro h1 h2 h3 h4 h5 n ε V _ _ E hE
  obtain ⟨hm, ho, he, hmu, hc, -, hz⟩ := h1 n ε V E hE
  exact GradedNormalNilpotent.main ⟨hm, ho, he, hmu, hc, hz⟩ (h2 n ε V E hE) (h3 n ε V E hE) h4 (h5 n ε V E hE)
end PositivityTheory.CW
