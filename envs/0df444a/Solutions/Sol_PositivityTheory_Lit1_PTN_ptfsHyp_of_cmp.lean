-- Prove2me | solution 1 for PositivityTheory.Lit1.PTN.ptfsHyp_of_cmp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T05:19:08.824494+00:00
-- url     : https://prove2.me/submissions/59db9c3b-70ea-41d4-8993-9a136df9cd7e

import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_PoitouTateDuality_PtfsTransfer
import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_PoitouTateDuality_PtfsShaHalf
import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_PoitouTateDuality_PtfsHyp
import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_PoitouTateDuality_PtfsHypOfCmp
import Theorems.Thm_PositivityTheory_Lit1_PTN_nineTermExact_of_nineCmp
import Theorems.Thm_PositivityTheory_Lit1_PTN_shaDual_of_perfectPair


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Representation Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Published GlobalTheory.Published.PoitouTate
  PositivityTheory.PoitouTateConclusion
open PositivityTheory PositivityTheory.Lit1 PositivityTheory.Lit1.PTN
namespace PositivityTheory.Lit1.PTN
theorem _root_.solution (hN : NineCmpFS) (hS : ShaCmpFS) : PositivityTheory.PTN.PtfsHyp := by
  intro K _ _ l _ r hl hr ζ hζ inv hinv S hS' Av hAv μ hμ M _ _ _ _ _ ρ hρ
  exact ⟨nineTermExact_of_nineCmp S Av μ _ ρ hρ
      (hN K l r hl hr ζ hζ inv hinv S hS' Av hAv μ hμ M ρ hρ),
    shaDual_of_perfectPair S Av μ ρ (hS K l r hl hr ζ hζ inv hinv S hS' Av hAv μ hμ M ρ hρ).1
      (hS K l r hl hr ζ hζ inv hinv S hS' Av hAv μ hμ M ρ hρ).2⟩
end PositivityTheory.Lit1.PTN
