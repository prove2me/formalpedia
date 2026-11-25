-- Prove2me | solution 1 for ReciprocityTheory.Coh.modT_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T15:03:35.69948+00:00
-- url     : https://prove2.me/submissions/0a527cb7-9dbf-45f8-94c8-9aac451c3747

import Definitions.Def_ReciprocityTheory_GroupCohomology_CupConnRightStatement
import Definitions.Def_ReciprocityTheory_GroupCohomology_DEqZeroOfMemB
import Definitions.Def_ReciprocityTheory_GroupCohomology_ConnNatHolds
import Definitions.Def_ReciprocityTheory_GroupCohomology_IsSuccSubset
import Definitions.Def_ReciprocityTheory_GroupCohomology_FinGen
import Theorems.Thm_ReciprocityTheory_Coh_hom_H_smul
import Theorems.Thm_ReciprocityTheory_Coh_lES_holds


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.Coh
open Cx Function
universe u
namespace ReciprocityTheory.Coh
theorem _root_.solution : ModTStatement.{u} := by
  intro R _ A C i p t δ hi hs hc n
  obtain ⟨⟨δ0, hc0, hl⟩, huniq⟩ := lES_holds R A A C i p hs
  obtain rfl : δ = δ0 := huniq δ δ0 hc hc0
  refine ⟨fun x => ?_, hl.exC n, fun x => ?_⟩
  · rw [hl.exB n x]
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨y, hom_H_smul i t hi n y⟩
    · rintro ⟨y, rfl⟩
      exact ⟨y, hom_H_smul i t hi n y⟩
  · rw [LinearMap.mem_range, ← hom_H_smul i t hi (n + 1) x]
    exact (hl.exA n x).symm
end ReciprocityTheory.Coh
