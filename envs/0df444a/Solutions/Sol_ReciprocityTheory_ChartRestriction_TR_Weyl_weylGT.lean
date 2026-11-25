-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.TR.Weyl.weylGT
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T14:11:04.755809+00:00
-- url     : https://prove2.me/submissions/7db727bd-0caa-4fd5-9c8d-0013388c5eb8

import Definitions.Def_ReciprocityTheory_ReductiveGroups_SymplecticTraces_WeylCharacters_AltBranchStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_SymplecticTraces_WeylCharacters_AntitoneOfMemInterl
import Theorems.Thm_ReciprocityTheory_ChartRestriction_TR_Weyl_wdenSucc
import Theorems.Thm_ReciprocityTheory_ChartRestriction_TR_Weyl_antitone_of_mem_interl
import Theorems.Thm_ReciprocityTheory_ChartRestriction_TR_Weyl_altBranch

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.TR ReciprocityTheory.ChartRestriction.TR.Weyl
namespace ReciprocityTheory.ChartRestriction.TR.Weyl
theorem _root_.solution : WeylGTStatement := by
  intro K _ n
  induction n with
  | zero =>
    intro lam _ t _
    simp [wden, gtChar, alt]
  | succ n ih =>
    intro lam hlam t ht
    rw [wdenSucc, altBranch K n lam hlam t ht, gtChar, mul_sum, mul_sum]
    refine sum_congr rfl fun mu hmu => ?_
    rw [← ih mu (antitone_of_mem_interl hlam hmu) (fun i => t i.castSucc) (fun i => ht _)]
    ring
end ReciprocityTheory.ChartRestriction.TR.Weyl
