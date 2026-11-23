-- Prove2me | solution 1 for StableMSR.Recovery.WindowMasks.native_regional_block_incidences
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @lreyzin
-- created : 2026-11-23T00:12:17.84786+00:00
-- url     : https://prove2.me/submissions/d3f9af5c-249f-408c-a586-750c9010b5e7
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_StableMSR_SingleWindowGrammar
import Theorems.Thm_StableMSR_Recovery_SingleWindows_emit_singleton_separator_grammar
import Theorems.Thm_StableMSR_Recovery_SingleWindows_singleton_board_describes_regional_incidences
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 12000
open StableMSR.Recovery StableMSR.Recovery.Havens StableMSR.Recovery.PartialDecompositions
open StableMSR.Recovery.DecompositionSearch StableMSR.Recovery.WindowCuts StableMSR.Recovery.SingleSearch
open RobertsonSeymour1986.GM5
open StableMSR.Recovery.Compiler StableMSR.Recovery.OracleQueries StableMSR.Recovery.Supplement
open StableMSR.Recovery.WindowCSP StableMSR.Recovery.WindowPorts StableMSR.Recovery.WindowMasks StableMSR.Recovery.SingleWindows
open StableMSR.Recovery.WindowProfiles (piece keys)
theorem solution : ∃c D b : ℕ,0< c ∧ 0< b ∧ ∀e : ℚ,0< e → e<1 → ∃cmd : Cmd,maskSpec e c D b cmd := by
  obtain ⟨c,D,b,cp,bp,source⟩:=emit_singleton_separator_grammar
  refine ⟨c,D,b,cp,bp,?_⟩;intro e ep el
  obtain ⟨cmd,run⟩:=source e ep el
  refine ⟨cmd,?_⟩;intro x s hk hn dm ready
  obtain ⟨t,z,H,ex,time,space,out,sem⟩:=run x s hk hn dm ready
  exact ⟨t,z,H,ex,time,space,out,singleton_board_describes_regional_incidences _ _ _ dm sem⟩
