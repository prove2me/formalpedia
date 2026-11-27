-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.TR.Weyl.blk_strictMono
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T05:29:05.198037+00:00
-- url     : https://prove2.me/submissions/644517a6-2ba9-498d-900e-bef1408f3cdb

import Definitions.Def_ReciprocityTheory_ReductiveGroups_SymplecticTraces_WeylCharacters_AntitoneOfMemInterl
import Definitions.Def_ReciprocityTheory_ReductiveGroups_SymplecticTraces_WeylCharacters_BlockCombStatement

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
theorem _root_.solution {n : ℕ} (ε : Fin n → Bool) (b : Bool) : StrictMono (blk ε b) :=
  fun _ _ h => (Finset.orderEmbOfFin (univ.filter fun i : Fin n => ε i = b) rfl).strictMono h
end ReciprocityTheory.ChartRestriction.TR.Weyl
