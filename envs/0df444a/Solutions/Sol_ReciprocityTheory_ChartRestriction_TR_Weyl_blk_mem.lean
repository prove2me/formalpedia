-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.TR.Weyl.blk_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T05:28:43.420325+00:00
-- url     : https://prove2.me/submissions/5782494c-efd0-4943-bed4-153c00498213

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
theorem _root_.solution {n : ℕ} (ε : Fin n → Bool) (b : Bool) (r : Fin (cnt ε b)) : ε (blk ε b r) = b := by
  have h := Finset.orderEmbOfFin_mem (univ.filter fun i : Fin n => ε i = b) rfl r
  exact (Finset.mem_filter.mp h).2
end ReciprocityTheory.ChartRestriction.TR.Weyl
