-- Prove2me | solution 1 for ReciprocityTheory.PGsh.Up.killedGen
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T16:15:44.794801+00:00
-- url     : https://prove2.me/submissions/edab716a-95f1-471e-aab5-668b1b6b4df1

import Definitions.Def_ReciprocityTheory_DualLattices_UnramifiedCokernelLowerBoundOf
import Definitions.Def_ReciprocityTheory_DualLattices_IsLocalOfIntegers
import Definitions.Def_ReciprocityTheory_DualLattices_KilledGen
import Theorems.Thm_ReciprocityTheory_PGsh_Up_prod_le_of_gen


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up
namespace ReciprocityTheory.PGsh.Up
theorem _root_.solution : KilledGenStatement := by
  intro C _ v R _ _ hv M _ _ x d c hx hy hc
  obtain ⟨y, hy⟩ := hy
  have h := prod_le_of_gen hv hx y hy (fun _ => c) (fun i => ⟨0, by simp [hc]⟩)
  simpa [Finset.prod_const, Finset.card_univ, Fintype.card_fin] using h
end ReciprocityTheory.PGsh.Up
