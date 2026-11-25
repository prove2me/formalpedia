-- Prove2me | solution 1 for ReciprocityTheory.Neutral.Bridge.HCFR.infIdele_mem_rayUnits
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T15:30:22.690196+00:00
-- url     : https://prove2.me/submissions/8f520326-053f-4341-a18b-777096ffc467

import Definitions.Def_ReciprocityTheory_NeutralLocalFields_LocalFieldComparison_HCFFromRecipA
import Definitions.Def_ReciprocityTheory_NeutralLocalFields_LocalFieldComparison_HCFFromRecipB
import Theorems.Thm_ReciprocityTheory_Neutral_Bridge_HCFR_infIdele_snd

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option linter.style.haveILetI false
noncomputable section
open NumberField IsDedekindDomain Neutral.B1
open ReciprocityTheory ReciprocityTheory.Neutral ReciprocityTheory.Neutral.Bridge ReciprocityTheory.Neutral.Bridge.HCFR
variable (K : Type) [Field K] [NumberField K]
namespace ReciprocityTheory.Neutral.Bridge.HCFR
theorem _root_.solution (w : InfinitePlace K) (x : (w.Completion)ˣ) :
    infIdele K w x ∈ rayUnits K ⊤ ∅ := by
  refine ⟨fun w' hw' => by simp at hw', fun v => ⟨?_, 0, Submodule.mem_top, ?_⟩⟩
  · rw [infIdele_snd]
    exact map_one _
  · rw [infIdele_snd, sub_self]
    simp
end ReciprocityTheory.Neutral.Bridge.HCFR
