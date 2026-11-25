-- Prove2me | solution 1 for P2M_ReciprocityTheory_ChartRestriction_G_FD_FrequencyIndexing__k_injective_ab739a144fb6
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T13:10:13.712645+00:00
-- url     : https://prove2.me/submissions/d3411178-07d4-4213-8fa8-504e6d4e5dfb

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_TubeFourierExpansion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FrequencyIndexing
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_FD_FrequencyIndexing__k_spec_f7cb7fb69995

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.FrequencyIndexing
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ} (ω : Module.Basis (Fin n) ℝ (ι → ℝ))
namespace ReciprocityTheory.ChartRestriction.G.FD.FrequencyIndexing
theorem _root_.solution : Function.Injective (νk ω) := by
  intro k k' h
  funext i
  have h1 := νk_spec ω k i
  have h2 := νk_spec ω k' i
  rw [h] at h1
  exact_mod_cast h1.symm.trans h2
end ReciprocityTheory.ChartRestriction.G.FD.FrequencyIndexing
