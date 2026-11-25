-- Prove2me | solution 1 for PI.ExistsGaugeMeasureForEachRank.W.mem_UWb_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:02:07.280095+00:00
-- url     : https://prove2.me/submissions/354b3a7b-2c60-4f21-a031-20e31d7f9068

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_ExistsGaugeMeasureForEachRank
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CircleGaugeAction_DglApplyOff
import Theorems.Thm_PI_ExistsGaugeMeasureForEachRank_W_dgl_mem
import Theorems.Thm_PI_ExistsGaugeMeasureForEachRank_W_eq_dgl
import Theorems.Thm_PI_ExistsGaugeMeasureForEachRank_W_dgl_norm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open PI PI.ExistsGaugeMeasureForEachRank PI.ExistsGaugeMeasureForEachRank.W
variable {r : ℕ}
namespace PI.ExistsGaugeMeasureForEachRank.W
theorem _root_.solution (g : Mat 0 r) :
    g ∈ UWb 0 r ↔ ∃ u : ℂ, (starRingEnd ℂ) u * u = 1 ∧ g = dgl r u := by
  constructor
  · intro hg
    have e := eq_dgl hg
    exact ⟨g (cI r) (cI r), dgl_norm (e ▸ hg), e⟩
  · rintro ⟨u, hu, rfl⟩
    exact dgl_mem hu
end PI.ExistsGaugeMeasureForEachRank.W
