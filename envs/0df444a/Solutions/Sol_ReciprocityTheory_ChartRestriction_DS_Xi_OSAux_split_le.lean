-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Xi.OSAux.split_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:26:10.101561+00:00
-- url     : https://prove2.me/submissions/4a75715a-8921-4d2f-954b-fa88ece05749

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_Imports
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_RhoSqInsSucc
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_OSAux_splitE_mp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_OSAux_ins_splitE

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open scoped ENNReal
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Xi
open ReciprocityTheory.ChartRestriction.DS.Xi.OSAux
namespace ReciprocityTheory.ChartRestriction.DS.Xi.OSAux
theorem _root_.solution {p m : ℕ} (G : Xp (p + 1) m → ℝ≥0∞) :
    ∫⁻ x, G x ≤ ∫⁻ y : Yp p m, ∫⁻ z : ℂ, G (ins y z) := by
  have h := (splitE_mp p m).lintegral_comp_emb (splitE p m).measurableEmbedding
    (fun w => G (ins w.1 w.2))
  simp only [ins_splitE] at h
  exact h.trans_le (lintegral_prod_le _)
end ReciprocityTheory.ChartRestriction.DS.Xi.OSAux
