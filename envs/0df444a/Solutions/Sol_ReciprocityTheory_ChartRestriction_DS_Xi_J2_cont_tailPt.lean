-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Xi.J2.cont_tailPt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:17:38.907893+00:00
-- url     : https://prove2.me/submissions/99622a00-2dd2-4ebf-a007-59065136ffcb

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_TailInt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_GaugeSplittingAlgebra
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_J2_cont_cons

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped ENNReal
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Xi
open ReciprocityTheory.ChartRestriction.DS.Xi.J2
namespace ReciprocityTheory.ChartRestriction.DS.Xi.J2
theorem _root_.solution {p m : ℕ} :
    Continuous (tailPt : (Fin (p + 1) → ℂ) × (Fin p → ℂ) × (Fin m → ℂ) × ℝ → Xp (p + 1) m) := by
  unfold tailPt
  exact continuous_fst.prodMk ((cont_cons.comp (continuous_const.prodMk
    (continuous_fst.comp continuous_snd))).prodMk (continuous_snd.comp continuous_snd))
end ReciprocityTheory.ChartRestriction.DS.Xi.J2
