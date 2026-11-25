-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Xi.J2.de_cons
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:24:41.928805+00:00
-- url     : https://prove2.me/submissions/0c7f0f70-bc6a-45ee-8600-90325d266dce

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_TailInt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_GaugeSplittingAlgebra
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_J2_rhoSq_cons
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_J2_bco_cons

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
theorem _root_.solution {p m : ℕ} (a : Fin (p + 1) → ℂ) (w : ℂ) (b : Fin p → ℂ) (r : (Fin m → ℂ) × ℝ)
    (i : Fin (p + 1)) :
    de ((a, Fin.cons w b, r) : Xp (p + 1) m) i.succ = de ((a, Fin.cons 0 b, r) : Xp (p + 1) m) i.succ := by
  simp only [de, rhoSq_cons, bco_cons]
  rfl
end ReciprocityTheory.ChartRestriction.DS.Xi.J2
