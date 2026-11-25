-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Xi.J2.rhoSq_cons
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:18:07.350819+00:00
-- url     : https://prove2.me/submissions/cd8eb6be-531e-4bbc-b44e-2414ec31d589

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_TailInt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_GaugeSplittingAlgebra

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
    rhoSq ((a, Fin.cons w b, r) : Xp (p + 1) m) i.succ = rhoSq ((a, Fin.cons 0 b, r) : Xp (p + 1) m) i.succ := by
  simp [rhoSq, Lsq, Fin.sum_univ_succ]
end ReciprocityTheory.ChartRestriction.DS.Xi.J2
