-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Xi.OSAux.cont_tailPt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:18:48.558037+00:00
-- url     : https://prove2.me/submissions/c89a855c-9085-41e0-95db-28129eb5d29f

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_Imports
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_RhoSqInsSucc

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
theorem _root_.solution {p m : ℕ} : Continuous (fun y : Yp p m => tailPt y) := by
  have hmid : Continuous fun y : Yp p m => (Fin.cons (0 : ℂ) y.2.1 : Fin (p + 1) → ℂ) :=
    continuous_pi (fun j => by
      induction j using Fin.cases with
      | zero => simp only [Fin.cons_zero]; exact continuous_const
      | succ k => simp only [Fin.cons_succ]; fun_prop)
  unfold ReciprocityTheory.ChartRestriction.DS.Xi.tailPt
  fun_prop
end ReciprocityTheory.ChartRestriction.DS.Xi.OSAux
