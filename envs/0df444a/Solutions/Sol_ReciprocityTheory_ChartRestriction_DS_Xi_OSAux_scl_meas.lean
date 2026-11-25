-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Xi.OSAux.scl_meas
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:20:40.626189+00:00
-- url     : https://prove2.me/submissions/9230f399-2b16-446c-a1f5-95bbc797c31f

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_Imports
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_RhoSqNonneg

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
theorem _root_.solution {p m : ℕ} : Measurable (fun q : ℝ × Xp (p + 1) m => scl q.1 q.2) := by
  have h1 : Measurable (fun q : ℝ × Xp (p + 1) m =>
      Function.update q.2.1 0 ((q.1 : ℂ) * q.2.1 0)) := by
    refine measurable_pi_lambda _ (fun i => ?_)
    by_cases hi : i = 0
    · subst hi
      simp only [Function.update_apply, if_true]
      fun_prop
    · simp only [Function.update_apply, hi, if_false]
      fun_prop
  have h2 : Measurable (fun q : ℝ × Xp (p + 1) m =>
      Function.update q.2.2.1 0 (q.2.2.1 0 / (q.1 : ℂ))) := by
    refine measurable_pi_lambda _ (fun i => ?_)
    by_cases hi : i = 0
    · subst hi
      simp only [Function.update_apply, if_true]
      fun_prop
    · simp only [Function.update_apply, hi, if_false]
      fun_prop
  unfold scl
  fun_prop
end ReciprocityTheory.ChartRestriction.DS.Xi.OSAux
