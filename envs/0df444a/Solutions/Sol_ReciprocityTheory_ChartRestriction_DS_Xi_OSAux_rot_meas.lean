-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Xi.OSAux.rot_meas
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:19:10.314973+00:00
-- url     : https://prove2.me/submissions/1eaa5b5b-1361-4e3f-9f62-5c729f0ef3bc

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_Imports
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_RhoMulStar
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace ReciprocityTheory.ChartRestriction.DS.Xi
namespace OSAux
private lemma rho_den (t : ℝ) : ((1 + t ^ 2 : ℝ) : ℂ) ≠ 0 := by
  exact Complex.ofReal_ne_zero.mpr (by positivity)
private theorem continuous_rho_tail_integrals : Continuous rho := by
  unfold rho
  exact ((continuous_const.add (Complex.continuous_ofReal.mul continuous_const)).pow 2).div
    (Complex.continuous_ofReal.comp (continuous_const.add (continuous_id.pow 2))) rho_den
end OSAux
end ReciprocityTheory.ChartRestriction.DS.Xi
end
end

set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open scoped ENNReal
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Xi
open ReciprocityTheory.ChartRestriction.DS.Xi.OSAux
namespace ReciprocityTheory.ChartRestriction.DS.Xi.OSAux
theorem _root_.solution {p m : ℕ} : Measurable (fun q : ℝ × Xp p m => rot q.1 q.2) := by
  have hu : Continuous rho := continuous_rho_tail_integrals
  have hc : Continuous (fun q : ℝ × ReciprocityTheory.ChartRestriction.DS.Xi.Xp p m => rot q.1 q.2) := by
    unfold rot
    fun_prop
  exact hc.measurable
end ReciprocityTheory.ChartRestriction.DS.Xi.OSAux
