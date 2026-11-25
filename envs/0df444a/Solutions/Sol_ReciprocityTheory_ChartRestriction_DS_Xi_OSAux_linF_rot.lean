-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Xi.OSAux.linF_rot
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:19:06.992814+00:00
-- url     : https://prove2.me/submissions/f8126aa2-21e4-40a8-870f-f028be63eb2c

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_Imports
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_RhoMulStar

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
theorem _root_.solution {p m : ℕ} (η η' : Fin p → ℂ) (ζ : Fin m → ℂ) (t : ℝ) (x : Xp p m) :
    linF η η' ζ (rot t x) = rho t * linF η η' ζ x := by
  simp only [ReciprocityTheory.ChartRestriction.DS.Xi.linF, rot]
  rw [mul_add, Finset.mul_sum, Finset.mul_sum]
  congr 1 <;> refine Finset.sum_congr rfl fun j _ => ?_ <;> ring
end ReciprocityTheory.ChartRestriction.DS.Xi.OSAux
