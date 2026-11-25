-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Geo.abs_log_div_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T13:05:22.716547+00:00
-- url     : https://prove2.me/submissions/e3840de9-684e-434f-bc50-3492562d9f63

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterBridgeE
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterSheet
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_LocDens
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterBridgeJ

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo
open MvPolynomial MeasureTheory ReciprocityTheory.AnForm.M Topology Filter Set
namespace ReciprocityTheory.ChartRestriction.G.Geo
theorem _root_.solution {a b : ℝ} (ha : 0 ≤ a) (hb : 0 < b) :
    |Real.log (a / b)| ≤ |Real.log a| + |Real.log b| := by
  rcases ha.eq_or_lt with h | h
  · subst h
    simp
  · rw [Real.log_div h.ne' hb.ne', abs_le]
    constructor <;> linarith [le_abs_self (Real.log a), neg_abs_le (Real.log a),
      le_abs_self (Real.log b), neg_abs_le (Real.log b)]
end ReciprocityTheory.ChartRestriction.G.Geo
