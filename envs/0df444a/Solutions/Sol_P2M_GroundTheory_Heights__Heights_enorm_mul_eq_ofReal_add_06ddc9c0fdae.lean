-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_enorm_mul_eq_ofReal_add_06ddc9c0fdae
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T08:31:52.121381+00:00
-- url     : https://prove2.me/submissions/1307156d-7247-499a-a427-9de64f23ef26

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsConeSheetAreaLintegral
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PConeChartArea
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterFib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PConeSheetArea

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial MeasureTheory Matrix Set
open ReciprocityTheory.ChartRestriction.G.Geo (MRing PBlk IsArithVar IsGoodProj IsSheet fibre)
open scoped ENNReal ComplexOrder
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution {a r : ℝ} (hr : 0 ≤ r) :
    ‖a * r‖ₑ = ENNReal.ofReal a * ENNReal.ofReal r + ENNReal.ofReal (-a) * ENNReal.ofReal r := by
  rw [← ofReal_norm, Real.norm_eq_abs, abs_mul, abs_of_nonneg hr, ← add_mul,
    ENNReal.ofReal_mul (abs_nonneg a)]
  congr 1
  rcases le_total 0 a with ha | ha
  · rw [abs_of_nonneg ha, ENNReal.ofReal_of_nonpos (by linarith : -a ≤ 0), add_zero]
  · rw [abs_of_nonpos ha, ENNReal.ofReal_of_nonpos ha, zero_add]
end GroundTheory.Heights₂.Heights
