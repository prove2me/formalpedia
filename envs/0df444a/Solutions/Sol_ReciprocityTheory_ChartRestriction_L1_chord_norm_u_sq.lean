-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L1.chord_norm_u_sq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T14:00:00.36049+00:00
-- url     : https://prove2.me/submissions/e3c3bc3c-0ab2-47fe-a400-e1ce4403f1d4

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_TorDefs
import Definitions.Def_Formalism_EllipticTorsion_FormalGroupPointsNoTorsion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_TorChord
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_chord_norm_y_sq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped Classical
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.L1
open Formalism.L2.Th1.CM Formalism.ELL WeierstrassCurve
open Formalism.L2.Th1.E (px py IntCurve)
open Formalism.L2.Th1.A (shortW)
variable {C : Type} [NormedField C] [IsUltrametricDist C]
namespace ReciprocityTheory.ChartRestriction.L1
theorem _root_.solution (W : WeierstrassCurve C) (hW : IntegralModel W) {x y : C}
    (h : W.toAffine.Equation x y) (hx : 1 < ‖x‖) : ‖-x / y‖ ^ 2 * ‖x‖ = 1 := by
  have hy := chord_norm_y_sq W hW h hx
  have hx0 : 0 < ‖x‖ := by linarith
  have hx0' := hx0.ne'
  rw [norm_div, norm_neg, div_pow, hy]
  field_simp
end ReciprocityTheory.ChartRestriction.L1
