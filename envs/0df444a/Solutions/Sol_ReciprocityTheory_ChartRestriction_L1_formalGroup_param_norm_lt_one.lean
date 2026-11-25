-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L1.formalGroup_param_norm_lt_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T14:11:49.051649+00:00
-- url     : https://prove2.me/submissions/88a5c060-53a5-402d-b81f-f61e967ed8f0

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_TorDefs
import Definitions.Def_Formalism_EllipticTorsion_FormalGroupPointsNoTorsion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_TorChord
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_chord_norm_u_sq

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
theorem _root_.solution (W : WeierstrassCurve C) (hW : IntegralModel W) (P : W.toAffine.Point) (hP : InFormalGroupPoints P) :
    ‖uOf P‖ < 1 := by
  rcases P with _ | @⟨x, y, h⟩
  · simp [uOf]
  · have hx : 1 < ‖x‖ := hP
    have hu := chord_norm_u_sq W hW h.1 hx
    show ‖-x / y‖ < 1
    by_contra hcon
    rw [not_lt] at hcon
    have : 1 ≤ ‖-x / y‖ ^ 2 := one_le_pow₀ hcon
    nlinarith
end ReciprocityTheory.ChartRestriction.L1
