-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L1.formalGroup_param_sq_norm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T05:27:55.260216+00:00
-- url     : https://prove2.me/submissions/04ba0396-15ee-49d4-8314-88bce9aca7db

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
theorem _root_.solution (W : WeierstrassCurve C) (hW : IntegralModel W) (P : W.toAffine.Point) (hP : InFormalGroupPoints P)
    (h0 : P ≠ 0) : ‖uOf P‖ ^ 2 * ‖px W P‖ = 1 := by
  rcases P with _ | @⟨x, y, h⟩
  · exact absurd rfl h0
  · exact chord_norm_u_sq W hW h.1 hP
end ReciprocityTheory.ChartRestriction.L1
