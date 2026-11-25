-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L1.formalGroup_add_estimate
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T14:33:10.628223+00:00
-- url     : https://prove2.me/submissions/db7b4c6b-9f03-496d-97e8-30de65feb9aa

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_TorDefs
import Definitions.Def_Formalism_EllipticTorsion_FormalGroupPointsNoTorsion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_TorChord
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_formalGroup_param_norm_lt_one
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_chord_adjoin_le
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_chord_eval_est
import Theorems.Thm_Formalism_ELL_formal_group_points_hom
import Theorems.Thm_Formalism_ELL_wChordSeries
import Theorems.Thm_Formalism_ELL_wSeriesUnique


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
theorem _root_.solution [CompleteSpace C] (W : WeierstrassCurve C) (hW : IntegralModel W)
    (P Q : W.toAffine.Point) (hP : InFormalGroupPoints P) (hQ : InFormalGroupPoints Q) :
    ‖uOf (P + Q) - uOf P - uOf Q‖ ≤ (max ‖uOf P‖ ‖uOf Q‖) ^ 2 := by
  obtain ⟨w, hw, -⟩ := wSeriesUnique.{0} C W
  obtain ⟨F, hFc, h00, h10, h01, hch⟩ := wChordSeries.{0} C W w hw
  have hF : Formalism.G.IntegralMv F := fun d => chord_adjoin_le W hW (hFc d)
  rw [formal_group_points_hom.{0} C W w F hW hw hF h00 hch P Q hP hQ]
  exact chord_eval_est hF h00 h10 h01 (formalGroup_param_norm_lt_one W hW P hP) (formalGroup_param_norm_lt_one W hW Q hQ)
end ReciprocityTheory.ChartRestriction.L1
