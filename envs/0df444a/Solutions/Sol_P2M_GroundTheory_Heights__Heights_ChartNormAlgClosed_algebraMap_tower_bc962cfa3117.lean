-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ChartNormAlgClosed_algebraMap_tower_bc962cfa3117
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:10:20.475561+00:00
-- url     : https://prove2.me/submissions/155e4102-be51-4593-b7d5-1e4383a79e6c

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_StatementsChartFirstGroupDvd
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsChartNormAlgClosed
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsChartNormSep
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PChartNormAlgClosed

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial
noncomputable section
open GroundTheory.Heights₂.Heights.ChartNormAlgClosed
variable {F : Type} [Field F] {n e : ℕ} (I : Ideal (MvPolynomial (Fin n) F)) (t : Fin n → F)
  (p : Ideal (MvPolynomial (Fin e × Fin n) F)) [p.IsPrime]
namespace GroundTheory.Heights₂.Heights.ChartNormAlgClosed
theorem _root_.solution (x : MvPolynomial (Fin e × Fin n) F) :
    algebraMap (Localization.AtPrime p) (ChartLoc I t e p) (algebraMap _ _ x) =
      algebraMap (ChartInc I t e) (ChartLoc I t e p) (algebraMap _ (ChartInc I t e) x) := by
  rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]
end GroundTheory.Heights₂.Heights.ChartNormAlgClosed
