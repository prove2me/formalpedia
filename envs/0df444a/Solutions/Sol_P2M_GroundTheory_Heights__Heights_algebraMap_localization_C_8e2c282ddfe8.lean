-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_algebraMap_localization_C_8e2c282ddfe8
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:43:02.576657+00:00
-- url     : https://prove2.me/submissions/40f84227-4805-4b75-bf9f-6f69f0847d04

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_StatementsChartFirstGroupDvd
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_StatementsNormOfDividedForm
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_PChartNorm

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
variable {F : Type} [Field F] {n e : ℕ} (I : Ideal (MvPolynomial (Fin n) F)) (t : Fin n → F)
  (p : Ideal (MvPolynomial (Fin e × Fin n) F)) [p.IsPrime]
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution (c : F) :
    algebraMap (MvPolynomial (Fin e × Fin n) F) (Localization.AtPrime p) (C c) =
      algebraMap F (Localization.AtPrime p) c := by
  rw [IsScalarTower.algebraMap_apply F (MvPolynomial (Fin e × Fin n) F) (Localization.AtPrime p),
    MvPolynomial.algebraMap_eq]
end GroundTheory.Heights₂.Heights
