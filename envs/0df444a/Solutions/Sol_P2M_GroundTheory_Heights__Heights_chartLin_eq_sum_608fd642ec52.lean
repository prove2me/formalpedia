-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_chartLin_eq_sum_608fd642ec52
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T08:34:15.415981+00:00
-- url     : https://prove2.me/submissions/50d0cab4-6c67-4aa9-bcbf-7cefc36ff16e

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_StatementsChartFirstGroupDvd
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_StatementsNormOfDividedForm
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_PChartNorm
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_chartLoc_algebraMap_tower_3afd568a4b3d
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_chartX_C_e13c0da01265
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_algebraMap_localization_C_8e2c282ddfe8

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
theorem _root_.solution (u : Fin n → F) :
    algebraMap (ChartInc I t e) (ChartLoc I t e p) (chartLin I t e u) =
      ∑ m, algebraMap F (Localization.AtPrime p) (u m) •
        algebraMap (ChartInc I t e) (ChartLoc I t e p) (chartX I t e (X m)) := by
  simp only [chartLin, linForm, map_sum, map_mul, Algebra.smul_def]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [← algebraMap_localization_C p, chartLoc_algebraMap_tower, chartX_C]
end GroundTheory.Heights₂.Heights
