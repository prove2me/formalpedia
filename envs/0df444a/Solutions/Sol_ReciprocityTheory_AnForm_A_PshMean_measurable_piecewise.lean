-- Prove2me | solution 1 for ReciprocityTheory.AnForm.A.PshMean.measurable_piecewise
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:11:54.074271+00:00
-- url     : https://prove2.me/submissions/a10892c7-718a-494e-a347-f1e6dd4d9308

import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_IsPshLocallyIntegrableStatement
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshMean
import Theorems.Thm_ReciprocityTheory_AnForm_A_PshMean_isOpen_inter_preimage

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Metric Set Filter Topology Real
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A ReciprocityTheory.AnForm.A.PshMean
noncomputable section
variable {D : ℕ}
namespace ReciprocityTheory.AnForm.A.PshMean
theorem _root_.solution {U : Set (Fin D → ℂ)} {φ : (Fin D → ℂ) → ℝ} (hU : IsOpen U)
    (hφ : UpperSemicontinuousOn φ U) : Measurable (U.indicator φ) := by
  refine measurable_of_Iio fun y => ?_
  rw [Set.indicator_preimage]
  exact (isOpen_inter_preimage hU hφ y).measurableSet.union
    ((measurable_zero measurableSet_Iio).diff hU.measurableSet)
end ReciprocityTheory.AnForm.A.PshMean
