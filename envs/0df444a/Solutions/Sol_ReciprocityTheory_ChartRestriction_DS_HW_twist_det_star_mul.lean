-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.HW.twist_det_star_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:03:34.701239+00:00
-- url     : https://prove2.me/submissions/7ced067d-a66b-4951-9e36-45684b157143

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_PsiExistsStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_InhabA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_ModelTwist

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.HW
open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7
variable {n : ℕ}
namespace ReciprocityTheory.ChartRestriction.DS.HW
theorem _root_.solution {ε : Fin n → Bool} (k : KG ε) : star (toMK k).det * (toMK k).det = 1 := by
  obtain ⟨hu, -⟩ := k.2
  calc star (toMK k).det * (toMK k).det = (star (toMK k)).det * (toMK k).det := by
        rw [Matrix.star_eq_conjTranspose, Matrix.det_conjTranspose]
    _ = (star (toMK k) * toMK k).det := (Matrix.det_mul _ _).symm
    _ = 1 := by
        rw [show star (toMK k) * toMK k = 1 from Unitary.star_mul_self_of_mem hu, Matrix.det_one]
end ReciprocityTheory.ChartRestriction.DS.HW
