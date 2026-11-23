-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.HW.exists_curve
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:07:04.315295+00:00
-- url     : https://prove2.me/submissions/1d2dbce7-812d-4a3b-ad4c-8bd7337385eb

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_PsiExistsStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_OneParam
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_HW_toMK_onepCurve

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
theorem _root_.solution (ε : Fin n → Bool) {X : Matrix (Fin n) (Fin n) ℂ} (hX : inK ε X) :
    ∃ γ : ℝ → KG ε, ∀ t : ℝ, toMK (γ t) = NormedSpace.exp ((t : ℂ) • X) := ⟨onepCurve ε hX, toMK_onepCurve ε hX⟩
end ReciprocityTheory.ChartRestriction.DS.HW
