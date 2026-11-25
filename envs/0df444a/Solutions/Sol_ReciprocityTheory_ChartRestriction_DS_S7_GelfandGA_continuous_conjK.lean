-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.S7.GelfandGA.continuous_conjK
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:15:03.999483+00:00
-- url     : https://prove2.me/submissions/3926ca84-a22a-469b-ac68-86adb5797174

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_IsClosedKset
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_PsiExistsOfFormula
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_PhiCasA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_PhiFacts
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_KFacts
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_ContinuousOnFderivPhiP
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_GelfandGB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_GelfandGA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset MeasureTheory Matrix
open scoped ComplexOrder ContDiff ENNReal
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7
open ReciprocityTheory.ChartRestriction.DS
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ}
open ReciprocityTheory.ChartRestriction.DS.S7.GelfandGA
local notation "𝕄" => Fin n → Fin n → ℂ
namespace ReciprocityTheory.ChartRestriction.DS.S7.GelfandGA
theorem _root_.solution (ε : Fin n → Bool) : Continuous (conjK ε) := by
  rw [continuous_clm_apply]
  intro y
  have h1 : Continuous (fun k : KG ε => toMK k) := by
    unfold toMK
    fun_prop
  have h2 : Continuous (fun k : KG ε => toMK k⁻¹) := h1.comp continuous_inv
  show Continuous (fun k : KG ε => toMK k⁻¹ * (show Matrix (Fin n) (Fin n) ℂ from y) * toMK k)
  exact (h2.matrix_mul continuous_const).matrix_mul h1
end ReciprocityTheory.ChartRestriction.DS.S7.GelfandGA
