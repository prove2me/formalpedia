-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.S7.InfKA.continuous_Ek
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:59:19.031347+00:00
-- url     : https://prove2.me/submissions/9689519e-c9db-481f-a914-b2b03ca010d1

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_IsClosedKset
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_KFacts
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_PhiFacts
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_DerivG
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_ByParts
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_DTauFacts
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_DerivGA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_ContinuousOnFderivPhiM
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_InfKA_continuous_B
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_InfKA_continuous_Gint
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_InfKA_continuous_DkL

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
variable {n : ℕ} {ε : Fin n → Bool} {Λ : Fin n → ℝ}
open ReciprocityTheory.ChartRestriction.DS.S7.InfKA
namespace ReciprocityTheory.ChartRestriction.DS.S7.InfKA
theorem _root_.solution (T : KType ε Λ) (μ : Fin n → ℤ) {x : Matrix (Fin n) (Fin n) ℂ} (hx : x.PosDef)
    (φ : Matrix (Fin n) (Fin n) ℂ →L[ℂ] ℂ) (A M : Matrix (Fin n) (Fin n) ℂ) : Continuous (Ek T μ x φ A M) := by
  have hBA : Continuous fun k : KG ε => toMK k⁻¹ * A * toMK k := continuous_B A
  show Continuous fun k => φ (toMK k⁻¹ * A * toMK k) • DkL T μ x k M +
    φ (toMK k⁻¹ * A * toMK k * M - M * (toMK k⁻¹ * A * toMK k)) • Gint T μ x k
  exact ((φ.continuous.comp hBA).smul (continuous_DkL T μ hx M)).add
    ((φ.continuous.comp ((hBA.matrix_mul continuous_const).sub (continuous_const.matrix_mul hBA))).smul
      (continuous_Gint T μ hx))
end ReciprocityTheory.ChartRestriction.DS.S7.InfKA
