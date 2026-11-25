-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.S7.InfKA.continuous_Gint
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:44:21.915181+00:00
-- url     : https://prove2.me/submissions/3af3a0cc-687c-4779-844f-31aaa177c9c1

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_IsClosedKset
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_KFacts
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_PhiFacts
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_DerivG
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_ByParts
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_DTauFacts
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_DerivGA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_ContinuousOnFderivPhiM
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_InfKA_continuousOn_phiM
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_InfKA_continuous_P
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_InfKA_conj_mem_omega
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_InfKA_continuous_B

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
theorem _root_.solution (T : KType ε Λ) (μ : Fin n → ℤ) {x : Matrix (Fin n) (Fin n) ℂ}
    (hx : x.PosDef) : Continuous (Gint T μ x) := by
  have hphi : Continuous fun k : KG ε => PhiM μ (toMK k⁻¹ * x * toMK k) :=
    (continuousOn_phiM μ).comp_continuous (continuous_B x) (fun k => conj_mem_omega hx k)
  show Continuous fun k => PhiM μ (toMK k⁻¹ * x * toMK k) • (T.op k * projW T * T.op k⁻¹)
  exact hphi.smul (continuous_P T)
end ReciprocityTheory.ChartRestriction.DS.S7.InfKA
