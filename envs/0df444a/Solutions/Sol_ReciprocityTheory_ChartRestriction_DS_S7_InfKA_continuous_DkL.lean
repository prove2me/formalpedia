-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.S7.InfKA.continuous_DkL
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:50:28.597987+00:00
-- url     : https://prove2.me/submissions/7126a609-697f-4a7a-b115-3471c4db19c6

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_IsClosedKset
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_KFacts
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_PhiFacts
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_DerivG
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_ByParts
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_DTauFacts
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_DerivGA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_ContinuousOnFderivPhiM
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_InfKA_continuousOn_fderiv_phiM
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_InfKA_continuousOn_phiM
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_InfKA_continuous_P
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_InfKA_conj_mem_omega
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_InfKA_DkL_apply
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
theorem _root_.solution (T : KType ε Λ) (μ : Fin n → ℤ) {x : Matrix (Fin n) (Fin n) ℂ} (hx : x.PosDef)
    (Y : Matrix (Fin n) (Fin n) ℂ) : Continuous fun k => DkL T μ x k Y := by
  have hB : Continuous fun k : KG ε => toMK k⁻¹ * x * toMK k := continuous_B x
  have hmem : ∀ k : KG ε, toMK k⁻¹ * x * toMK k ∈ OmegaSet n := fun k => conj_mem_omega hx k
  have hop : Continuous fun k : KG ε => T.op k := continuous_subtype_val.comp T.cont
  have hphi : Continuous fun k : KG ε => PhiM μ (toMK k⁻¹ * x * toMK k) :=
    (continuousOn_phiM μ).comp_continuous hB hmem
  have hd : Continuous fun k : KG ε => fderiv ℂ (PhiM μ) (toMK k⁻¹ * x * toMK k) :=
    (continuousOn_fderiv_phiM μ).comp_continuous hB hmem
  have harg : Continuous fun k : KG ε => toMK k⁻¹ * x * toMK k * Y - Y * (toMK k⁻¹ * x * toMK k) :=
    (hB.matrix_mul continuous_const).sub (continuous_const.matrix_mul hB)
  simp only [DkL_apply]
  exact ((hd.clm_apply harg).smul (continuous_P T)).add
    (hphi.smul ((hop.mul continuous_const).mul (hop.comp continuous_inv)))
end ReciprocityTheory.ChartRestriction.DS.S7.InfKA
