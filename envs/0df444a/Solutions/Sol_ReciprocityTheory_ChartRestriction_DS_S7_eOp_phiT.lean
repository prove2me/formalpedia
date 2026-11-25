-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.S7.eOp_phiT
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T13:02:08.38922+00:00
-- url     : https://prove2.me/submissions/f0779250-c412-484b-b047-57a0de6a16fc

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_IsClosedKset
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_PsiExistsOfFormula
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_PhiCas
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_GelfandPhiA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_GelfandPhi
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_phiT_eqOn
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_eOp_apply
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_lhol_congr


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
namespace ReciprocityTheory.ChartRestriction.DS.S7
theorem _root_.solution (μ : Fin n → ℤ) (X : Matrix (Fin n) (Fin n) ℂ) (c : ℂ)
    (h : ∀ z ∈ OmegaSet n, Lhol X (PhiM μ) z = c * PhiM μ z) : eOp X (phiT μ) = c • phiT μ := by
  apply Subtype.ext
  funext z
  rw [eOp_apply]
  simp only [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul]
  by_cases hz : z ∈ OmegaSet n
  · rw [ltOp_of_mem _ hz, lhol_congr (phiT_eqOn μ).symm hz, h z hz, ← phiT_eqOn μ hz]
  · rw [ltOp_of_not_mem _ hz]
    simp [phiT, Set.indicator_apply, hz]
end ReciprocityTheory.ChartRestriction.DS.S7
