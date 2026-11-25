-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.S7.hw_tr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T13:07:49.086661+00:00
-- url     : https://prove2.me/submissions/d11e9173-ff77-4f57-87ff-45fee98c4c47

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_IsClosedKset
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_PsiExistsOfFormula
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_PhiCas
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_GelfandPhiA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_GelfandPhi
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_eOp_phiT
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_lhol_phiM_diag
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_lhol_phiM_lower


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
theorem _root_.solution (μ : Fin n → ℤ) :
    IsHWVec (fun a b => eOp (xTr n a b)) (fun a => -((μ a : ℤ) : ℝ)) (phiT μ) := by
  refine ⟨fun a => ?_, fun a b hab => ?_⟩
  · refine eOp_phiT μ _ _ fun z hz => ?_
    unfold xTr
    rw [lhol_phiM_diag μ _ hz]
    push_cast
    ring
  · have h0 : eOp (xTr n a b) (phiT μ) = (0 : ℂ) • phiT μ := by
      refine eOp_phiT μ _ _ fun z hz => ?_
      unfold xTr
      rw [lhol_phiM_lower μ hab hz]
      simp
    rw [h0, zero_smul]
end ReciprocityTheory.ChartRestriction.DS.S7
