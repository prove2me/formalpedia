-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.S7.hw_rev
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T13:14:37.696849+00:00
-- url     : https://prove2.me/submissions/ff1f22d8-7184-4dff-94e1-02a2ef90fce5

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_IsClosedKset
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_PsiExistsOfFormula
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_PhiCas
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_GelfandPhiA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_GelfandPhi
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_lhol_neg
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
    IsHWVec (fun a b => eOp (xRev n a b)) (fun a => ((μ (Fin.rev a) : ℤ) : ℝ)) (phiT μ) := by
  refine ⟨fun a => ?_, fun a b hab => ?_⟩
  · refine eOp_phiT μ _ _ fun z hz => ?_
    unfold xRev
    rw [lhol_neg, lhol_phiM_diag μ _ hz]
    push_cast
    ring
  · have h0 : eOp (xRev n a b) (phiT μ) = (0 : ℂ) • phiT μ := by
      refine eOp_phiT μ _ _ fun z hz => ?_
      unfold xRev
      rw [lhol_neg, lhol_phiM_lower μ (Fin.rev_lt_rev.2 hab) hz]
      simp
    rw [h0, zero_smul]
end ReciprocityTheory.ChartRestriction.DS.S7
