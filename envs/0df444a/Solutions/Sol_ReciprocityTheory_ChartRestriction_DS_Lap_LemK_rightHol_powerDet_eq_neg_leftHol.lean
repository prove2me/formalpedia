-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Lap.LemK.rightHol_powerDet_eq_neg_leftHol
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T13:03:25.331379+00:00
-- url     : https://prove2.me/submissions/aafebc07-51dc-4b47-a431-05385f952211

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_KTypeLemma_TransferStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_KTypeLemma_TransferB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_PhiCasA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_PhiCas
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_KTypeLemma_RightHolRightHolEq
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Lap_LemK_leftHol_neg
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Lap_LemK_tb_hWord_phiP


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset Matrix
open scoped ContDiff
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Lap ReciprocityTheory.ChartRestriction.DS.Lap.LemK
open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ}
namespace ReciprocityTheory.ChartRestriction.DS.Lap.LemK
theorem _root_.solution (μ : Fin n → ℤ) (X : Matrix (Fin n) (Fin n) ℂ) {z : Matrix (Fin n) (Fin n) ℂ}
    (hz : z ∈ OmegaP n) : Rhol X (PhiP μ) z = -Lhol X (PhiM μ) z⁻¹ := by
  have h := tb_hWord_phiP μ [X] z hz
  rw [← leftHol_neg]
  exact h
end ReciprocityTheory.ChartRestriction.DS.Lap.LemK
