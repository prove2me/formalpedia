-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Lap.LemK.tb_contDiffOn_phiM
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:34:09.222187+00:00
-- url     : https://prove2.me/submissions/f82c4d80-7d8e-4aec-b457-04aa54757245

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_KTypeLemma_TransferStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_PhiFacts
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_KTypeLemma_TransferB
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Lap_LemK_tb_contDiff_lead
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Lap_LemK_tb_contDiffOn_zpow

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
variable {n : ℕ}
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
namespace ReciprocityTheory.ChartRestriction.DS.Lap.LemK
theorem _root_.solution (μ : Fin n → ℤ) : ContDiffOn ℂ ω (PhiM μ) (OmegaSet n) := by
  show ContDiffOn ℂ ω (fun z => ∏ i : Fin n, lead ((i : ℕ) + 1) z ^ (-(μ i - muNext μ i))) (OmegaSet n)
  exact contDiffOn_prod fun i _ =>
    tb_contDiffOn_zpow (tb_contDiff_lead _).contDiffOn (fun x (hx : x ∈ OmegaSet n) => hx i) _
end ReciprocityTheory.ChartRestriction.DS.Lap.LemK
