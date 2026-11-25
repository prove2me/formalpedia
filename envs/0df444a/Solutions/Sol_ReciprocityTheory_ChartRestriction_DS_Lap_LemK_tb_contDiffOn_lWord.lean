-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Lap.LemK.tb_contDiffOn_lWord
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:46:46.11698+00:00
-- url     : https://prove2.me/submissions/80671aaf-3bc6-4000-aae7-beea42a0310d

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_KTypeLemma_TransferStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_PhiFacts
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_KTypeLemma_TransferB
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Lap_LemK_tb_contDiffOn_phiM
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Lap_LemK_tb_contDiffOn_lhol
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_isOpen_omega


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
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
namespace ReciprocityTheory.ChartRestriction.DS.Lap.LemK
theorem _root_.solution (μ : Fin n → ℤ) (D : List (Matrix (Fin n) (Fin n) ℂ)) :
    ContDiffOn ℂ ω (lWord D (PhiM μ)) (OmegaSet n) := by
  induction D with
  | nil => exact tb_contDiffOn_phiM μ
  | cons Z D ih => exact tb_contDiffOn_lhol isOpen_omega ih Z
end ReciprocityTheory.ChartRestriction.DS.Lap.LemK
