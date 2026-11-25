-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Lap.LemK.rightHol_congr_on_omega
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:18:56.734794+00:00
-- url     : https://prove2.me/submissions/056d7297-c410-4b6b-8d58-513dda38e5da

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_KTypeLemma_TransferStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_KTypeLemma_TransferB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_PhiCasA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_PhiCas
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_KTypeLemma_RightHolRightHolEq
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Lap_LemK_positiveOmega_mem_nhds

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
theorem _root_.solution {X : Matrix (Fin n) (Fin n) ℂ} {G H : Matrix (Fin n) (Fin n) ℂ → ℂ}
    (h : Set.EqOn G H (OmegaP n)) {z : Matrix (Fin n) (Fin n) ℂ} (hz : z ∈ OmegaP n) :
    Rhol X G z = Rhol X H z := by
  show fderiv ℂ G z (z * X) = fderiv ℂ H z (z * X)
  rw [(h.eventuallyEq_of_mem (positiveOmega_mem_nhds hz)).fderiv_eq]
end ReciprocityTheory.ChartRestriction.DS.Lap.LemK
