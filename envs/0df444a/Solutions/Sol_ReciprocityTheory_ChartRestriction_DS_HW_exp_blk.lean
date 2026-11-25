-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.HW.exp_blk
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:21:38.464928+00:00
-- url     : https://prove2.me/submissions/64442237-f3b5-4075-bdf6-c7e6fc523be0

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_ContinuousRepresentations_DerivExistsAllPosStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_OneParam
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_ContinuousRepresentations_Blocks
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_HW_eq_blkDiag
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_HW_exp_blkDiag

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Topology
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.HW
open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7
variable {n : ℕ}
namespace ReciprocityTheory.ChartRestriction.DS.HW
theorem _root_.solution {ε : Fin n → Bool} {X : Matrix (Fin n) (Fin n) ℂ} (hX : X * Jm ε = Jm ε * X) :
    NormedSpace.exp X = embM ε true (NormedSpace.exp (blkRes ε true X)) *
      embM ε false (NormedSpace.exp (blkRes ε false X)) := by
  conv_lhs => rw [eq_blkDiag hX, exp_blkDiag]
  rw [embM, embM, ← map_mul]
  congr 1
  funext t
  cases t <;> simp [Pi.mulSingle_apply]
end ReciprocityTheory.ChartRestriction.DS.HW
