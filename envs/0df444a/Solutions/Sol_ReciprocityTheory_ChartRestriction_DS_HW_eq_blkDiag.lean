-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.HW.eq_blkDiag
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:12:17.376621+00:00
-- url     : https://prove2.me/submissions/a367b348-586c-4398-add5-09738c6228e5

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_ContinuousRepresentations_DerivExistsAllPosStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_OneParam
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_ContinuousRepresentations_Blocks
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_HW_blkRes_apply

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
    X = blkDiag ε (fun s => blkRes ε s X) := by
  ext a b
  obtain ⟨⟨s, i⟩, rfl⟩ := (blkSig ε).surjective a
  obtain ⟨⟨t, j⟩, rfl⟩ := (blkSig ε).surjective b
  rw [blkDiag_apply]
  by_cases hst : s = t
  · subst hst
    rw [Matrix.blockDiagonal'_apply_eq, blkRes_apply]
  · rw [Matrix.blockDiagonal'_apply_ne _ _ _ hst]
    refine (commJ_iff ε X).mp hX _ _ ?_
    rw [ε_blkSig ε s i, ε_blkSig ε t j]
    exact hst
end ReciprocityTheory.ChartRestriction.DS.HW
