-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.HW.inK_blkRes
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:16:25.892948+00:00
-- url     : https://prove2.me/submissions/9817ce31-977d-4d03-a430-7aaeea5af6a5

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_ContinuousRepresentations_DerivExistsAllPosStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_OneParam
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_ContinuousRepresentations_Blocks
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_HW_blkRes_apply
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_HW_Jm_allPos

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
theorem _root_.solution {ε : Fin n → Bool} {X : Matrix (Fin n) (Fin n) ℂ} (hX : inK ε X) (s : Bool) :
    inK (fun _ : Fin (blkP ε s) => true) (blkRes ε s X) := by
  refine ⟨?_, by rw [Jm_allPos, Matrix.mul_one, Matrix.one_mul]⟩
  show (blkRes ε s X)ᴴ * Jm (fun _ : Fin (blkP ε s) => true) +
    Jm (fun _ : Fin (blkP ε s) => true) * blkRes ε s X = 0
  rw [Jm_allPos, Matrix.mul_one, Matrix.one_mul]
  ext i j
  have h := congrFun (congrFun hX.1 (blkSig ε ⟨s, i⟩)) (blkSig ε ⟨s, j⟩)
  rw [Jm, Matrix.add_apply, Matrix.mul_diagonal, Matrix.diagonal_mul, ε_blkSig ε s i,
    ε_blkSig ε s j] at h
  simp only [Matrix.add_apply, Matrix.conjTranspose_apply, blkRes_apply, Matrix.zero_apply] at h ⊢
  cases s <;> simp at h ⊢ <;> first | linear_combination h | linear_combination -h
end ReciprocityTheory.ChartRestriction.DS.HW
