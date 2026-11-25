-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.HW.exp_blkDiag
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:12:31.897479+00:00
-- url     : https://prove2.me/submissions/25293fc4-73ae-4991-ab0a-1eae7814b052

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_ContinuousRepresentations_DerivExistsAllPosStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_OneParam
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_ContinuousRepresentations_Blocks
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_HW_continuous_blkDiag

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
theorem _root_.solution (ε : Fin n → Bool) (v : ∀ s : Bool, Matrix (Fin (blkP ε s)) (Fin (blkP ε s)) ℂ) :
    NormedSpace.exp (blkDiag ε v) = blkDiag ε (fun s => NormedSpace.exp (v s)) := by
  letI : ∀ s : Bool, NormedRing (Matrix (Fin (blkP ε s)) (Fin (blkP ε s)) ℂ) :=
    fun _ => Matrix.linftyOpNormedRing
  letI : ∀ s : Bool, NormedAlgebra ℚ (Matrix (Fin (blkP ε s)) (Fin (blkP ε s)) ℂ) :=
    fun _ => Matrix.linftyOpNormedAlgebra
  letI : ∀ s : Bool, NormedAlgebra ℂ (Matrix (Fin (blkP ε s)) (Fin (blkP ε s)) ℂ) :=
    fun _ => Matrix.linftyOpNormedAlgebra
  haveI : ∀ s : Bool, CompleteSpace (Matrix (Fin (blkP ε s)) (Fin (blkP ε s)) ℂ) :=
    fun _ => FiniteDimensional.complete ℂ _
  letI : NormedRing (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra ℚ (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedAlgebra
  have h := NormedSpace.map_exp (blkDiag ε) (continuous_blkDiag ε) v
  exact h.symm.trans (congrArg _ (Pi.exp_def v))
end ReciprocityTheory.ChartRestriction.DS.HW
