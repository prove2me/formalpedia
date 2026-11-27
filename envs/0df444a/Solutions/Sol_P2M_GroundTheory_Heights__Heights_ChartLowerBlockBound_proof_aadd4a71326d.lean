-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ChartLowerBlockBound_proof_aadd4a71326d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T04:53:14.497255+00:00
-- url     : https://prove2.me/submissions/e4da31d1-c9f5-4e3c-af3c-ebbc573423ef

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_StatementsCusp
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_TransposeEqOfPosSemidef
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_PChartLowerHeightsound
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartLowerBlockBound_period_apply_of_le_d76b460d7d89
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartLowerBlockBound_entry_bound_a0f56bc4d3ff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open Matrix
noncomputable section
namespace GroundTheory.Heights₂.Heights
namespace ChartLowerBlockBound
theorem _root_.solution : ChartLowerBlockBound.Statement := by
  intro D T
  choose C hC using ChartLowerBlockBound.entry_bound D
  refine ⟨1 + ∑ i, ∑ l, |C i l|, ?_, ?_⟩
  · have : 0 ≤ ∑ i, ∑ l, |C i l| :=
      Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _
    linarith
  · intro p hp ℓ i l hi
    rw [ChartLowerBlockBound.period_apply_of_le D T p.1 ℓ i l hi]
    have h1 : |C i l| ≤ ∑ l', |C i l'| :=
      Finset.single_le_sum (f := fun l' => |C i l'|) (fun _ _ => abs_nonneg _) (Finset.mem_univ l)
    have h2 : ∑ l', |C i l'| ≤ ∑ i', ∑ l', |C i' l'| :=
      Finset.single_le_sum (f := fun i' => ∑ l', |C i' l'|)
        (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) (Finset.mem_univ i)
    have h3 := hC i l p hp
    have h4 := le_abs_self (C i l)
    linarith
end ChartLowerBlockBound
end GroundTheory.Heights₂.Heights
