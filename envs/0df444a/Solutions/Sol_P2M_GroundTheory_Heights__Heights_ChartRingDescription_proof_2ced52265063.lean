-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ChartRingDescription_proof_2ced52265063
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T04:54:12.259899+00:00
-- url     : https://prove2.me/submissions/1be87eea-76e5-4984-b569-1511fdeec425

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_ChartPowNeZero
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_AddBlockData_chartPow_ne_zero_0ca6bf248649
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_AddBlockData_elt_div_elt_eac7066069af

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
open MvPolynomial
noncomputable section
namespace GroundTheory.Heights₂.Heights
namespace ChartRingDescription
theorem _root_.solution : ChartRingDescription.Statement := by
  intro ι _ _ n P D c hc j hj
  have hp := AddBlockData.chartPow_ne_zero hc D.deg
  set S := Subring.closure (insert (D.xi c j)⁻¹ (P.chartRing c : Set P.FunField))
  have hA : (P.chartRing c : Set P.FunField) ⊆ S := fun x hx ↦
    Subring.subset_closure (Set.mem_insert_of_mem _ hx)
  have hinv : (D.xi c j)⁻¹ ∈ S := Subring.subset_closure (Set.mem_insert _ _)
  apply le_antisymm
  · rw [AddBlockData.extChartRing, Subring.closure_le]
    rintro x (⟨v, rfl⟩ | ⟨i, rfl⟩)
    · exact hA (Subring.subset_closure ⟨v, rfl⟩)
    · show D.elt i / D.elt j ∈ S
      rw [D.elt_div_elt hc i j]
      exact S.mul_mem (hA (D.chart_mem c hc i)) hinv
  · have hA' : P.chartRing c ≤ D.extChartRing c j := by
      rw [ArithVariety.chartRing]
      exact Subring.closure_mono Set.subset_union_left
    rw [Subring.closure_le]
    rintro x (rfl | hx)
    · obtain ⟨u, hu, hsum⟩ := D.generating c hc
      have h : (D.xi c j)⁻¹ = ∑ i, u i * (D.elt i / D.elt j) := by
        rw [← one_mul (D.xi c j)⁻¹, ← hsum, Finset.sum_mul]
        refine Finset.sum_congr rfl fun i _ ↦ ?_
        rw [D.elt_div_elt hc i j, mul_assoc]
        rfl
      rw [h]
      refine Subring.sum_mem _ fun i _ ↦ Subring.mul_mem _ (hA' (hu i)) ?_
      exact Subring.subset_closure (Or.inr ⟨i, rfl⟩)
    · exact hA' hx
end ChartRingDescription
end GroundTheory.Heights₂.Heights
