-- Prove2me | solution 1 for P2M_GlobalTheory_JR_HeightSquareIntegrable_tsum_pi_prod_le__f38cf3f9f8ef
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T02:31:07.475998+00:00
-- url     : https://prove2.me/submissions/093323ba-1cbe-41bb-97dd-4a938432ae9b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsTestRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsSubringEqOK
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_EtaleHermitianPairStructureFactsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsIntegralOrInvIsIntegralFiniteExtUltrametricStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IdempotentDecompositionOfIntegralityStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnimodularHeightSqLintegralLtTop

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
open scoped Pointwise ENNReal NNReal
noncomputable section
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.HeightSquareIntegrable
namespace GlobalTheory.JR.HeightSquareIntegrable
theorem _root_.solution {ι : Type} [Fintype ι] {α : ι → Type} (f : ∀ i, α i → ℝ≥0∞) :
    ∑' t : ∀ i, α i, ∏ i, f i (t i) ≤ ∏ i, ∑' x, f i x := by
  classical
  rw [ENNReal.tsum_eq_iSup_sum]
  refine iSup_le fun s => ?_
  calc ∑ t ∈ s, ∏ i, f i (t i)
      ≤ ∑ t ∈ Fintype.piFinset (fun i => s.image (fun t => t i)), ∏ i, f i (t i) := by
        refine Finset.sum_le_sum_of_subset fun t ht => ?_
        exact Fintype.mem_piFinset.2 fun i => Finset.mem_image_of_mem _ ht
    _ = ∏ i, ∑ x ∈ s.image (fun t => t i), f i x := (Finset.prod_univ_sum _ _).symm
    _ ≤ _ := Finset.prod_le_prod' fun i _ => ENNReal.sum_le_tsum _
end GlobalTheory.JR.HeightSquareIntegrable
