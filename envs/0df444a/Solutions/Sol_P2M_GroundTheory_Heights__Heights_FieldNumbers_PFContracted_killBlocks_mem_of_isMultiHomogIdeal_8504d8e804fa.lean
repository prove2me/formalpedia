-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FieldNumbers_PFContracted_killBlocks_mem_of_isMultiHomogIdeal_8504d8e804fa
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T05:21:11.122834+00:00
-- url     : https://prove2.me/submissions/cc905d75-17f2-48cd-8906-3cfadb0e489d

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PPFContractedDim
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_PFContracted_killBlocks_of_isMultiHomog_d5143d61805c

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FieldNumbers
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR
noncomputable section
open GroundTheory.Heights₂.Heights.FieldNumbers.PFContracted
variable {K : Type*} [DecidableEq K] {ι : K → Type*} {F : Type*} [Field F]
namespace GroundTheory.Heights₂.Heights.FieldNumbers.PFContracted
theorem _root_.solution {Q : Ideal (MRing ι F)} (hQ : IsMultiHomogIdeal Q)
    (T : Finset K) {q : MRing ι F} (hq : q ∈ Q) : killBlocks T q ∈ Q := by
  rw [← sum_weightedHomogeneousComponent (blockWeight ι) q,
    finsum_eq_sum _ (weightedHomogeneousComponent_finsupp q), map_sum]
  refine Ideal.sum_mem _ fun b _ => ?_
  rw [killBlocks_of_isMultiHomog T (weightedHomogeneousComponent_isWeightedHomogeneous b q)]
  split_ifs
  · exact hQ q hq b
  · exact Q.zero_mem
end GroundTheory.Heights₂.Heights.FieldNumbers.PFContracted
