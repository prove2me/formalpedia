-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FieldNumbers_PFContracted_blockDeg_component_mem_56f385ad8a51
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T04:28:21.587611+00:00
-- url     : https://prove2.me/submissions/dcfcad88-c484-43cd-9f70-9d4dbf467924

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PPFContractedDim
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PPFContracted
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_PFContracted_component_blockDeg_of_isMultiHomog_bfebfe40735a

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
universe u
open GroundTheory.Heights₂.Heights.FieldNumbers.PFContracted
variable {K : Type*} [DecidableEq K] {ι : K → Type*} {F : Type*} [Field F]
attribute [local instance] MvPolynomial.weightedGradedAlgebra
namespace GroundTheory.Heights₂.Heights.FieldNumbers.PFContracted
theorem _root_.solution {I : Ideal (MRing ι F)} (hI : IsMultiHomogIdeal I) (k : K) (n : ℕ)
    {r : MRing ι F} (hr : r ∈ I) : weightedHomogeneousComponent (blockDeg k) n r ∈ I := by
  rw [← sum_weightedHomogeneousComponent (blockWeight ι) r,
    finsum_eq_sum _ (weightedHomogeneousComponent_finsupp r), map_sum]
  refine Ideal.sum_mem _ fun b _ => ?_
  rw [component_blockDeg_of_isMultiHomog (weightedHomogeneousComponent_isWeightedHomogeneous b r)]
  split_ifs
  · exact hI r hr b
  · exact I.zero_mem
end GroundTheory.Heights₂.Heights.FieldNumbers.PFContracted
