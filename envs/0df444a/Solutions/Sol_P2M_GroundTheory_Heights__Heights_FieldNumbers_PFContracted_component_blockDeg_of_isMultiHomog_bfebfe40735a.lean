-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FieldNumbers_PFContracted_component_blockDeg_of_isMultiHomog_bfebfe40735a
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T03:53:36.897272+00:00
-- url     : https://prove2.me/submissions/588809f1-98fb-46b7-a391-0483942627a1

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PPFContractedDim
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PPFContracted
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_PFContracted_weight_blockDeg_b5265fab4acc

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
theorem _root_.solution {p : MRing ι F} {b : K → ℕ} (hp : IsMultiHomog p b)
    (k : K) (n : ℕ) :
    weightedHomogeneousComponent (blockDeg k) n p = if b k = n then p else 0 := by
  ext d
  rw [coeff_weightedHomogeneousComponent, weight_blockDeg]
  by_cases hd : coeff d p = 0
  · split_ifs <;> simp [hd]
  · have hw : Finsupp.weight (blockWeight ι) d = b := hp hd
    rw [hw]
    split_ifs <;> simp
end GroundTheory.Heights₂.Heights.FieldNumbers.PFContracted
