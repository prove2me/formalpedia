-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_sum_weightedHomogeneousComponent_image_27a7ee41f296
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T08:40:44.316306+00:00
-- url     : https://prove2.me/submissions/9571da98-b175-41d8-974b-b8ed1fbd24d3

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_PHomogGeneratorsExist

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
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution (f : MvPolynomial (Coord n) ℤ) :
    ∑ m ∈ f.support.image (Finsupp.weight (coordDeg n)), weightedHomogeneousComponent (coordDeg n) m f = f := by
  conv_rhs => rw [← sum_weightedHomogeneousComponent (coordDeg n) f]
  refine (finsum_eq_sum_of_support_subset _ ?_).symm
  intro m hm
  rw [Function.mem_support] at hm
  rw [Finset.coe_image, Set.mem_image]
  by_contra h
  refine hm (weightedHomogeneousComponent_eq_zero' m f fun d hd hdm ↦ h ⟨d, hd, hdm⟩)
end GroundTheory.Heights₂.Heights
