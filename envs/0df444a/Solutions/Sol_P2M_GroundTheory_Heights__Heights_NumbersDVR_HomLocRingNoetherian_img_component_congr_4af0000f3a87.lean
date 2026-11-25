-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_HomLocRingNoetherian_img_component_congr_4af0000f3a87
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T04:39:11.274789+00:00
-- url     : https://prove2.me/submissions/5f548606-b289-4a8c-ae4c-c42c79158833

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsHomLocRingLocal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PHomLocRingNoetherian
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_HomLocRingNoetherian_img_eq_zero_iff_1a7b10f3ef75

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NumbersDVR
open MvPolynomial
noncomputable section
universe u
open GroundTheory.Heights₂.Heights.NumbersDVR.HomLocRingNoetherian
variable {R : Type u} [CommRing R] {K : Type} [DecidableEq K] {ι : K → Type}
variable (P : Ideal (MRing ι R)) [P.IsPrime]
variable {P}
namespace GroundTheory.Heights₂.Heights.NumbersDVR.HomLocRingNoetherian
theorem _root_.solution (hP : IsMultiHomogIdeal P) {u v : MRing ι R} (huv : img P u = img P v)
    (d : K → ℕ) :
    img P (weightedHomogeneousComponent (blockWeight ι) d u) =
      img P (weightedHomogeneousComponent (blockWeight ι) d v) := by
  rw [← sub_eq_zero, ← map_sub, img_eq_zero_iff] at huv ⊢
  rw [← map_sub]
  exact hP _ huv d
end GroundTheory.Heights₂.Heights.NumbersDVR.HomLocRingNoetherian
