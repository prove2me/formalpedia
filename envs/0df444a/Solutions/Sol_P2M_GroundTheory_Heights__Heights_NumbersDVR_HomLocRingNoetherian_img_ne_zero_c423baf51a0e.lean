-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_HomLocRingNoetherian_img_ne_zero_c423baf51a0e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T04:39:12.24778+00:00
-- url     : https://prove2.me/submissions/f766eaab-8305-4cd9-98a1-898132db15c1

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
omit [DecidableEq K]
namespace GroundTheory.Heights₂.Heights.NumbersDVR.HomLocRingNoetherian
theorem _root_.solution {W : Ideal (MRing ι R)} (hPW : P ≤ W) {t : MRing ι R} (ht : t ∉ W) :
    img P t ≠ 0 := fun h0 => ht (hPW (img_eq_zero_iff.mp h0))
end GroundTheory.Heights₂.Heights.NumbersDVR.HomLocRingNoetherian
