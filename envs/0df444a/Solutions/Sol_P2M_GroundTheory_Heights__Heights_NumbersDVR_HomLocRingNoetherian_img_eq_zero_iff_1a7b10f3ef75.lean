-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_HomLocRingNoetherian_img_eq_zero_iff_1a7b10f3ef75
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:51:37.905049+00:00
-- url     : https://prove2.me/submissions/d237d933-8a00-465b-bb4e-247c033b5878

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsHomLocRingLocal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PHomLocRingNoetherian

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
theorem _root_.solution {f : MRing ι R} : img P f = 0 ↔ f ∈ P := by
  simp [img, Ideal.Quotient.eq_zero_iff_mem]
end GroundTheory.Heights₂.Heights.NumbersDVR.HomLocRingNoetherian
