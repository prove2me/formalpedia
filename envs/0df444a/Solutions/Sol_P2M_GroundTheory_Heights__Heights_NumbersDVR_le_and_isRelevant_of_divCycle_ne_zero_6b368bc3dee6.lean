-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_le_and_isRelevant_of_divCycle_ne_zero_6b368bc3dee6
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:56:46.207295+00:00
-- url     : https://prove2.me/submissions/1ef54ce9-cd69-4fc4-a48b-7c9225c78867

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_Objects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_Cartier

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
variable {K : Type*} {ι : K → Type*} {R : Type*} [CommRing R]
namespace GroundTheory.Heights₂.Heights.NumbersDVR
theorem _root_.solution {P : Ideal (MRing ι R)} {f : MRing ι R}
    {W : Ideal (MRing ι R)} (h : divCycle P f W ≠ 0) : W.IsPrime ∧ P ≤ W ∧ IsRelevant W := by
  unfold divCycle at h
  split_ifs at h with hW
  · exact ⟨hW.1.1.1, le_sup_left.trans hW.1.1.2, hW.2⟩
  · exact absurd rfl h
end GroundTheory.Heights₂.Heights.NumbersDVR
