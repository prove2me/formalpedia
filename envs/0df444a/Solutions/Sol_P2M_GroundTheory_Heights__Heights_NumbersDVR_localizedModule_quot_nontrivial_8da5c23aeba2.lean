-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_localizedModule_quot_nontrivial_8da5c23aeba2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T04:42:57.040799+00:00
-- url     : https://prove2.me/submissions/f701a3f5-c32c-40d1-9e66-2eeb4c8e828d

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsLocalCoeffLocal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_MemDivSuppOfDivCycleNeZero
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PLocCyclePos

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
noncomputable section
universe u
namespace GroundTheory.Heights₂.Heights.NumbersDVR
theorem _root_.solution {R : Type u} [CommRing R] (J W : Ideal R) [W.IsPrime]
    (hJW : J ≤ W) : Nontrivial (LocalizedModule W.primeCompl (R ⧸ J)) := by
  refine ⟨⟨LocalizedModule.mk (1 : R ⧸ J) 1, 0, fun h => ?_⟩⟩
  rw [← LocalizedModule.zero_mk (1 : W.primeCompl), LocalizedModule.mk_eq] at h
  obtain ⟨v, hv⟩ := h
  have hv' : ((v : R) : R ⧸ J) = 0 := by
    simpa [Submonoid.smul_def, Algebra.smul_def] using hv
  exact v.2 (hJW (Ideal.Quotient.eq_zero_iff_mem.mp hv'))
end GroundTheory.Heights₂.Heights.NumbersDVR
