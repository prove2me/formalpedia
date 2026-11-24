-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_Objects_isModelOver_iff_82cd95b74825
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:43:42.094195+00:00
-- url     : https://prove2.me/submissions/0f45a464-b3f3-4bae-ad84-4ad45c04bff6

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_Objects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_MemOfMemSupportDivCycle
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_IsVerticalDivOfIsVerticalDivisorAlt
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_Objects_isMultiProjPrime_iff_a67b98d88a86

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
open GroundTheory.Heights₂.Heights.NumbersDVR.Objects
variable {K : Type*} [Fintype K] [DecidableEq K] {ι : K → Type*} [∀ k, Fintype (ι k)]
variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
omit [IsDomain O] [IsDiscreteValuationRing O]
namespace GroundTheory.Heights₂.Heights.NumbersDVR.Objects
theorem _root_.solution (P : Ideal (MRing ι O)) (d : ℕ) :
    IsModelOver P d ↔ GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.IsModelOver P d :=
  ⟨fun h => ⟨(isMultiProjPrime_iff P).mp h.multiProj, h.noTorsion, h.dim⟩,
    fun h => ⟨(isMultiProjPrime_iff P).mpr h.1, h.2.1, h.2.2⟩⟩
end GroundTheory.Heights₂.Heights.NumbersDVR.Objects
