-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_Objects_divO_eq_ratDiv_c8baeb4d1a16
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:28:01.119818+00:00
-- url     : https://prove2.me/submissions/ee57e888-e2e2-4306-b8c1-8c8bf0907275

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_Objects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_MemOfMemSupportDivCycle
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_IsVerticalDivOfIsVerticalDivisorAlt
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_Objects_intCyc_divCycle_0b46b449395b

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
namespace GroundTheory.Heights₂.Heights.NumbersDVR.Objects
theorem _root_.solution (P : Ideal (MRing ι O)) (f g : MRing ι O) (W : Ideal (MRing ι O)) :
    GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.divO P f g W = ratDiv P f g W := by
  rw [GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.divO, Finsupp.sub_apply, intCyc_divCycle,
    intCyc_divCycle, ratDiv]
end GroundTheory.Heights₂.Heights.NumbersDVR.Objects
