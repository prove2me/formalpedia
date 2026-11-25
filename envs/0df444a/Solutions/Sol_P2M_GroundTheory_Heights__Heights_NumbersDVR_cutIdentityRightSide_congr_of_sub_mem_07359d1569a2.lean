-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_cutIdentityRightSide_congr_of_sub_mem_07359d1569a2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T04:40:58.567683+00:00
-- url     : https://prove2.me/submissions/78437be3-5e83-4936-97ba-2f3a34c12e03

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_SpanTwoIsPrimeRelevant
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_BundleObjects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_CutIdentityRightSideCongrOfSubMem
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_divCycle_congr_of_sub_mem_56ff166eaee6

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
namespace GroundTheory.Heights₂.Heights.NumbersDVR
theorem _root_.solution {K : Type*} [DecidableEq K] {ι : K → Type*} {O : Type*} [CommRing O]
    [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O) (P : Ideal (MRing ι O)) (b : K → ℤ)
    (f g : MRing ι O) {s s' : MRing ι O} (h : s - s' ∈ P) {d : ℕ} (L : Fin d → K → ℤ) :
    cutIdentityRightSide ϖ P b f g s L = cutIdentityRightSide ϖ P b f g s' L := by
  unfold cutIdentityRightSide
  rw [divCycle_congr_of_sub_mem h]
end GroundTheory.Heights₂.Heights.NumbersDVR
