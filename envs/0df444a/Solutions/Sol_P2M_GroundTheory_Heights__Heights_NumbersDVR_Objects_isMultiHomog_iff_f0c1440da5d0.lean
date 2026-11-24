-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_Objects_isMultiHomog_iff_f0c1440da5d0
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:24:26.6772+00:00
-- url     : https://prove2.me/submissions/ebc76532-370b-4f2c-828f-6a4bdc689120

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_Objects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_MemOfMemSupportDivCycle
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_IsVerticalDivOfIsVerticalDivisorAlt
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_Objects_weight_blockWeight_apply_e42af7815746

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
variable {R : Type*} [CommRing R]
namespace GroundTheory.Heights₂.Heights.NumbersDVR.Objects
theorem _root_.solution (f : MRing ι R) (b : K → ℕ) :
    IsMultiHomog f b ↔ ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog f b := by
  constructor
  · intro h m hm k
    rw [← weight_blockWeight_apply, h (mem_support_iff.mp hm)]
  · intro h m hm
    funext k
    rw [weight_blockWeight_apply, h m (mem_support_iff.mpr hm) k]
end GroundTheory.Heights₂.Heights.NumbersDVR.Objects
