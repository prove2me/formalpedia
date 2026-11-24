-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Bridge_isMultiHomog_iff_c75df70a60fa
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:10:45.803805+00:00
-- url     : https://prove2.me/submissions/8f217422-baa2-41ed-8731-4779d4a5b29b

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_Objects
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_IsIntersectionFamily
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_IsMultiHomogIdealIff
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Bridge_weight_blockWeight_3721b3973afe

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Bridge
open MvPolynomial
noncomputable section
variable {K : Type*} {ι : K → Type*} {R : Type*} [CommRing R]
variable [DecidableEq K] [∀ k, Fintype (ι k)]
namespace GroundTheory.Heights₂.Heights.Bridge
theorem _root_.solution (f : NumbersDVR.MRing ι R) (a : K → ℕ) :
    NumbersDVR.IsMultiHomog f a ↔ ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog (R := R) f a := by
  unfold NumbersDVR.IsMultiHomog ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog IsWeightedHomogeneous
  simp only [weight_blockWeight, mem_support_iff, funext_iff]
end GroundTheory.Heights₂.Heights.Bridge
