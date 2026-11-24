-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Bridge_multAt_eq_toNat_f8855e745589
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:55:56.701578+00:00
-- url     : https://prove2.me/submissions/c84e2087-8b82-4cf4-ac07-8a542307941d

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_Objects
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_IsIntersectionFamily
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_IsMultiHomogIdealIff

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
namespace GroundTheory.Heights₂.Heights.Bridge
theorem _root_.solution (J W : Ideal (NumbersDVR.MRing ι R)) [W.IsPrime] :
    ReciprocityTheory.ChartRestriction.G.Geo.multAt (R := R) J W = (NumbersDVR.multAt J W).toNat := by
  unfold ReciprocityTheory.ChartRestriction.G.Geo.multAt NumbersDVR.multAt
  rw [dif_pos ‹W.IsPrime›]
end GroundTheory.Heights₂.Heights.Bridge
