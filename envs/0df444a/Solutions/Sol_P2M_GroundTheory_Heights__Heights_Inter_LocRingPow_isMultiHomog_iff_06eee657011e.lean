-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_LocRingPow_isMultiHomog_iff_06eee657011e
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:23:11.843193+00:00
-- url     : https://prove2.me/submissions/a6a6877e-ec23-4764-9387-f4b3950b785a

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StLocRingPow
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_AvoidRing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterDivSupp
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PLocRingPow
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_LocRingPow_weight_multiDegWeight_ca852a704747

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.Inter.AvoidRing
noncomputable section
open GroundTheory.Heights₂.Heights.Inter.LocRingPow
variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]
namespace GroundTheory.Heights₂.Heights.Inter.LocRingPow
theorem _root_.solution {f : MRing ι} {a : K → ℕ} :
    IsMultiHomog f a ↔ IsWeightedHomogeneous (multiDegWeight ι) f a := by
  constructor
  · intro h d hd
    rw [weight_multiDegWeight]
    funext k
    exact h d (mem_support_iff.mpr hd) k
  · intro h m hm k
    have := h (mem_support_iff.mp hm)
    rw [weight_multiDegWeight] at this
    exact congrFun this k
end GroundTheory.Heights₂.Heights.Inter.LocRingPow
