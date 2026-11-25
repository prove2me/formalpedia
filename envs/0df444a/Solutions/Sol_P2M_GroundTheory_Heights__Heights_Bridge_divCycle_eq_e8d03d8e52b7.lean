-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Bridge_divCycle_eq_e8d03d8e52b7
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T02:36:21.84213+00:00
-- url     : https://prove2.me/submissions/ea86e2a1-1af5-4edc-9144-84958c5e3e65

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_Objects
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_IsIntersectionFamily
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_IsMultiHomogIdealIff
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Bridge_isRelevant_iff_3762d4b164c8
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Bridge_multAt_eq_toNat_f8855e745589

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
theorem _root_.solution [Fintype K] [∀ k, Fintype (ι k)] [IsNoetherianRing R]
    (P : Ideal (NumbersDVR.MRing ι R)) (f : NumbersDVR.MRing ι R) (W : Ideal (NumbersDVR.MRing ι R)) :
    NumbersDVR.divCycle P f W = (ReciprocityTheory.ChartRestriction.G.Geo.divCycle (R := R) P f W : ℤ) := by
  classical
  unfold NumbersDVR.divCycle ReciprocityTheory.ChartRestriction.G.Geo.divCycle
  simp only [Finsupp.ofSupportFinite_coe, ReciprocityTheory.ChartRestriction.G.Geo.divSupp, Set.mem_ofPred_eq,
    ← isRelevant_iff]
  split_ifs with h
  · have : W.IsPrime := h.1.1.1
    rw [multAt_eq_toNat]
  · rfl
end GroundTheory.Heights₂.Heights.Bridge
