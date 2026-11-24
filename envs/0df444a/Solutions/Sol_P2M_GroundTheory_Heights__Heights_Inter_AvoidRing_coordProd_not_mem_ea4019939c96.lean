-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_AvoidRing_coordProd_not_mem_ea4019939c96
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:56:46.180561+00:00
-- url     : https://prove2.me/submissions/c5a2f5f6-9fcb-4235-ae9c-d5a84710b6d2

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_IsIntersectionFamily
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_AvoidRing

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
set_option linter.unusedSectionVars false
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter GroundTheory.Heights₂.Heights.Inter.AvoidRing
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)] {R : Type*} [CommRing R]
namespace GroundTheory.Heights₂.Heights.Inter.AvoidRing
theorem _root_.solution {V : Ideal (MRingOver R ι)} (hV : V.IsPrime) (c : ∀ k, ι k)
    (hc : ∀ k, (X ⟨k, c k⟩ : MRingOver R ι) ∉ V) (d : K → ℕ) :
    (∏ k, (X ⟨k, c k⟩ : MRingOver R ι) ^ d k) ∉ V := by
  intro h
  obtain ⟨k, -, hk⟩ := (hV.prod_mem_iff).mp h
  exact hc k (hV.mem_of_pow_mem _ hk)
end GroundTheory.Heights₂.Heights.Inter.AvoidRing
