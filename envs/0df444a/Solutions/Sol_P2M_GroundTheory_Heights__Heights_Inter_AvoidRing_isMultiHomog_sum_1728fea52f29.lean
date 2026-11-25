-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_AvoidRing_isMultiHomog_sum_1728fea52f29
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T04:13:56.018714+00:00
-- url     : https://prove2.me/submissions/d526b5dd-a905-4939-8b80-9d565c7c2045

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
theorem _root_.solution {β : Type*} (s : Finset β) (f : β → MRingOver R ι) {a : K → ℕ}
    (h : ∀ b ∈ s, IsMultiHomog (f b) a) : IsMultiHomog (∑ b ∈ s, f b) a := by
  classical
  intro m hm k
  obtain ⟨b, hb, hmb⟩ := Finset.mem_biUnion.mp (MvPolynomial.support_sum hm)
  exact h b hb m hmb k
end GroundTheory.Heights₂.Heights.Inter.AvoidRing
