-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_RegularityDivisorSupportClosed_le_of_height_map_eq_zero_c6898706a633
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T03:56:47.97097+00:00
-- url     : https://prove2.me/submissions/c84382ff-a7e2-4062-b150-a30bee8df604

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ImportsTerMore
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterDivSupp
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_LeOfHeightMapEqZero

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
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
noncomputable section
namespace GroundTheory.Heights₂.Heights.Inter
namespace RegularityDivisorSupportClosed
theorem _root_.solution {A : Type*} [CommRing A] {P Q : Ideal A} [P.IsPrime]
    (h : (Q.map (Ideal.Quotient.mk P)).height = 0) : Q ≤ P := by
  intro x hx
  rw [Ideal.height_eq_zero_iff_eq_bot] at h
  have : Ideal.Quotient.mk P x ∈ Q.map (Ideal.Quotient.mk P) := Ideal.mem_map_of_mem _ hx
  rwa [h, Ideal.mem_bot, Ideal.Quotient.eq_zero_iff_mem] at this
end RegularityDivisorSupportClosed
end GroundTheory.Heights₂.Heights.Inter
