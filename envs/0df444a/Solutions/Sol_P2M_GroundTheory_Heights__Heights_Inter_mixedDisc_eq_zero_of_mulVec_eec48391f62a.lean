-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_mixedDisc_eq_zero_of_mulVec_eec48391f62a
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T03:59:15.259882+00:00
-- url     : https://prove2.me/submissions/f37285ed-1591-4eb6-9b43-13e7de6636f0

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ImportsFurtherTail
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ExMapAlt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ExMap
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_TableDegreeThreeBase
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterSheet
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_MixedDiscEqZeroOfMulVec

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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open MvPolynomial Matrix Filter Topology ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4
namespace GroundTheory.Heights₂.Heights.Inter
theorem _root_.solution {D : ℕ} {A : Fin D → Matrix (Fin D) (Fin D) ℂ} {u : Fin D → ℂ} (hu : u ≠ 0)
    (hA : ∀ k, A k *ᵥ u = 0) : mixedDisc A = 0 := by
  unfold mixedDisc
  rw [Finset.sum_eq_zero, mul_zero]
  intro S _
  have hS : (∑ k ∈ S, A k) *ᵥ u = 0 :=
    Finset.sum_induction _ (fun M => M *ᵥ u = 0) (fun M N hM hN => by rw [add_mulVec, hM, hN, add_zero])
      (zero_mulVec u) fun k _ => hA k
  rw [Matrix.exists_mulVec_eq_zero_iff.mp ⟨u, hu, hS⟩, mul_zero]
end GroundTheory.Heights₂.Heights.Inter
