-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_RegularityRelativeClosedPoint_killBlocks_empty_f64bb506dbf9
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T05:53:19.624391+00:00
-- url     : https://prove2.me/submissions/d8d21f3d-fff2-4592-a7ef-daef52641ae7

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ImportsMoreExtra
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_NotIsUnitOfNumMem
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PHorizNotMem
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_CardLeRingKrullDim

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
open GroundTheory.Heights₂.Heights.Inter.RegularityRelativeClosedPoint
variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)] [DecidableEq K]
omit [Fintype K] [∀ k, Fintype (ι k)]
namespace GroundTheory.Heights₂.Heights.Inter.RegularityRelativeClosedPoint
theorem _root_.solution : (killBlocks ∅ : MRing ι →ₐ[ℤ] MRing ι) = AlgHom.id ℤ (MRing ι) :=
  MvPolynomial.algHom_ext fun p => by simp [killBlocks]
end GroundTheory.Heights₂.Heights.Inter.RegularityRelativeClosedPoint
