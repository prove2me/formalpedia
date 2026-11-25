-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_RegularityRelativeClosedPoint_le_comap_killBlocks_6f4593612eea
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T08:15:45.536823+00:00
-- url     : https://prove2.me/submissions/3cb9a63c-4349-4364-81c3-03a7f25cebaa

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ImportsMoreExtra
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_NotIsUnitOfNumMem
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PHorizNotMem
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_CardLeRingKrullDim
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_RegularityRelativeClosedPoint_killBlocks_form_97a235c0fcde

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
namespace GroundTheory.Heights₂.Heights.Inter.RegularityRelativeClosedPoint
theorem _root_.solution (S : Finset K) {W : Ideal (MRing ι)} (hW : IsMultiHomogIdeal W) :
    W ≤ W.comap (killBlocks S) := by
  obtain ⟨T, hT, rfl⟩ := hW
  rw [Ideal.span_le]
  intro g hg
  obtain ⟨a, ha⟩ := hT g hg
  rw [SetLike.mem_coe, Ideal.mem_comap, killBlocks_form S ha]
  exact Ideal.mul_mem_left _ _ (Ideal.subset_span hg)
end GroundTheory.Heights₂.Heights.Inter.RegularityRelativeClosedPoint
