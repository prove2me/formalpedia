-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NefOfNonnegAlt_geoNum_one_nonneg_729cfb3b0c67
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T05:21:59.647702+00:00
-- url     : https://prove2.me/submissions/99596f02-8be9-4caf-8c60-608645f14d25

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsGrassHeight
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PNefOfNonneg
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NefOfNonnegAlt_geoNum_zero_nonneg_d7114637c6bd

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open ReciprocityTheory.ChartRestriction.G.Geo
open GroundTheory.Heights₂.Heights.NefOfNonnegAlt
namespace GroundTheory.Heights₂.Heights.NefOfNonnegAlt
theorem _root_.solution {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]
    (V : Ideal (MRing ι)) (a : K → ℤ) (ha : ∀ k, 0 ≤ a k) : 0 ≤ geoNum 1 V (fun _ => a) := by
  unfold geoNum
  split_ifs
  · refine Finset.sum_nonneg fun k _ => mul_nonneg (ha k) ?_
    refine finsum_nonneg fun W => finsum_nonneg fun _ => ?_
    exact mul_nonneg (Int.natCast_nonneg _) (geoNum_zero_nonneg _ _)
  · exact le_rfl
end GroundTheory.Heights₂.Heights.NefOfNonnegAlt
