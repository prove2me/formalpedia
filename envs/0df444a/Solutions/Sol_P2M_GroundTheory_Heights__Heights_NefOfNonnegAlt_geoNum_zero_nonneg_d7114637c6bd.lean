-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NefOfNonnegAlt_geoNum_zero_nonneg_d7114637c6bd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T04:37:17.172535+00:00
-- url     : https://prove2.me/submissions/b4a300b8-45d6-49f2-aa4e-c854d1793b66

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsGrassHeight
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PNefOfNonneg

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
    (V : Ideal (MRing ι)) (a : Fin 0 → K → ℤ) : 0 ≤ geoNum 0 V a := by
  unfold geoNum
  split_ifs
  · exact Int.natCast_nonneg _
  · exact le_rfl
end GroundTheory.Heights₂.Heights.NefOfNonnegAlt
