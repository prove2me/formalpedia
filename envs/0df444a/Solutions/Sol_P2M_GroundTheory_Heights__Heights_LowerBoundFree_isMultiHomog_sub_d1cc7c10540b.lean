-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_LowerBoundFree_isMultiHomog_sub_d1cc7c10540b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T04:04:21.958003+00:00
-- url     : https://prove2.me/submissions/36852f97-9d9f-442d-b764-3b8d1b28b7ee

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HodgeLowerBound_CoordinateIdeals_MemMCoordIdealOfAevalEqZero
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HodgeLowerBound_FrameDefinitions_Metric
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LowerBoundFree_isMultiHomog_add_95ee52bfb1b9


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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
variable {Ω : Type} [Field Ω]
omit [Fintype K]
namespace GroundTheory.Heights₂.Heights.LowerBoundFree
theorem _root_.solution {g h : MRing ι} {d : K → ℕ} (hg : IsMultiHomog g d)
    (hh : IsMultiHomog h d) : IsMultiHomog (g - h) d := by
  rw [sub_eq_add_neg]
  refine isMultiHomog_add hg ?_
  intro m hm
  exact hh m (by simpa using hm)
end GroundTheory.Heights₂.Heights.LowerBoundFree
