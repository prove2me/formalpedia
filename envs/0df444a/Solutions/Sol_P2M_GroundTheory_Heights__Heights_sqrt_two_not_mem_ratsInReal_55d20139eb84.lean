-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_sqrt_two_not_mem_ratsInReal_55d20139eb84
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:56:58.370578+00:00
-- url     : https://prove2.me/submissions/0415a8f1-a9ef-4980-9f78-445cd2898874

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Antisymmetric_StatementsGluing
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Antisymmetric_LocallyFreeSpreadHyp
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Antisymmetric_AddBlockPullbackOfChartBundlePullback

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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open ReciprocityTheory.ChartRestriction.G.Geo
open IndefiniteRowSideFullHecke.Antisym
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution : √2 ∉ ratsInReal := by
  rintro ⟨q, hq⟩
  exact irrational_sqrt_two ⟨q, hq⟩
end GroundTheory.Heights₂.Heights
