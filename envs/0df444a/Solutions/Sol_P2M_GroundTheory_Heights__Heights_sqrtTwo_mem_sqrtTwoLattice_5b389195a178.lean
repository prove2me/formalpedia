-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_sqrtTwo_mem_sqrtTwoLattice_5b389195a178
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T08:40:48.66291+00:00
-- url     : https://prove2.me/submissions/72808f80-f12a-4902-ba26-e4218a4e6478

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
theorem _root_.solution : √2 ∈ sqrtTwoLattice :=
  Submodule.subset_span ⟨1, rfl⟩
end GroundTheory.Heights₂.Heights
