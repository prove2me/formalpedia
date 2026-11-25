-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_mem_ratsInReal_of_mem_zTwo_cb3a3a6f0d2e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T08:43:34.235323+00:00
-- url     : https://prove2.me/submissions/231df8d4-9f4a-4771-829b-05bca93c5422

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Antisymmetric_StatementsGluing
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Antisymmetric_LocallyFreeSpreadHyp
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Antisymmetric_AddBlockPullbackOfChartBundlePullback
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_locAtIntPrime_eq_locPrimeTo_4bb9be37f9c6
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_mem_ratsInReal_of_mem_locPrimeTo_5ce87b3c663b

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
theorem _root_.solution {u : ℝ} (hu : u ∈ zTwo) : u ∈ ratsInReal := by
  rw [zTwo, locAtIntPrime_eq_locPrimeTo] at hu
  exact mem_ratsInReal_of_mem_locPrimeTo hu
end GroundTheory.Heights₂.Heights
