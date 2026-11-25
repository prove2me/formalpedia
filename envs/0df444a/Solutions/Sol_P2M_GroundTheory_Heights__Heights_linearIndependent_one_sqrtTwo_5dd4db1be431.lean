-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_linearIndependent_one_sqrtTwo_5dd4db1be431
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T09:00:02.050997+00:00
-- url     : https://prove2.me/submissions/5b5f3e53-2d26-4c51-9bc2-51c7f4a45ab8

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Antisymmetric_StatementsGluing
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Antisymmetric_LocallyFreeSpreadHyp
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Antisymmetric_AddBlockPullbackOfChartBundlePullback
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_sqrt_two_not_mem_ratsInReal_55d20139eb84
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_mem_ratsInReal_of_mem_zTwo_cb3a3a6f0d2e

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
theorem _root_.solution : LinearIndependent zTwo ![(1 : ℝ), √2] := by
  refine LinearIndependent.pair_iffₛ.2 fun s t s' t' h => ?_
  simp only [Subring.smul_def, smul_eq_mul, mul_one] at h
  have hs := mem_ratsInReal_of_mem_zTwo (s - s').2
  have ht := mem_ratsInReal_of_mem_zTwo (t - t').2
  push_cast at hs ht
  by_cases htt : (t : ℝ) - t' = 0
  · refine ⟨Subtype.ext ?_, Subtype.ext (by linarith)⟩
    have : (t : ℝ) = t' := by linarith
    rw [this] at h
    linarith
  · exfalso
    apply sqrt_two_not_mem_ratsInReal
    have : √2 = ((s' : ℝ) - s) / ((t : ℝ) - t') := by
      field_simp
      linarith
    rw [this]
    exact div_mem (by simpa using neg_mem hs) ht
end GroundTheory.Heights₂.Heights
