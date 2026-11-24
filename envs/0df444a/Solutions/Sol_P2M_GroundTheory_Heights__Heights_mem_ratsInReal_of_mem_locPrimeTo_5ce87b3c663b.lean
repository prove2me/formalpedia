-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_mem_ratsInReal_of_mem_locPrimeTo_5ce87b3c663b
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:04:40.872103+00:00
-- url     : https://prove2.me/submissions/8307b98c-3fa3-45e1-9474-68cfa4be7bf2

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
theorem _root_.solution {u : ℝ} (hu : u ∈ locPrimeTo chartOne 2) :
    u ∈ ratsInReal := by
  have hA : chartOne ≤ subalgebraOfSubring ratsInReal.toSubring :=
    Algebra.adjoin_le (by
      rintro _ ⟨_, rfl⟩
      exact mem_subalgebraOfSubring.2 (by simp [one_mem]))
  have hB : locPrimeTo chartOne 2 ≤ subalgebraOfSubring ratsInReal.toSubring := by
    refine Algebra.adjoin_le (Set.union_subset hA ?_)
    rintro _ ⟨s, -, rfl⟩
    exact mem_subalgebraOfSubring.2 (ratsInReal.inv_mem (natCast_mem ratsInReal s))
  exact mem_subalgebraOfSubring.1 (hB hu)
end GroundTheory.Heights₂.Heights
