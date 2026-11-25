-- Prove2me | solution 1 for P2M_GlobalTheory_DegCnt_LiftS_q_X__232d051c03ce
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T08:13:03.308704+00:00
-- url     : https://prove2.me/submissions/773935a0-c9a7-419d-bf41-24b3fe20e922

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FlagPairDefinitePartLattice
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NormalFormDualOrthogonalLast
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermFramePairNormalFormGeometrySummaryStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermFramePairCommonUnipotentStabiliserSummary
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsIntegerAddStarEqOneOfIsCMUnram
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermFramePairNormalFormCongruenceLiftSmallGroup
import Theorems.Thm_GlobalTheory_DegCnt_LiftS_e_mem_Xa
import Theorems.Thm_GlobalTheory_DegCnt_LiftS_orth_X
import Theorems.Thm_GlobalTheory_DegCnt_LiftS_qI_apply
import Theorems.Thm_P2M_GlobalTheory_DegCnt_LiftS_e__eq_6ca77138a685
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_e_mem_Xa
import Theorems.Thm_GlobalTheory_UnipStab_orth_X


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical nonZeroDivisors
open GlobalTheory GlobalTheory.DegCnt GlobalTheory.DegCnt.LiftS
variable {K V : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V]
  {H : HermSpace K V} {r : ℕ} (N : NF H r)
namespace GlobalTheory.DegCnt.LiftS
theorem _root_.solution {y : V} (hy : y ∈ N.F'.X) : qI N y = 0 := by
  rw [qI_apply]
  refine Finset.sum_eq_zero (fun b hb => ?_)
  have hb' : N.j ≤ b.val := (Finset.mem_filter.1 hb).2
  have h1 : H.B y (N.F'.e b.castSucc) = 0 := orth_X N.F' hy (e_mem_Xa N.F' b b.2)
  rw [e'_eq N b hb', map_smulₛₗ] at h1
  have hc : starRingEnd K N.c ≠ 0 := by
    intro h
    have h2 := N.c_norm
    rw [← starRingEnd_apply, h, mul_zero] at h2
    exact zero_ne_one h2
  rw [smul_eq_mul] at h1
  rw [(mul_eq_zero.1 h1).resolve_left hc, zero_smul]
end GlobalTheory.DegCnt.LiftS
