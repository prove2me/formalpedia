-- Prove2me | solution 1 for P2M_GlobalTheory_KSp_OpenCrit_blk___one_f3d920fac981
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T02:32:02.255401+00:00
-- url     : https://prove2.me/submissions/40682b56-7fc5-4f1f-ac36-d3457d03b8fd

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_UnipVal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PadicIsNonarchimedeanLocalField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_QuadExtTopologyStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsOpenSubgroupOfSiegelAndOppositeNhds

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary Filter Topology
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)
noncomputable section
open GlobalTheory GlobalTheory.KSp GlobalTheory.KSp.OpenCrit
variable {F : Type} [Field F] {E : Type} [Field E] [Algebra F E] (c : E →ₐ[F] E)
  {ν : Type} [Fintype ν] [DecidableEq ν]
variable [TopologicalSpace E] [IsTopologicalRing E] [ContinuousInv₀ E] [T2Space E]
namespace GlobalTheory.KSp.OpenCrit
theorem _root_.solution : (mat c (1 : UG c (stdJ ν E))).toBlocks₂₁ = 0 := by
  ext i j; simp [mat, toBlocks₂₁, one_apply]
end GlobalTheory.KSp.OpenCrit
