-- Prove2me | solution 1 for PositivityTheory.ThK.LinAct.schr_comm
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:05:46.728468+00:00
-- url     : https://prove2.me/submissions/d2b3863f-028d-4965-81a7-a61ea3cfb7e1

import Definitions.Def_Development_WeilBound_CoreStatements_LocalThetaKernels_EvlLoc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsLocallyConstantAddChar
import Definitions.Def_Development_WeilBound_CoreStatements_CompactAveragingSplitting_EigenvectorLifting_LinearActInt
import Theorems.Thm_PositivityTheory_ThKH_Evl_schr_schr


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix GlobalTheory.WeilM MeasureTheory ValuativeRel Topology Filter PositivityTheory.ThKH.Evl
open PositivityTheory PositivityTheory.ThK PositivityTheory.ThK.LinAct
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [Invertible (2 : k)]
  {κ ι : Type} [Fintype κ] [Fintype ι] {ψ : AddChar k ℂ}
omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
namespace PositivityTheory.ThK.LinAct
theorem _root_.solution (w w' : (κ → k) × (κ → k)) (φ : (κ → k) → ℂ) :
    schr ψ w (schr ψ w' φ) = ψ (w.1 ⬝ᵥ w'.2 - w'.1 ⬝ᵥ w.2) • schr ψ w' (schr ψ w φ) := by
  rw [schr_schr, schr_schr, smul_smul, ← AddChar.map_add_eq_mul, add_comm w]
  congr 2
  have h2 : ⅟(2 : k) * 2 = 1 := invOf_mul_self _
  linear_combination (w.1 ⬝ᵥ w'.2 - w'.1 ⬝ᵥ w.2) * h2
end PositivityTheory.ThK.LinAct
