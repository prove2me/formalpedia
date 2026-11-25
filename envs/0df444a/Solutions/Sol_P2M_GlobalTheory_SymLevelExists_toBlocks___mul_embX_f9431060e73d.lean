-- Prove2me | solution 1 for P2M_GlobalTheory_SymLevelExists_toBlocks___mul_embX_f9431060e73d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T02:34:24.160978+00:00
-- url     : https://prove2.me/submissions/5e2eaff4-96ab-4f6c-a059-de2a408dae58

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_FramePositiveSum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_UnipotentRadicalBasic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsIsSymmetricPositionLevel
import Theorems.Thm_GlobalTheory_RootEx_Radical_embX_val
import Theorems.Thm_P2M_GlobalTheory_RootEx_Radical_toBlocks___of_mem_fe0d9551bf6c


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix Topology GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum
noncomputable section
open GlobalTheory GlobalTheory.SymLevelExists
variable {F : Type} [Field F] {κ l : ℕ}
namespace GlobalTheory.SymLevelExists
theorem _root_.solution {p : ℕ} {u : GL (Fin κ ⊕ Fin l) F} (hu : u ∈ N F (Fin κ) l p) (γ : GL (Fin κ) F) :
    (u * embX l γ).val.toBlocks₁₁ = γ.val := by
  rw [Units.val_mul, Radical.embX_val]
  conv_lhs => rw [← Matrix.fromBlocks_toBlocks u.val]
  simp [fromBlocks_multiply, Radical.toBlocks₁₁_of_mem hu]
end GlobalTheory.SymLevelExists
