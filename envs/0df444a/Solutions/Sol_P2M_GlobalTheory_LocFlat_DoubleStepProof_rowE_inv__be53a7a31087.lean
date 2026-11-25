-- Prove2me | solution 1 for P2M_GlobalTheory_LocFlat_DoubleStepProof_rowE_inv__be53a7a31087
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T11:30:44.034791+00:00
-- url     : https://prove2.me/submissions/d9221ccb-d920-41c8-87c0-c736649f6b30

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_ContrFactor
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_AllPositions
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PadicIsNonarchimedeanLocalField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_FlatRowMapEqRootExchangeOperatorTranslateStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_SymLevelDoubleStepOfFlatColumnFlatRow

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain
noncomputable section
noncomputable section
open GlobalTheory GlobalTheory.LocFlat GlobalTheory.LocFlat.DoubleStepProof
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
namespace GlobalTheory.LocFlat.DoubleStepProof
theorem _root_.solution {n : Type} [Fintype n] [DecidableEq n] (c p : ℕ) (u : n → k) :
    (rowE c p u)⁻¹ = rowE c p (-u) := by
  ext1
  change fromBlocks 1 0 (-(Matrix.of fun (l : Fin c) (s : n) => if l.val + 1 = p then u s else 0)) 1 =
    fromBlocks 1 0 (Matrix.of fun (l : Fin c) (s : n) => if l.val + 1 = p then (-u) s else 0) 1
  congr 1
  ext l s
  simp only [Matrix.neg_apply, Matrix.of_apply, Pi.neg_apply]
  split_ifs <;> simp
end GlobalTheory.LocFlat.DoubleStepProof
