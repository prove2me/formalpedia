-- Prove2me | solution 1 for P2M_GlobalTheory_LocFlat_PureColPf_typeFrame_val__94b5cad94009
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T11:12:18.011414+00:00
-- url     : https://prove2.me/submissions/5a54ef10-4377-43a0-9d2e-badbdb944873

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_ContrFactor
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_AllPositions
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_FlatColumnIndicatorPureAtSymmetricPosition

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
open GlobalTheory GlobalTheory.LocFlat GlobalTheory.LocFlat.PureColPf
variable {k : Type} [Field k] {n n' ι ι' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c c' : ℕ}
namespace GlobalTheory.LocFlat.PureColPf
theorem _root_.solution (ϖ : kˣ) (ord : ι ≃ n ⊕ Fin c) :
    (typeFrame ϖ ord).bas.val = diagonal (Sum.elim (fun _ => 1) fun i : Fin c => (ϖ : k) ^ (i.val + 1)) := by
  change fromBlocks 1 0 0 (diagonal _) = _
  rw [← fromBlocks_diagonal]; simp
end GlobalTheory.LocFlat.PureColPf
