-- Prove2me | solution 1 for P2M_GlobalTheory_TwistVertex_toBlocks___eq_one_7440c14eaaa2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T02:33:52.525083+00:00
-- url     : https://prove2.me/submissions/7d25406f-218c-4c9b-9eb7-81ea6f66493d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_FramePositiveSum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_FirstVertexParahoricLevelChainTwist

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
open GlobalTheory GlobalTheory.TwistVertex
variable {k : Type*} [Field k] {n : Type*} [Fintype n] [DecidableEq n] {c p : ℕ}
namespace GlobalTheory.TwistVertex
theorem _root_.solution {u : GL (n ⊕ Fin c) k} (hu : u ∈ N k n c p) : u.val.toBlocks₁₁ = 1 := by
  ext i j
  have := RootEx.Model.mem_N_iff.1 hu (.inl i) (.inl j) le_rfl
  simpa [toBlocks₁₁, Matrix.one_apply] using this
end GlobalTheory.TwistVertex
