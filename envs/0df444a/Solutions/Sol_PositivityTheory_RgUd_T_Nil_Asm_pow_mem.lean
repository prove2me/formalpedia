-- Prove2me | solution 1 for PositivityTheory.RgUd.T.Nil.Asm.pow_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:54:50.776483+00:00
-- url     : https://prove2.me/submissions/7c66b7c8-2c66-4824-b92d-7c446ee064ff

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_UnitaryDualProof_CompactOrbits_NilpotentOrbits_NilpotentHypotheses_AevalProdLinearFactors

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Polynomial
open PositivityTheory PositivityTheory.RgUd PositivityTheory.RgUd.T PositivityTheory.RgUd.T.Nil PositivityTheory.RgUd.T.Nil.Asm
variable {M : Type*} [AddCommGroup M] [Module ℂ M]
namespace PositivityTheory.RgUd.T.Nil.Asm
theorem _root_.solution (K : Submodule ℂ M) (R : Module.End ℂ M) (hK : ∀ m ∈ K, R m ∈ K) :
    ∀ (j : ℕ), ∀ m ∈ K, (R ^ j) m ∈ K := by
  intro j
  induction j with
  | zero => intro m hm; simpa using hm
  | succ j ih => intro m hm; rw [pow_succ', Module.End.mul_apply]; exact hK _ (ih m hm)
end PositivityTheory.RgUd.T.Nil.Asm
