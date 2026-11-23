-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LVs.CEq.symm_perm
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:47:15.989806+00:00
-- url     : https://prove2.me/submissions/cdcf3bcd-0ebf-4056-86bf-b2f7d65ea6ea

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_CayleyA
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_CayleyEq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open scoped ContDiff
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs PositivityTheory.Rg.Sw.LVs.CEq
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
omit [DecidableEq κ]
namespace PositivityTheory.Rg.Sw.LVs.CEq
theorem _root_.solution (F : Matrix κ κ ℂ → ℂ) (hF : AnalyticAt ℂ F 0) {n : ℕ} (v : Fin n → Matrix κ κ ℂ)
    (π : Equiv.Perm (Fin n)) : iteratedFDeriv ℂ n F 0 (v ∘ π) = iteratedFDeriv ℂ n F 0 v :=
  (hF.contDiffAt).iteratedFDeriv_comp_perm v π
end PositivityTheory.Rg.Sw.LVs.CEq
