-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.HSt.MI.contDiff_entry
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:04:53.4408+00:00
-- url     : https://prove2.me/submissions/d7d6394c-9076-43dc-9bd0-3147ca8b596f

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_IILeft
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_CayleyCosetSums_MatInv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Set Filter Topology
open scoped ContDiff
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.HSt PositivityTheory.Rg.Sw.HSt.MI
open PositivityTheory.Rg.Sw
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ}
namespace PositivityTheory.Rg.Sw.HSt.MI
theorem _root_.solution (a b : Fin n ⊕ Fin n) : ContDiff ℝ ∞ (fun x : M2 n => x a b) := by
  have h1 : ContDiff ℝ ∞ (fun x : (Fin n ⊕ Fin n) → (Fin n ⊕ Fin n) → ℂ => x a) := contDiff_apply ℝ _ a
  have h2 : ContDiff ℝ ∞ (fun y : (Fin n ⊕ Fin n) → ℂ => y b) := contDiff_apply ℝ ℂ b
  exact h2.comp h1
end PositivityTheory.Rg.Sw.HSt.MI
