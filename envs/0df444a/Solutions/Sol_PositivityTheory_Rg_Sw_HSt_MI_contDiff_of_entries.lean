-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.HSt.MI.contDiff_of_entries
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:50:50.550738+00:00
-- url     : https://prove2.me/submissions/24895d16-07fd-4a03-9c50-1866c5adcf44

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
theorem _root_.solution {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : E → M2 n}
    (h : ∀ a b, ContDiff ℝ ∞ fun x => f x a b) : ContDiff ℝ ∞ f := by
  have : ContDiff ℝ ∞ (fun x => (f x : (Fin n ⊕ Fin n) → (Fin n ⊕ Fin n) → ℂ)) :=
    contDiff_pi.2 fun a => contDiff_pi.2 fun b => h a b
  exact this
end PositivityTheory.Rg.Sw.HSt.MI
