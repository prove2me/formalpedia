-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LVs.ub_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T11:47:22.739809+00:00
-- url     : https://prove2.me/submissions/7a169148-236c-429d-9b2d-5c2d5c47e443

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_SingToDiffAlt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_DpDual

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
open scoped ContDiff ComplexOrder
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open PositivityTheory.Rg.Sw
variable {n : ℕ}
namespace PositivityTheory.Rg.Sw.LVs
theorem _root_.solution (Z : M2 n) :
    Z.toBlocks₁₁ + Complex.I • Z.toBlocks₂₁ = (Lr n * Z : Matrix (Fin n) (Fin n ⊕ Fin n) ℂ) * Rc n := by
  conv_rhs => rw [← Matrix.fromBlocks_toBlocks Z]
  rw [Lr, Rc, Matrix.fromCols_mul_fromBlocks, Matrix.fromCols_mul_fromRows]
  simp
end PositivityTheory.Rg.Sw.LVs
