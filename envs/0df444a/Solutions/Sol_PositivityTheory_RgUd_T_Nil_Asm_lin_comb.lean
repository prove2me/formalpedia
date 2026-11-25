-- Prove2me | solution 1 for PositivityTheory.RgUd.T.Nil.Asm.lin_comb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T11:57:27.788674+00:00
-- url     : https://prove2.me/submissions/089eac16-d0e7-4963-993c-9af7c6109f3d

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
theorem _root_.solution (α β γ u0 v0 : ℂ) :
    C u0 * (X - C α) + C v0 * (C β - C γ * X) = C (u0 * (-α) + v0 * β) + C (u0 - v0 * γ) * X := by
  simp only [C_add, C_mul, C_neg, C_sub]
  ring
end PositivityTheory.RgUd.T.Nil.Asm
