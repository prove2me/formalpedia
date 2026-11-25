-- Prove2me | solution 1 for PositivityTheory.SiegelWeilFormula.KLI.gramX_tr_g
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T11:57:22.555803+00:00
-- url     : https://prove2.me/submissions/bc04e95a-b580-4578-9e02-849e9eda673d

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_NullSec
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_SiegelWeilFormula_LocalOperatorBlocks_GaussSec

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Matrix PositivityTheory.Rg.Sw
open scoped Matrix ComplexConjugate
open PositivityTheory PositivityTheory.SiegelWeilFormula PositivityTheory.SiegelWeilFormula.KLI
variable {m n : ℕ}
namespace PositivityTheory.SiegelWeilFormula.KLI
theorem _root_.solution (x : Fin m → Fin n → ℂ) (j i : Fin n) :
    gramX (fun _ : Fin m => true) x j i = ∑ a, star (x a j) * x a i := by
  simp [PositivityTheory.Rg.Sw.gramX, PositivityTheory.Rg.Sw.evX, PositivityTheory.Rg.Sw.Qp,
    PositivityTheory.Rg.Sw.Qb]
end PositivityTheory.SiegelWeilFormula.KLI
