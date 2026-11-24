-- Prove2me | solution 1 for PI.KerTens.W.blk_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T21:34:08.789826+00:00
-- url     : https://prove2.me/submissions/6bbd585d-b47e-46ea-ad33-e5c99d43cc1f

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_KerTens
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TensorSpanning_MatHHOne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate
open PI PI.KerTens PI.KerTens.W
open Formalism.L2.Th1.H (Sesq matH alphaQ qOf opU Th fixedBy)
namespace PI.KerTens.W
theorem _root_.solution {n : Type} {N N' : ℕ} (b : Fin N' × Fin N) (x : n → ℂ) (τ : n) (i : Fin N') (j : Fin N) :
    blk b x τ i j = if (i, j) = b then x τ else 0 := rfl
end PI.KerTens.W
