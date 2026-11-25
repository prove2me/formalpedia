-- Prove2me | solution 1 for PI.KerTens.W.tens_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T09:48:37.699024+00:00
-- url     : https://prove2.me/submissions/245cfbde-ecd0-4594-b9dd-fb4ef65ca2dd

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_KerTens
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TensorSpanning_MatHHOne
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TensorSpanning_TensSpans

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
theorem _root_.solution {n : Type} (θ : (n → ℂ) → ℂ) (N N' : ℕ) (z : n → Fin N' → Fin N → ℂ) :
    tensPow θ N N' z = ∏ b : Fin N' × Fin N, θ (part z b) := by
  rw [tensPow, Fintype.prod_prod_type]
  rfl
end PI.KerTens.W
