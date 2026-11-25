-- Prove2me | solution 1 for PI.KerTens.W.upd_part
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T09:48:45.789902+00:00
-- url     : https://prove2.me/submissions/24fd6601-9e2b-4765-bae7-6a498d1a570b

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
theorem _root_.solution {n : Type} {N N' : ℕ} (z : n → Fin N' → Fin N → ℂ) (b : Fin N' × Fin N) :
    upd z b (part z b) = z := by
  funext τ i j
  simp only [upd, part]
  split_ifs with h
  · subst h
    rfl
  · rfl
end PI.KerTens.W
