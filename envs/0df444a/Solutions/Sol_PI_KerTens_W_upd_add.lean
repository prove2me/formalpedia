-- Prove2me | solution 1 for PI.KerTens.W.upd_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T09:48:39.848039+00:00
-- url     : https://prove2.me/submissions/b7ed7140-a443-4e22-a6bf-2a83845f6a50

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_KerTens
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TensorSpanning_MatHHOne
import Theorems.Thm_PI_KerTens_W_blk_apply

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
theorem _root_.solution {n : Type} {N N' : ℕ} (z : n → Fin N' → Fin N → ℂ) (b : Fin N' × Fin N) (t x : n → ℂ) :
    upd z b t + blk b x = upd z b (t + x) := by
  funext τ i j
  simp only [upd, Pi.add_apply, blk_apply]
  split_ifs <;> simp
end PI.KerTens.W
