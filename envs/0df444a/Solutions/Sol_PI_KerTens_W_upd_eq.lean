-- Prove2me | solution 1 for PI.KerTens.W.upd_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T09:48:42.558998+00:00
-- url     : https://prove2.me/submissions/40ef9e3e-2899-4616-9e93-ee3ad535d070

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
theorem _root_.solution {n : Type} {N N' : ℕ} (z : n → Fin N' → Fin N → ℂ) (b : Fin N' × Fin N) (t : n → ℂ) :
    upd z b t = (fun τ i j => if (i, j) = b then 0 else z τ i j) + blk b t := by
  funext τ i j
  simp only [upd, Pi.add_apply, blk_apply]
  split_ifs <;> simp
end PI.KerTens.W
