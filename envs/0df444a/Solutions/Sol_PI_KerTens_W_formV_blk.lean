-- Prove2me | solution 1 for PI.KerTens.W.formV_blk
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T09:47:41.497358+00:00
-- url     : https://prove2.me/submissions/533bcf1b-e1f9-45d4-8895-a7df3d5bc78f

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
theorem _root_.solution (A : ℝ) {n : Type} [Fintype n] {N N' : ℕ} (w : n → Fin N' → Fin N → ℂ)
    (b : Fin N' × Fin N) (x : n → ℂ) :
    formV A n N N' w (blk b x) = (∑ τ, w τ b.1 b.2 * conj (x τ)) / (A : ℂ) := by
  simp only [formV, LinearMap.mk₂'ₛₗ_apply, blk_apply, Prod.ext_iff, ite_and]
  congr 1
  refine Finset.sum_congr rfl fun τ _ => ?_
  simp [apply_ite (starRingEnd ℂ), mul_ite, Finset.sum_ite_eq']
end PI.KerTens.W
