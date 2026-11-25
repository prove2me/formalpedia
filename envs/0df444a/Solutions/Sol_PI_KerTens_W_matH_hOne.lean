-- Prove2me | solution 1 for PI.KerTens.W.matH_hOne
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T09:50:42.146407+00:00
-- url     : https://prove2.me/submissions/c5aaf5f8-5776-4558-9ccc-05c1b04b8d22

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
theorem _root_.solution (L : PeriodPair) {n : Type} [Fintype n] [DecidableEq n] (t x : n → ℂ) :
    matH (hOne L n) t x = (∑ τ, t τ * conj (x τ)) / ((Formalism.L2.Th1.F.area L : ℝ) : ℂ) := by
  unfold matH hOne
  simp only [LinearMap.mk₂'ₛₗ_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul, mul_ite,
    mul_one, mul_zero, ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl fun τ _ => ?_
  ring
end PI.KerTens.W
