-- Prove2me | solution 1 for P2M_PI_PowBddIntWork_eval__int_map_eq_zero_9ea7a06fc8b4
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T08:47:46.958856+00:00
-- url     : https://prove2.me/submissions/29a04f0c-e3e1-4d2b-947d-a324aa9e1ff3

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PowerBoundedIntegrality_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PowerBoundedIntegrality_EvalIntMapEqZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.PowBddIntWork
open Matrix Polynomial
namespace PI.PowBddIntWork
theorem _root_.solution {A B : Type*} [Ring A] [Ring B] (ψ : A →+* B) (p : ℤ[X]) (a : A)
    (h : p.eval₂ (algebraMap ℤ A) a = 0) : p.eval₂ (algebraMap ℤ B) (ψ a) = 0 := by
  have e : ψ.comp (algebraMap ℤ A) = algebraMap ℤ B := RingHom.ext_int _ _
  rw [← e, ← Polynomial.hom_eval₂, h, map_zero]
end PI.PowBddIntWork
