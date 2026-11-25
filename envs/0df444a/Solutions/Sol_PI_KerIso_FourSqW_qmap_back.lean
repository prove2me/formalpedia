-- Prove2me | solution 1 for PI.KerIso.FourSqW.qmap_back
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T09:47:33.537556+00:00
-- url     : https://prove2.me/submissions/5550529b-05e4-488e-9750-844302f66825

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_KerIso
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FourSquareQuaternions_FourSqOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FourSquareQuaternions_QuatMatTransposeMul
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FourSquareQuaternions_QmapInjective
import Theorems.Thm_PI_KerIso_FourSqW_qmap_apply
import Theorems.Thm_PI_KerFourSqW_sum_mul_cast


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators Matrix
open PI PI.KerIso PI.KerIso.FourSqW
open PI.KerFourSqW
namespace PI.KerIso.FourSqW
theorem _root_.solution {K E : Type*} [Field K] [CharZero K] [Field E] [Algebra K E] {n : Type*}
    (b : Module.Basis n K E) (Q : n → Matrix (Fin 4) (Fin 4) ℚ) (q : n → ℚ)
    (hQ : ∀ i, (Q i)ᵀ * Q i = q i • (1 : Matrix (Fin 4) (Fin 4) ℚ)) (x : Fin 4 → E) (a' : Fin 4) (i : n) :
    ∑ c, (Q i c a' : K) * qmap b Q x (c, i) = (q i : K) * b.repr (x a') i := by
  simp only [qmap_apply, Finset.mul_sum]
  rw [Finset.sum_comm]
  have h : ∀ a, ∑ c, (Q i c a' : K) * ((Q i c a : K) * b.repr (x a) i)
      = (∑ c, (Q i c a' : K) * (Q i c a : K)) * b.repr (x a) i := by
    intro a
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun c _ => ?_
    ring
  simp_rw [h, sum_mul_cast (Q i) (q i) (hQ i), ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
end PI.KerIso.FourSqW
