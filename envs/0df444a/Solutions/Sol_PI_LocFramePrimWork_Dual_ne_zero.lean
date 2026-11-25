-- Prove2me | solution 1 for PI.LocFramePrimWork.Dual_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T09:57:04.69113+00:00
-- url     : https://prove2.me/submissions/1cc8acce-9cf3-4002-a991-ad3326cba900

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalPrimitiveFrame_StepsTop
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalPrimitiveFrame_DualFunctionalsExist

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.LocFramePrimWork
open NumberField IsDedekindDomain PI.LocFramePrim Module
open scoped TensorProduct
variable {E : Type} [Field E] [NumberField E] {n : ℕ}
namespace PI.LocFramePrimWork
theorem _root_.solution (Lb : Submodule (𝓞 E) (Fin n → E)) (z : Fin n → E)
    (hprim : ∀ c : E, c • z ∈ Lb → ∃ o : 𝓞 E, (o : E) = c) : z ≠ 0 := by
  intro hz
  obtain ⟨o, ho⟩ := hprim (algebraMap ℚ E (1 / 2)) (by rw [hz, smul_zero]; exact Lb.zero_mem)
  have hint : IsIntegral ℤ (algebraMap ℚ E (1 / 2)) := ho ▸ RingOfIntegers.isIntegral_coe o
  rw [isIntegral_algebraMap_iff (algebraMap ℚ E).injective] at hint
  obtain ⟨m, hm⟩ := IsIntegrallyClosed.isIntegral_iff.1 hint
  have h2 : ((2 * m : ℤ) : ℚ) = 1 := by
    push_cast
    rw [show (m : ℚ) = algebraMap ℤ ℚ m by simp, hm]
    norm_num
  have h2' : 2 * m = 1 := by exact_mod_cast h2
  omega
end PI.LocFramePrimWork
