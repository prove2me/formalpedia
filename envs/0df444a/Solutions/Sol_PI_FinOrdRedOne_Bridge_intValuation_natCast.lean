-- Prove2me | solution 1 for PI.FinOrdRedOne.Bridge.intValuation_natCast
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T09:46:50.792146+00:00
-- url     : https://prove2.me/submissions/0c295853-e72c-4818-a1bb-51331d659b48

import Definitions.Def_Formalism_PeriodIntegrals_FinOrdRedOne
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FiniteOrderReduction_EqOneOfIsOfFinOrder
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FiniteOrderReduction_Bridge
import Theorems.Thm_PI_FinOrdRedOne_Bridge_natCast_not_mem_sq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.FinOrdRedOne PI.FinOrdRedOne.Bridge
open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum Ideal WithZero
variable {E : Type} [Field E] [NumberField E]
namespace PI.FinOrdRedOne.Bridge
theorem _root_.solution (p : ℕ) (hp : p.Prime) (hU : Unram E p)
    (P : HeightOneSpectrum (𝓞 E)) (hpP : (p : 𝓞 E) ∈ P.asIdeal) :
    P.intValuation (p : 𝓞 E) = exp (-1 : ℤ) := by
  have h1 := (P.intValuation_le_pow_iff_mem (p : 𝓞 E) 1).mpr (by rw [pow_one]; exact hpP)
  have h2 : ¬ P.intValuation (p : 𝓞 E) ≤ exp (-((2 : ℕ) : ℤ)) := fun h =>
    natCast_not_mem_sq p hp hU P hpP ((P.intValuation_le_pow_iff_mem (p : 𝓞 E) 2).mp h)
  have hx0 : P.intValuation (p : 𝓞 E) ≠ 0 := by
    intro h; apply h2; rw [h]; exact zero_le
  rw [← exp_log hx0] at h1 h2 ⊢
  rw [exp_le_exp] at h1 h2
  rw [exp_inj]
  push_cast at h1 h2
  omega
end PI.FinOrdRedOne.Bridge
