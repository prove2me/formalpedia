-- Prove2me | solution 1 for PI.FinOrdRedOne.Bridge.valued_natCast
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T09:53:36.244194+00:00
-- url     : https://prove2.me/submissions/224ed811-8ed4-43e7-961b-900535f96c6e

import Definitions.Def_Formalism_PeriodIntegrals_FinOrdRedOne
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FiniteOrderReduction_EqOneOfIsOfFinOrder
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FiniteOrderReduction_Bridge
import Theorems.Thm_PI_FinOrdRedOne_Bridge_intValuation_natCast

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
    Valued.v ((p : ℕ) : P.adicCompletion E) = exp (-1 : ℤ) := by
  have h1 := P.valuedAdicCompletion_eq_valuation (K := E) ((p : ℕ) : 𝓞 E)
  rw [valuation_of_algebraMap, intValuation_natCast p hp hU P hpP] at h1
  simp only [map_natCast] at h1
  exact h1
end PI.FinOrdRedOne.Bridge
