-- Prove2me | solution 1 for PI.FinOrdRedOne.Bridge.natCast_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:00:29.792908+00:00
-- url     : https://prove2.me/submissions/e18f8435-7cf7-4a04-8c57-391a625997ef

import Definitions.Def_Formalism_PeriodIntegrals_FinOrdRedOne
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FiniteOrderReduction_EqOneOfIsOfFinOrder
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FiniteOrderReduction_Bridge
import Theorems.Thm_PI_FinOrdRedOne_Bridge_valued_natCast

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
    ((p : ℕ) : OP E P) ≠ 0 := by
  intro h
  have h1 := valued_natCast p hp hU P hpP
  have h2 := congrArg (fun z : OP E P => (z : P.adicCompletion E)) h
  push_cast at h2
  rw [h2, map_zero] at h1
  exact exp_ne_zero h1.symm
end PI.FinOrdRedOne.Bridge
