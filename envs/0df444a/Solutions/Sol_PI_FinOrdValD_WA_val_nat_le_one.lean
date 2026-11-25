-- Prove2me | solution 1 for PI.FinOrdValD.WA.val_nat_le_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T09:39:59.316803+00:00
-- url     : https://prove2.me/submissions/9d116aa1-2e8a-4429-aeab-cd583a228ec1

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FiniteOrderValuation_WeakApprox

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum WithZero
open PI PI.FinOrdValD PI.FinOrdValD.WA
variable {L : Type*} [Field L] [NumberField L]
namespace PI.FinOrdValD.WA
theorem _root_.solution (v : HeightOneSpectrum (𝓞 L)) (m : ℕ) : v.valuation L (m : L) ≤ 1 := by
  have h := v.valuation_le_one (K := L) (m : 𝓞 L)
  simpa using h
end PI.FinOrdValD.WA
