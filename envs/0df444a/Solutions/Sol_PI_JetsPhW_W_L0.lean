-- Prove2me | solution 1 for PI.JetsPhW.W.L0
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:14:49.144416+00:00
-- url     : https://prove2.me/submissions/7e2cc98c-0b19-4e5f-90a9-22773ebfd7e7

import Definitions.Def_Formalism_PeriodIntegrals_JetsPhW
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_IntegralMv
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_CapelliComplements_FirstLemmaG
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_IntegralPolynomialFirst
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_CapelliComplements_FirstLemmaF
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_IntegralPolynomialThird
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_IntegralPolynomialFourth
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_UnitBall
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_IsIntegralNatCast
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_IntegralPolynomialFifth
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_IntegralPolynomialSixth
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_ImportsTerAlt
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_IntMvPderiv
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_IntegralPolynomialSecond
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_JetIntegrality_ExpLog
import Theorems.Thm_PI_JetsPhW_W_intMv_mul
import Theorems.Thm_PI_JetsPhW_W_intMv_pderiv
import Theorems.Thm_PI_JetsPhW_W_intMv_inv
import Theorems.Thm_PI_JetsPhW_W_pderiv_expMv
import Theorems.Thm_PI_JetsPhW_W_constantCoeff_expMv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Classical
open PI PI.JetsPhW PI.JetsPhW.W
open PI.JetsPhW MvPowerSeries
variable {p : ℕ} [Fact p.Prime] {σ : Type*}
namespace PI.JetsPhW.W
theorem _root_.solution {f c : MvPowerSeries σ ℂ_[p]} (i : σ) (hf : constantCoeff f = 0)
    (hE : IntegralMv (expMv f)) (hc : IntegralMv c) : IntegralMv (c * pderiv ℂ_[p] i f) := by
  obtain ⟨G, hG, hEG⟩ := intMv_inv hE (constantCoeff_expMv f)
  have : c * pderiv ℂ_[p] i f = c * pderiv ℂ_[p] i (expMv f) * G := by
    rw [pderiv_expMv hf, mul_assoc, mul_assoc, hEG, mul_one]
  rw [this]
  exact intMv_mul (intMv_mul hc (intMv_pderiv i hE)) hG
end PI.JetsPhW.W
