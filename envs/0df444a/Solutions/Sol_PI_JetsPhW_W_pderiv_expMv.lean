-- Prove2me | solution 1 for PI.JetsPhW.W.pderiv_expMv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:08:24.502488+00:00
-- url     : https://prove2.me/submissions/9811abf6-0bc2-4251-86cd-34d301b1628d

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
import Theorems.Thm_PI_JetsPhW_W_coeff_expMv_eq_expT
import Theorems.Thm_PI_JetsPhW_W_pderiv_expT

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
theorem _root_.solution {f : MvPowerSeries σ ℂ_[p]} (hf : constantCoeff f = 0) (i : σ) :
    pderiv ℂ_[p] i (expMv f) = pderiv ℂ_[p] i f * expMv f := by
  ext α
  have h1 : coeff α (pderiv ℂ_[p] i (expMv f)) =
      coeff α (pderiv ℂ_[p] i (expT f (Finsupp.degree α + 1 + 1))) := by
    rw [coeff_pderiv, coeff_pderiv, coeff_expMv_eq_expT hf]
    rw [map_add, Finsupp.degree_single]; omega
  rw [h1, pderiv_expT, coeff_mul, coeff_mul]
  refine Finset.sum_congr rfl fun x hx => ?_
  congr 1
  refine (coeff_expMv_eq_expT hf ?_).symm
  have := congrArg Finsupp.degree (Finset.HasAntidiagonal.mem_antidiagonal.1 hx)
  rw [map_add] at this; omega
end PI.JetsPhW.W
