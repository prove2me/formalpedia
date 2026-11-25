-- Prove2me | solution 1 for PI.BeDiagZp.simeq_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:02:07.500633+00:00
-- url     : https://prove2.me/submissions/4f998164-35d1-43a9-a528-ac9d5b23e4bd

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DiagonalPadicSubstitution_SubstOps
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DiagonalPadicSubstitution_CoeffPowMulPowEqZeroOfLt
import Theorems.Thm_PI_BeDiagZp_expMv_add
import Theorems.Thm_PI_BeDiagZp_integral_mul

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
open PI PI.BeDiagZp
open MvPowerSeries
open IntegralPowerSeriesBall
variable {p : ℕ} [Fact p.Prime] {σ : Type*}
namespace PI.BeDiagZp
theorem _root_.solution {f g f' g' : MvPowerSeries σ ℂ_[p]} (h : Simeq f g) (h' : Simeq f' g') :
    Simeq (f + f') (g + g') := by
  have e : f + f' - (g + g') = (f - g) + (f' - g') := add_sub_add_comm f f' g g'
  refine ⟨by rw [e, map_add, h.1, h'.1, add_zero], ?_⟩
  rw [e, expMv_add h.1 h'.1]; exact integral_mul h.2 h'.2
end PI.BeDiagZp
