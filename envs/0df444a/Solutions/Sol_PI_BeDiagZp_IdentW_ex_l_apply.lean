-- Prove2me | solution 1 for PI.BeDiagZp.IdentW.ex_l_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T09:45:06.114318+00:00
-- url     : https://prove2.me/submissions/2e16ead2-6b4c-47d3-9250-991973c9b65b

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DiagonalPadicSubstitution_SubstOps
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DiagonalPadicSubstitution_CoeffOneLNeZero
import Theorems.Thm_PI_BeDiagZp_IdentW_constantCoeff_l
import Theorems.Thm_PI_BeDiagZp_IdentW_subst_l_ex

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
open PI PI.BeDiagZp PI.BeDiagZp.IdentW
variable {p : ℕ} [Fact p.Prime]
namespace PI.BeDiagZp.IdentW
theorem _root_.solution {σ : Type} {l ex : PowerSeries ℂ_[p]} (hex0 : PowerSeries.constantCoeff ex = 0)
    (h : PowerSeries.subst ex l = PowerSeries.X) (y : MvPowerSeries σ ℂ_[p])
    (hy : MvPowerSeries.constantCoeff y = 0) :
    PowerSeries.subst (PowerSeries.subst y l) ex = y := by
  have hl := PowerSeries.HasSubst.of_constantCoeff_zero' (constantCoeff_l hex0 h)
  have hy' := PowerSeries.HasSubst.of_constantCoeff_zero hy
  rw [← PowerSeries.subst_comp_subst_apply hl hy' ex, subst_l_ex hex0 h, PowerSeries.subst_X hy']
end PI.BeDiagZp.IdentW
