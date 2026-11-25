-- Prove2me | solution 1 for PI.BeDiagZp.IdentW.subst_l_ex
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T09:39:17.074261+00:00
-- url     : https://prove2.me/submissions/51a0f3f0-22ad-46c0-81fe-2882ff3e9ffb

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DiagonalPadicSubstitution_SubstOps
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DiagonalPadicSubstitution_CoeffOneLNeZero
import Theorems.Thm_PI_BeDiagZp_IdentW_constantCoeff_l
import Theorems.Thm_PI_BeDiagZp_IdentW_coeff_one_l_ne_zero
import Theorems.Thm_PI_BeDiagZp_IdentW_subst_left_inv

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
theorem _root_.solution {l ex : PowerSeries ℂ_[p]} (hex0 : PowerSeries.constantCoeff ex = 0)
    (h : PowerSeries.subst ex l = PowerSeries.X) : PowerSeries.subst l ex = PowerSeries.X :=
  subst_left_inv (constantCoeff_l hex0 h) (isUnit_iff_ne_zero.2 (coeff_one_l_ne_zero hex0 h)) hex0 h
end PI.BeDiagZp.IdentW
