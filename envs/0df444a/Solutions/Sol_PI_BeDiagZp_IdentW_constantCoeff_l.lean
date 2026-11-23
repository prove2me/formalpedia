-- Prove2me | solution 1 for PI.BeDiagZp.IdentW.constantCoeff_l
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:39:32.942743+00:00
-- url     : https://prove2.me/submissions/03dec332-3565-4baf-ba6d-8e8611098370

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DiagonalPadicSubstitution_SubstOps
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DiagonalPadicSubstitution_CoeffOneLNeZero

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
    (h : PowerSeries.subst ex l = PowerSeries.X) : PowerSeries.constantCoeff l = 0 := by
  have hex := PowerSeries.HasSubst.of_constantCoeff_zero' hex0
  have key := congrArg (PowerSeries.coeff 0) h
  rw [PowerSeries.coeff_subst' hex, finsum_eq_single _ 0] at key
  · simpa using key
  · intro d hd
    rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, map_pow, hex0, zero_pow hd, smul_zero]
end PI.BeDiagZp.IdentW
