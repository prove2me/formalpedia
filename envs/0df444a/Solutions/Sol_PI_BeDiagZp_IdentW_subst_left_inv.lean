-- Prove2me | solution 1 for PI.BeDiagZp.IdentW.subst_left_inv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T09:34:58.214899+00:00
-- url     : https://prove2.me/submissions/b79a8ff5-ee71-43d7-856e-8ae7eb73ac7d

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
theorem _root_.solution {K : Type*} [Field K] {l ex : PowerSeries K} (hl0 : PowerSeries.constantCoeff l = 0)
    (hu : IsUnit (PowerSeries.coeff 1 l)) (hex0 : PowerSeries.constantCoeff ex = 0)
    (h : PowerSeries.subst ex l = PowerSeries.X) : PowerSeries.subst l ex = PowerSeries.X := by
  set Q := PowerSeries.substInvOfIsUnit l hu with hQ
  have hQl : PowerSeries.subst l Q = PowerSeries.X := PowerSeries.subst_substInvOfIsUnit_left l hl0 hu
  have hl : PowerSeries.HasSubst l := PowerSeries.HasSubst.of_constantCoeff_zero' hl0
  have hex : PowerSeries.HasSubst ex := PowerSeries.HasSubst.of_constantCoeff_zero' hex0
  have key : PowerSeries.subst ex (PowerSeries.subst l Q) = PowerSeries.subst (PowerSeries.subst ex l) Q :=
    PowerSeries.subst_comp_subst_apply hl hex Q
  rw [hQl, h, PowerSeries.subst_X hex, PowerSeries.X_subst] at key
  rw [key, hQl]
end PI.BeDiagZp.IdentW
