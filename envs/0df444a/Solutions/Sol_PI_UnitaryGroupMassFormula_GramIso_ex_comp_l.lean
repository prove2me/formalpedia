-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.GramIso.ex_comp_l
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:44:48.528722+00:00
-- url     : https://prove2.me/submissions/eed3d7af-2846-4ab8-ac67-1f36dba4d88e

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_FglGram
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GramIsometryCoefficient_ExCoeffOneNe
import Theorems.Thm_PI_UnitaryGroupMassFormula_GramIso_ex_coeff_one_ne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.GramIso
open PI.FglGram
variable {p : ℕ} [Fact p.Prime]
namespace PI.UnitaryGroupMassFormula.GramIso
theorem _root_.solution (l ex : PowerSeries ℂ_[p]) (he : PowerSeries.constantCoeff ex = 0)
    (hl : PowerSeries.subst ex l = PowerSeries.X) : PowerSeries.subst l ex = PowerSeries.X := by
  have hu : IsUnit (PowerSeries.coeff 1 ex) := isUnit_iff_ne_zero.mpr (ex_coeff_one_ne l ex he hl)
  have hex : PowerSeries.HasSubst ex := PowerSeries.HasSubst.of_constantCoeff_zero' he
  have hgS : PowerSeries.HasSubst (ex.substInvOfIsUnit hu) := PowerSeries.HasSubst.substInvOfIsUnit ex hu
  have hright : PowerSeries.subst (ex.substInvOfIsUnit hu) ex = PowerSeries.X :=
    PowerSeries.subst_substInvOfIsUnit_right ex he hu
  have hg : l = ex.substInvOfIsUnit hu := by
    calc l = PowerSeries.subst PowerSeries.X l := (PowerSeries.X_subst l).symm
      _ = PowerSeries.subst (PowerSeries.subst (ex.substInvOfIsUnit hu) ex) l := by rw [hright]
      _ = PowerSeries.subst (ex.substInvOfIsUnit hu) (PowerSeries.subst ex l) :=
          (PowerSeries.subst_comp_subst_apply hex hgS l).symm
      _ = PowerSeries.subst (ex.substInvOfIsUnit hu) PowerSeries.X := by rw [hl]
      _ = ex.substInvOfIsUnit hu := PowerSeries.subst_X hgS
  rw [hg, hright]
end PI.UnitaryGroupMassFormula.GramIso
