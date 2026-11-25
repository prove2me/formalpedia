-- Prove2me | solution 1 for PI.JetsPhW.Ch.subst_v_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T09:44:23.529379+00:00
-- url     : https://prove2.me/submissions/8097e63e-4a34-4e16-a550-30621168704b

import Definitions.Def_Formalism_PeriodIntegrals_JetsPhW
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_JetIntegrality_CoeffPowEqZeroOfDegreeLt
import Theorems.Thm_P2M_PI_JetsPhW_Ch_subst_one__be9486c9456e
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open PI.JetsPhW
namespace PI.JetsPhW.Ch
section Chain
variable {R : Type*} [CommRing R] {σ : Type*}
private theorem powerSeries_hasSubst_mvPowerSeries_X (i : σ) : PowerSeries.HasSubst (MvPowerSeries.X i : MvPowerSeries σ R) :=
  PowerSeries.HasSubst.of_constantCoeff_zero (MvPowerSeries.constantCoeff_X i)
end Chain
end PI.JetsPhW.Ch
end
end

set_option autoImplicit false
noncomputable section
open PI.JetsPhW
open PI PI.JetsPhW PI.JetsPhW.Ch
variable {R : Type*} [CommRing R] {σ : Type*}
namespace PI.JetsPhW.Ch
theorem _root_.solution {l v : PowerSeries R} (hv : v * dX l = 1) (i : σ) :
    PowerSeries.subst (MvPowerSeries.X i : MvPowerSeries σ R) v *
      PowerSeries.subst (MvPowerSeries.X i : MvPowerSeries σ R) (dX l) = 1 := by
  rw [← PowerSeries.subst_mul (powerSeries_hasSubst_mvPowerSeries_X i), hv, subst_one']
end PI.JetsPhW.Ch
