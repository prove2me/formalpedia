-- Prove2me | solution 1 for PI.JetsPhW.Ch.pderiv_subst
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T09:57:21.889973+00:00
-- url     : https://prove2.me/submissions/ca4947ce-083b-4165-a377-1b026db6bdbb

import Definitions.Def_Formalism_PeriodIntegrals_JetsPhW
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_JetIntegrality_CoeffPowEqZeroOfDegreeLt
import Theorems.Thm_PI_JetsPhW_Ch_degree_le_of_le
import Theorems.Thm_PI_JetsPhW_Ch_coeff_subst_congr
import Theorems.Thm_PI_JetsPhW_Ch_coeff_mul_congr
import Theorems.Thm_PI_JetsPhW_Ch_pderiv_subst_coe
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
private theorem coeff_dX (f : PowerSeries R) (n : ℕ) :
    PowerSeries.coeff n (PI.JetsPhW.dX f) = ((n : R) + 1) * PowerSeries.coeff (n + 1) f := by
  simp only [PI.JetsPhW.dX, PowerSeries.coeff_mk]
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
theorem _root_.solution (i : σ) {a : MvPowerSeries σ R} (ha : MvPowerSeries.constantCoeff a = 0)
    (g : PowerSeries R) :
    MvPowerSeries.pderiv R i (PowerSeries.subst a g) =
      MvPowerSeries.pderiv R i a * PowerSeries.subst a (dX g) := by
  ext e
  have h1 : MvPowerSeries.coeff e (MvPowerSeries.pderiv R i (PowerSeries.subst a g)) =
      MvPowerSeries.coeff e (MvPowerSeries.pderiv R i
        (PowerSeries.subst a (PowerSeries.trunc (e.degree + 2) g : PowerSeries R))) := by
    rw [MvPowerSeries.coeff_pderiv, MvPowerSeries.coeff_pderiv]
    congr 1
    refine coeff_subst_congr ha (N := e.degree + 2) (fun k hk => ?_) ?_
    · exact (PowerSeries.coeff_coe_trunc_of_lt hk).symm
    · rw [map_add, Finsupp.degree_single]
      omega
  have h2 : MvPowerSeries.coeff e (MvPowerSeries.pderiv R i a * PowerSeries.subst a (PI.JetsPhW.dX g)) =
      MvPowerSeries.coeff e (MvPowerSeries.pderiv R i a *
        PowerSeries.subst a (PI.JetsPhW.dX (PowerSeries.trunc (e.degree + 2) g : PowerSeries R))) := by
    refine coeff_mul_congr _ fun y hy => ?_
    refine coeff_subst_congr ha (N := e.degree + 1) (fun k hk => ?_) ?_
    · rw [coeff_dX, coeff_dX, PowerSeries.coeff_coe_trunc_of_lt (n := k + 1) (m := e.degree + 2) (by omega)]
    · exact Nat.lt_succ_of_le (degree_le_of_le hy)
  rw [h1, pderiv_subst_coe i ha, h2]
end PI.JetsPhW.Ch
