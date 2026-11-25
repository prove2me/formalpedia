-- Prove2me | solution 1 for PI.FglChordFactor.Wk.iW_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:02:10.425736+00:00
-- url     : https://prove2.me/submissions/1b63f97e-7da3-4ae6-96d8-f880b8b5cf4a

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_FglChordFactor
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdditiveIntegralGroups_DXEqDerivative
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdditiveIntegralGroups_DvCoeffMulEqZeroOfLtOrder
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdditiveIntegralGroups_GlueHoldsVar
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalGroupChords_NormDeltaWc
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalGroupChords_SubstPairSecondVariable
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalGroupChords_DerivativeFlog
import Theorems.Thm_PI_FglChordFactor_Wk_D_const
import Theorems.Thm_PI_AddIntG_Wk_inv_mem_SerS
import Theorems.Thm_PI_AddIntG_Wk_mem_SerS
import Theorems.Thm_PI_FglChordFactor_Wk_serS_unit
import Theorems.Thm_PI_FglChordFactor_Wk_serS_unit_iff


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
open PI PI.FglChordFactor PI.FglChordFactor.Wk
open PI.AddIntG.Wk (SerS mem_SerS inv_mem_SerS)
variable {p : ℕ} [Fact p.Prime]
namespace PI.FglChordFactor.Wk
theorem _root_.solution {S : Subring ℂ_[p]} {W : WeierstrassCurve ℂ_[p]} {wq : PowerSeries ℂ_[p]} (h1 : W.a₁ ∈ S)
    (h3 : W.a₃ ∈ S) (hw : ∀ n, PowerSeries.coeff n wq ∈ S) : ∀ n, PowerSeries.coeff n (iW W wq) ∈ S := by
  have hcP : ∀ x ∈ S, ∀ n, PowerSeries.coeff n (cP x) ∈ S := by
    intro x hx n
    rw [cP, Algebra.algebraMap_eq_smul_one, PowerSeries.coeff_smul, PowerSeries.coeff_one]
    split_ifs
    · rw [smul_eq_mul, mul_one]; exact hx
    · rw [smul_zero]; exact S.zero_mem
  have hXm : (PowerSeries.X : MvPowerSeries Unit ℂ_[p]) ∈ SerS S Unit := serS_unit fun n => by
    rw [PowerSeries.coeff_X]
    split_ifs
    · exact S.one_mem
    · exact S.zero_mem
  have h1m := serS_unit (hcP _ h1)
  have h3m := serS_unit (hcP _ h3)
  have hwm := serS_unit hw
  have hDm : (Dser W wq : MvPowerSeries Unit ℂ_[p]) ∈ SerS S Unit :=
    (SerS S Unit).sub_mem (SerS S Unit).one_mem ((SerS S Unit).add_mem ((SerS S Unit).mul_mem h1m hXm)
      ((SerS S Unit).mul_mem ((SerS S Unit).mul_mem h3m ((SerS S Unit).pow_mem hXm 3)) hwm))
  have hi : (iW W wq : MvPowerSeries Unit ℂ_[p]) ∈ SerS S Unit :=
    (SerS S Unit).mul_mem ((SerS S Unit).neg_mem hXm) (inv_mem_SerS S (D_const W wq) hDm)
  exact serS_unit_iff.1 hi
end PI.FglChordFactor.Wk
