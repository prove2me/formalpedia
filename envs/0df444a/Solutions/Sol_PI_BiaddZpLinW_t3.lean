-- Prove2me | solution 1 for PI.BiaddZpLinW.t3
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:00:16.553711+00:00
-- url     : https://prove2.me/submissions/2120efd5-30e5-45e6-b844-45fbb544c0a5

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_BiadditivePadicLinear_Cont2
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DiagonalPadicSubstitution_CoeffPowMulPowEqZeroOfLt
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DiagonalPadicSubstitution_PowerSeriesDiagonalLinear
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DiagonalPadicSubstitution_SubstOpsHolds
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DiagonalPadicSubstitution_CoeffOneLNeZero
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_BiadditivePadicLinear_BiaddZpLinOf
import Theorems.Thm_PI_BeDiagZp_IdentW_ident_holds


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
open PI PI.BiaddZpLinW
open PI.BiaddZpLin
namespace PI.BiaddZpLinW
theorem _root_.solution : ∀ (p : ℕ) [Fact p.Prime] (l ex : PowerSeries ℂ_[p]),
    PowerSeries.constantCoeff ex = 0 → PowerSeries.subst ex l = PowerSeries.X →
    PowerSeries.constantCoeff l = 0 ∧
    ∀ (σ : Type) (a b : MvPowerSeries σ ℂ_[p]),
      MvPowerSeries.constantCoeff a = 0 → MvPowerSeries.constantCoeff b = 0 →
      MvPowerSeries.constantCoeff (add l ex a b) = 0 ∧
      (∀ c, MvPowerSeries.constantCoeff (mulBy l ex c a) = 0) ∧
      add l ex a b = add l ex b a ∧
      add l ex a a = mulBy l ex 2 a ∧
      (∀ c d, add l ex (mulBy l ex c a) (mulBy l ex d a) = mulBy l ex (c + d) a) ∧
      (∀ c, add l ex (mulBy l ex c a) a = mulBy l ex (c + 1) a) ∧
      mulBy l ex 1 a = a ∧
      mulBy l ex 0 a = 0 :=
  PI.BeDiagZp.IdentW.ident_holds
end PI.BiaddZpLinW
