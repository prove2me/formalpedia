-- Prove2me | solution 1 for PI.BiaddZpLinW.t2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T09:45:19.749371+00:00
-- url     : https://prove2.me/submissions/585c445e-efa5-405c-8aab-77f07f25c4bb

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_BiadditivePadicLinear_Cont2
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DiagonalPadicSubstitution_CoeffPowMulPowEqZeroOfLt
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DiagonalPadicSubstitution_PowerSeriesDiagonalLinear
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DiagonalPadicSubstitution_SubstOpsHolds
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DiagonalPadicSubstitution_CoeffOneLNeZero
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_BiadditivePadicLinear_BiaddZpLinOf
import Theorems.Thm_PI_BeDiagZp_OpsW_substOps_holds


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
theorem _root_.solution : ∀ (p : ℕ) [Fact p.Prime] (l ex ph : PowerSeries ℂ_[p]),
    PowerSeries.constantCoeff ex = 0 → PowerSeries.constantCoeff l = 0 →
    ∀ (σ τ : Type) [Finite σ] (s : σ → MvPowerSeries τ ℂ_[p]),
    (∀ i, MvPowerSeries.constantCoeff (s i) = 0) →
    (∀ i, MvPowerSeries.subst s (Xv i : MvPowerSeries σ ℂ_[p]) = s i) ∧
    (∀ (c : ℂ_[p]) (a : MvPowerSeries σ ℂ_[p]),
      MvPowerSeries.subst s (MvPowerSeries.C c * a) = MvPowerSeries.C c * MvPowerSeries.subst s a) ∧
    (∀ a b : MvPowerSeries σ ℂ_[p],
      MvPowerSeries.subst s (a + b) = MvPowerSeries.subst s a + MvPowerSeries.subst s b) ∧
    ∀ a b : MvPowerSeries σ ℂ_[p], MvPowerSeries.constantCoeff a = 0 → MvPowerSeries.constantCoeff b = 0 →
      MvPowerSeries.constantCoeff (MvPowerSeries.subst s a) = 0 ∧
      MvPowerSeries.subst s (add l ex a b) = add l ex (MvPowerSeries.subst s a) (MvPowerSeries.subst s b) ∧
      (∀ c, MvPowerSeries.subst s (mulBy l ex c a) = mulBy l ex c (MvPowerSeries.subst s a)) ∧
      MvPowerSeries.subst s (phAt ph a) = phAt ph (MvPowerSeries.subst s a) ∧
      MvPowerSeries.subst s (be l ex ph a b) = be l ex ph (MvPowerSeries.subst s a) (MvPowerSeries.subst s b) :=
  PI.BeDiagZp.OpsW.substOps_holds
end PI.BiaddZpLinW
