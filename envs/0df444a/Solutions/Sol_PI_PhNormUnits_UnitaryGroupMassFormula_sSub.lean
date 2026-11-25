-- Prove2me | solution 1 for PI.PhNormUnits.UnitaryGroupMassFormula.sSub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:09:51.959033+00:00
-- url     : https://prove2.me/submissions/5fdb6552-1e0a-449f-be4d-5c7c6260a14a

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_PhNormUnits
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PowerSeriesNormUnits_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PowerSeriesNormUnits_ConstantCoeffFormalSMul
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PowerSeriesNormUnits_TendstoCoeffOfCont
import Theorems.Thm_PI_PhNormUnits_UnitaryGroupMassFormula_sAdd
import Theorems.Thm_PI_PhNormUnits_UnitaryGroupMassFormula_sNeg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Classical Filter Topology MvPowerSeries.WithPiTopology
open PI PI.PhNormUnits PI.PhNormUnits.UnitaryGroupMassFormula
open PI.PhNormUnits
variable {p : ℕ} [Fact p.Prime]
variable (hE : CalcEquiv)
include hE
namespace PI.PhNormUnits.UnitaryGroupMassFormula
theorem _root_.solution {σ : Type} {f g h k : MvPowerSeries σ ℂ_[p]} (h1 : Simeq f g) (h2 : Simeq h k) :
    Simeq (f - h) (g - k) := by
  rw [sub_eq_add_neg, sub_eq_add_neg]; exact sAdd hE h1 (sNeg hE h2)
end PI.PhNormUnits.UnitaryGroupMassFormula
