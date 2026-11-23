-- Prove2me | solution 1 for PI.JetsPhW.Ch.dX_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:34:02.404924+00:00
-- url     : https://prove2.me/submissions/860660c1-829f-43a3-8f92-5996ace8f040

import Definitions.Def_Formalism_PeriodIntegrals_JetsPhW
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_JetIntegrality_CoeffPowEqZeroOfDegreeLt
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
theorem _root_.solution (f : PowerSeries R) : dX f = PowerSeries.derivative R f := by
  ext n
  rw [PowerSeries.coeff_derivative, coeff_dX]
  ring
end PI.JetsPhW.Ch
