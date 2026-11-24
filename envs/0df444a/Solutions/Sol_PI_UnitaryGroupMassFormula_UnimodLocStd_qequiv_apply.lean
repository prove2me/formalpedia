-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UnimodLocStd.qequiv_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T21:41:10.20553+00:00
-- url     : https://prove2.me/submissions/75c533f0-6260-49af-88d6-ce20073c7004

import Definitions.Def_Formalism_PeriodIntegrals_UnimodLocStd
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnimodularLocalStandard_QequivApply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped ComplexConjugate
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.UnimodLocStd
open PI.ULS
variable {V : Type*} [AddCommGroup V] [Module ℂ V] (H : Sesq V)
namespace PI.UnitaryGroupMassFormula.UnimodLocStd
theorem _root_.solution (z : V) {c : ℂ} (hc0 : c ≠ 0) (hc : c + conj c = H z z) (w : V) :
    qequiv H z hc0 hc w = w - (c⁻¹ * H w z) • z := by
  show qmap H z c⁻¹ w = _
  exact qmap_apply H z c⁻¹ w
end PI.UnitaryGroupMassFormula.UnimodLocStd
