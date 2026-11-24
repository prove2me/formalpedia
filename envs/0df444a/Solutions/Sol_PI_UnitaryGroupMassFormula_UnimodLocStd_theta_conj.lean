-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UnimodLocStd.theta_conj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T21:56:01.759803+00:00
-- url     : https://prove2.me/submissions/0275b733-a214-44e4-bac2-9223d4846509

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnimodularLocalStandard_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnimodularLocalStandard_RelIdxNeZeroOfLeLeft
import Theorems.Thm_PI_UnitaryGroupMassFormula_UnimodLocStd_smulHom_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] PI.UnitaryGroupMassFormula.UnimodLocStd.smulHom_apply

set_option autoImplicit false
noncomputable section
open scoped ComplexConjugate
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.UnimodLocStd
open PI.ULS
variable {a : ℕ} {b c : ℤ} {d : ℕ}
namespace PI.UnitaryGroupMassFormula.UnimodLocStd
theorem _root_.solution (b : ℤ) (d : ℕ) : conj (cmTheta b d) = b - cmTheta b d := by
  have h2 : (starRingEnd ℂ) (2 : ℂ) = 2 := map_ofNat _ 2
  first
  | (simp only [PI.ULS.cmTheta, map_div₀, map_add, map_mul, Complex.conj_I, Complex.conj_ofReal, map_intCast, h2]; ring)
  | (simp [PI.ULS.cmTheta, map_div₀]; ring)
  | (simp [PI.ULS.cmTheta, map_div₀]; done)
  | (apply Complex.ext <;> simp [PI.ULS.cmTheta] <;> ring)
end PI.UnitaryGroupMassFormula.UnimodLocStd
