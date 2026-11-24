-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UnimodLocStd.isK_conj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:05:11.946649+00:00
-- url     : https://prove2.me/submissions/81fbbd0b-0413-4cc7-9ab3-e7d0932888a8

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnimodularLocalStandard_SelfDualStd
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnimodularLocalStandard_IsKTheta
import Theorems.Thm_PI_UnitaryGroupMassFormula_UnimodLocStd_smulHom_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] PI.UnitaryGroupMassFormula.UnimodLocStd.smulHom_apply


section
noncomputable section
open scoped ComplexConjugate
namespace PI.UnitaryGroupMassFormula.UnimodLocStd
open PI.ULS
section IsKsec
variable (b : ℤ) (d : ℕ)
variable {b d}
private lemma conj_cmTheta : conj (cmTheta b d) = (b : ℂ) - cmTheta b d := by
  unfold cmTheta
  simp only [map_div₀, map_add, map_mul, Complex.conj_I, Complex.conj_ofReal, map_intCast, map_ofNat]
  ring
variable {e : ℤ} (hn : cmTheta b d * (b - cmTheta b d) = (e : ℂ))
include hn
end IsKsec
end PI.UnitaryGroupMassFormula.UnimodLocStd
end
end

set_option autoImplicit false
noncomputable section
open scoped ComplexConjugate
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.UnimodLocStd
open PI.ULS
variable (b : ℤ) (d : ℕ)
variable {b d}
namespace PI.UnitaryGroupMassFormula.UnimodLocStd
theorem _root_.solution {t : ℂ} (h : IsK b d t) : IsK b d (conj t) := by
  obtain ⟨p, q, r, hr, h⟩ := h
  have h2 : (r : ℂ) * conj t = p + q * conj (cmTheta b d) := by
    have h3 := congrArg conj h
    simpa using h3
  unfold PI.UnitaryGroupMassFormula.UnimodLocStd.IsK
  refine ⟨p + q * b, -q, r, hr, ?_⟩
  rw [h2, PI.UnitaryGroupMassFormula.UnimodLocStd.conj_cmTheta]
  push_cast
  ring
end PI.UnitaryGroupMassFormula.UnimodLocStd
