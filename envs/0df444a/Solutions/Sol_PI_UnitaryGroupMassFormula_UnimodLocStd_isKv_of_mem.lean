-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UnimodLocStd.isKv_of_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:47:28.535378+00:00
-- url     : https://prove2.me/submissions/cb90be98-0fb5-417e-a779-b7067f50aadf

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnimodularLocalStandard_IsKTheta
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnimodularLocalStandard_CommOfBounded
import Theorems.Thm_PI_UnitaryGroupMassFormula_UnimodLocStd_cmL_omega1
import Theorems.Thm_PI_UnitaryGroupMassFormula_UnimodLocStd_cmL_omega2
import Theorems.Thm_PI_UnitaryGroupMassFormula_UnimodLocStd_mem_stdLat_iff
import Theorems.Thm_PI_UnitaryGroupMassFormula_UnimodLocStd_lattice_iff
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
variable {a : ℕ} {b c : ℤ} {d : ℕ} {ha : 0 < a} {hd : 0 < d} {lam : ℂ} {hlam : lam ≠ 0}
variable {m : Type*} [Fintype m] [DecidableEq m]
private theorem mul_div_cancel_left_of_ne_zero {w : ℂ} (hw : w ≠ 0) (x : ℂ) : w * x / w = x := by
  rw [mul_comm, mul_div_assoc, div_self hw, mul_one]
private theorem mem_cmL_lattice_iff (z : ℂ) :
    z ∈ (PI.ULS.cmL a b d ha hd lam hlam).lattice ↔
      ∃ p q : ℤ, z = lam * ((p : ℂ) * a + q * PI.ULS.cmTheta b d) := by
  rw [lattice_iff]
  simp only [cmL_omega1, cmL_omega2, Complex.real_smul, Complex.ofReal_intCast]
  constructor
  · rintro ⟨p, q, h⟩
    exact ⟨p, q, by rw [h]; ring⟩
  · rintro ⟨p, q, h⟩
    exact ⟨p, q, by rw [h]; ring⟩
end PI.UnitaryGroupMassFormula.UnimodLocStd
end
end

set_option autoImplicit false
noncomputable section
open scoped ComplexConjugate
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.UnimodLocStd
open PI.ULS
variable {a : ℕ} {b c : ℤ} {d : ℕ} {ha : 0 < a} {hd : 0 < d} {lam : ℂ} {hlam : lam ≠ 0}
variable {m : Type*} [Fintype m] [DecidableEq m]
namespace PI.UnitaryGroupMassFormula.UnimodLocStd
theorem _root_.solution {s : m → ℂ} (hs : s ∈ stdLat (cmL a b d ha hd lam hlam) m) : IsKv b d lam s := by
  intro i
  obtain ⟨p, q, hpq⟩ := (mem_cmL_lattice_iff _).1 ((mem_stdLat_iff _ s).1 hs i)
  refine ⟨p * (a : ℤ), q, 1, one_ne_zero, ?_⟩
  rw [hpq, mul_div_cancel_left_of_ne_zero hlam]
  push_cast
  ring
end PI.UnitaryGroupMassFormula.UnimodLocStd
