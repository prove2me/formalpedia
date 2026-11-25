-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UnimodLocStd.isKv_of_nsmul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:47:30.071234+00:00
-- url     : https://prove2.me/submissions/1ea7f49e-23aa-40a2-b5a3-ec449cd868fe

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnimodularLocalStandard_IsKTheta
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnimodularLocalStandard_CommOfBounded
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open scoped ComplexConjugate
namespace PI.UnitaryGroupMassFormula.UnimodLocStd
open PI.ULS
variable {a : ℕ} {b c : ℤ} {d : ℕ} {ha : 0 < a} {hd : 0 < d} {lam : ℂ} {hlam : lam ≠ 0}
variable {m : Type*} [Fintype m] [DecidableEq m]
private theorem natCast_smul_eq_nsmul (N : ℕ) (y : m → ℂ) : (N : ℂ) • y = N • y := by
  exact Nat.cast_smul_eq_nsmul ℂ N y
private theorem nsmul_apply_eq_natCast_mul (N : ℕ) (v : m → ℂ) (i : m) : (N • v) i = (N : ℂ) * v i := by
  rw [← natCast_smul_eq_nsmul, Pi.smul_apply, smul_eq_mul]
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
theorem _root_.solution {v : m → ℂ} {N : ℕ} (hN : N ≠ 0) (h : IsKv b d lam (N • v)) : IsKv b d lam v := by
  intro i
  obtain ⟨p, q, r, hr, h'⟩ := h i
  refine ⟨p, q, r * N, mul_ne_zero hr (by exact_mod_cast hN), ?_⟩
  rw [← h', nsmul_apply_eq_natCast_mul]
  push_cast
  ring
end PI.UnitaryGroupMassFormula.UnimodLocStd
