-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UnimodLocStd.exists_nsmul_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:50:51.798488+00:00
-- url     : https://prove2.me/submissions/5963e376-7f4b-4087-bf13-59da0e4f23c9

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
theorem _root_.solution {v : m → ℂ} (h : IsKv b d lam v) :
    ∃ N : ℕ, N ≠ 0 ∧ N • v ∈ stdLat (cmL a b d ha hd lam hlam) m := by
  choose p q r hr hpq using h
  have hself : ∀ z : ℤ, z ∣ (z.natAbs : ℤ) := fun _ => Int.dvd_natAbs.mpr dvd_rfl
  obtain ⟨M, hM0, hMdvd⟩ : ∃ M : ℕ, M ≠ 0 ∧ ∀ i, r i ∣ (M : ℤ) := by
    refine ⟨∏ j, (r j).natAbs, Finset.prod_ne_zero_iff.mpr fun j _ => Int.natAbs_ne_zero.mpr (hr j),
      fun i => (hself (r i)).trans ?_⟩
    have hi : (r i).natAbs ∣ ∏ j, (r j).natAbs :=
      Finset.dvd_prod_of_mem (fun j => (r j).natAbs) (Finset.mem_univ i)
    exact Int.natCast_dvd_natCast.mpr hi
  refine ⟨a * M, mul_ne_zero ha.ne' hM0, ?_⟩
  rw [mem_stdLat_iff]
  intro i
  obtain ⟨k, hk⟩ := hMdvd i
  have hk' : (M : ℂ) = (r i : ℂ) * k := by exact_mod_cast hk
  have e : v i = v i / lam * lam := (div_eq_iff hlam).mp rfl
  have hv : (r i : ℂ) * v i = lam * (p i + q i * PI.ULS.cmTheta b d) := by
    calc (r i : ℂ) * v i = (r i * (v i / lam)) * lam := by rw [mul_assoc, ← e]
      _ = (p i + q i * PI.ULS.cmTheta b d) * lam := by rw [hpq i]
      _ = lam * (p i + q i * PI.ULS.cmTheta b d) := mul_comm _ _
  rw [mem_cmL_lattice_iff]
  refine ⟨k * p i, a * k * q i, ?_⟩
  rw [nsmul_apply_eq_natCast_mul, Nat.cast_mul, hk']
  push_cast
  linear_combination ((a : ℂ) * k) * hv
end PI.UnitaryGroupMassFormula.UnimodLocStd
