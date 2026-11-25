-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UnimodLocStd.bounded_map
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T11:03:35.16494+00:00
-- url     : https://prove2.me/submissions/5594dc2b-9894-4c73-befa-5f0531efc643

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnimodularLocalStandard_IsKTheta
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnimodularLocalStandard_CommOfBounded
import Theorems.Thm_PI_UnitaryGroupMassFormula_UnimodLocStd_mem_stdLat_iff
import Theorems.Thm_PI_UnitaryGroupMassFormula_UnimodLocStd_exists_nsmul_mem
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
private theorem natCast_smul_eq_nsmul (N : ℕ) (y : m → ℂ) : (N : ℂ) • y = N • y := by
  exact Nat.cast_smul_eq_nsmul ℂ N y
private theorem intCast_smul_eq_zsmul (p : ℤ) (y : m → ℂ) : (p : ℂ) • y = p • y := by
  exact Int.cast_smul_eq_zsmul ℂ p y
private theorem nsmul_intCast_smul_comm (N : ℕ) (p : ℤ) (y : m → ℂ) : N • ((p : ℂ) • y) = p • (N • y) := by
  rw [← natCast_smul_eq_nsmul N ((p : ℂ) • y), ← natCast_smul_eq_nsmul N y, smul_comm (N : ℂ) (p : ℂ) y,
    intCast_smul_eq_zsmul p ((N : ℂ) • y)]
private theorem nsmul_mem_of_dvd_of_nsmul_mem {S : AddSubgroup (m → ℂ)} {x : m → ℂ} {n N : ℕ} (hnN : n ∣ N)
    (hx : n • x ∈ S) : N • x ∈ S := by
  obtain ⟨k, rfl⟩ := hnN
  have e : (n * k) • x = k • (n • x) := by
    calc (n * k) • x = ((n * k : ℕ) : ℂ) • x := (natCast_smul_eq_nsmul _ _).symm
      _ = (k : ℂ) • (n : ℂ) • x := by rw [smul_smul, Nat.cast_mul, mul_comm]
      _ = k • n • x := by rw [natCast_smul_eq_nsmul, natCast_smul_eq_nsmul]
  rw [e]
  exact nsmul_mem hx k
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
theorem _root_.solution (φ : (m → ℂ) →ₗ[ℂ] (m → ℂ))
    (h1 : ∀ i, IsKv b d lam (φ (Pi.single i (cmL a b d ha hd lam hlam).ω₁)))
    (h2 : ∀ i, IsKv b d lam (φ (Pi.single i (cmL a b d ha hd lam hlam).ω₂))) :
    ∃ N : ℕ, N ≠ 0 ∧ ∀ s ∈ stdLat (cmL a b d ha hd lam hlam) m,
      N • φ s ∈ stdLat (cmL a b d ha hd lam hlam) m := by
  choose N1 hN1 hm1 using fun i =>
    exists_nsmul_mem (ha := ha) (hd := hd) (hlam := hlam) (h1 i)
  choose N2 hN2 hm2 using fun i =>
    exists_nsmul_mem (ha := ha) (hd := hd) (hlam := hlam) (h2 i)
  refine ⟨∏ j, N1 j * N2 j, Finset.prod_ne_zero_iff.mpr fun j _ => mul_ne_zero (hN1 j) (hN2 j), ?_⟩
  have hdvd : ∀ i, N1 i * N2 i ∣ ∏ j, N1 j * N2 j := fun i =>
    Finset.dvd_prod_of_mem (fun j => N1 j * N2 j) (Finset.mem_univ i)
  have k1 : ∀ i, (∏ j, N1 j * N2 j) • φ (Pi.single i (PI.ULS.cmL a b d ha hd lam hlam).ω₁) ∈
      PI.ULS.stdLat (PI.ULS.cmL a b d ha hd lam hlam) m := fun i =>
    nsmul_mem_of_dvd_of_nsmul_mem ((dvd_mul_right (N1 i) (N2 i)).trans (hdvd i)) (hm1 i)
  have k2 : ∀ i, (∏ j, N1 j * N2 j) • φ (Pi.single i (PI.ULS.cmL a b d ha hd lam hlam).ω₂) ∈
      PI.ULS.stdLat (PI.ULS.cmL a b d ha hd lam hlam) m := fun i =>
    nsmul_mem_of_dvd_of_nsmul_mem ((dvd_mul_left (N2 i) (N1 i)).trans (hdvd i)) (hm2 i)
  intro s hs
  have hs' := (mem_stdLat_iff _ s).1 hs
  choose p q hpq using fun i => (lattice_iff _ _).1 (hs' i)
  have hs_sum : s = ∑ i, Pi.single i (s i) := by
    exact (Finset.univ_sum_single s).symm
  rw [hs_sum, map_sum, Finset.smul_sum]
  refine sum_mem fun i _ => ?_
  have e : Pi.single i (s i) = ((p i : ℤ) : ℂ) • Pi.single i (PI.ULS.cmL a b d ha hd lam hlam).ω₁ +
      ((q i : ℤ) : ℂ) • Pi.single i (PI.ULS.cmL a b d ha hd lam hlam).ω₂ := by
    rw [hpq i]
    funext j
    by_cases h : j = i
    · subst h
      simp [Complex.real_smul]
    · simp [Pi.single_apply, h]
  rw [e, map_add, map_smul, map_smul, smul_add, nsmul_intCast_smul_comm, nsmul_intCast_smul_comm]
  exact add_mem (zsmul_mem (k1 i) _) (zsmul_mem (k2 i) _)
end PI.UnitaryGroupMassFormula.UnimodLocStd
