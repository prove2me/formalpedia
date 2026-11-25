-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UnimodLocStd.comm_of_bounded
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T11:11:32.354976+00:00
-- url     : https://prove2.me/submissions/c278a573-a379-474c-8b63-8b334015205f

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnimodularLocalStandard_IsKTheta
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnimodularLocalStandard_CommOfBounded
import Theorems.Thm_PI_UnitaryGroupMassFormula_UnimodLocStd_relIdx_ne_zero_of_le_left
import Theorems.Thm_PI_UnitaryGroupMassFormula_UnimodLocStd_stdLat_smul_idx

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
theorem _root_.solution (σ : (m → ℂ) ≃ₗ[ℂ] (m → ℂ)) {N N' : ℕ} (hN : N ≠ 0) (hN' : N' ≠ 0)
    (h1 : ∀ s ∈ stdLat (cmL a b d ha hd lam hlam) m, N • σ s ∈ stdLat (cmL a b d ha hd lam hlam) m)
    (h2 : ∀ s ∈ stdLat (cmL a b d ha hd lam hlam) m, N' • σ.symm s ∈ stdLat (cmL a b d ha hd lam hlam) m) :
    relIdx (stdLat (cmL a b d ha hd lam hlam) m)
        (imgLat (σ : (m → ℂ) →ₗ[ℂ] (m → ℂ)) (stdLat (cmL a b d ha hd lam hlam) m)) ≠ 0 ∧
      relIdx (imgLat (σ : (m → ℂ) →ₗ[ℂ] (m → ℂ)) (stdLat (cmL a b d ha hd lam hlam) m))
        (stdLat (cmL a b d ha hd lam hlam) m) ≠ 0 := by
  unfold PI.ULS.relIdx PI.ULS.imgLat
  refine ⟨?_, ?_⟩
  · rw [← AddSubgroup.relIndex_comap]
    refine relIdx_ne_zero_of_le_left ?_ (stdLat_smul_idx _ m hN)
    intro x hx
    obtain ⟨s, hs, rfl⟩ := AddSubgroup.mem_map.mp hx
    rw [AddSubgroup.mem_comap]
    show σ ((N : ℂ) • s) ∈ _
    rw [map_smul, natCast_smul_eq_nsmul]
    exact h1 s hs
  · refine relIdx_ne_zero_of_le_left ?_ (stdLat_smul_idx _ m hN')
    intro x hx
    obtain ⟨s, hs, rfl⟩ := AddSubgroup.mem_map.mp hx
    refine AddSubgroup.mem_map.mpr ⟨N' • σ.symm s, h2 s hs, ?_⟩
    show σ (N' • σ.symm s) = (N' : ℂ) • s
    rw [map_nsmul, LinearEquiv.apply_symm_apply, natCast_smul_eq_nsmul]
end PI.UnitaryGroupMassFormula.UnimodLocStd
