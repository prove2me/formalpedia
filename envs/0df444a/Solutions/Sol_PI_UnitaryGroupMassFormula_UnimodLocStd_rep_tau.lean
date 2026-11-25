-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UnimodLocStd.rep_tau
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:52:40.543608+00:00
-- url     : https://prove2.me/submissions/a445455d-86ac-4283-9ba8-82aeb7aa6ed9

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnimodularLocalStandard_RepArith
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnimodularLocalStandard_RepNewton
import Theorems.Thm_PI_UnitaryGroupMassFormula_UnimodLocStd_rep_theta_add_conj
import Theorems.Thm_PI_UnitaryGroupMassFormula_UnimodLocStd_rep_theta_mul_conj


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
namespace PI.UnitaryGroupMassFormula.UnimodLocStd
theorem _root_.solution {m : Type} (a : ℕ) (b c : ℤ) (d : ℕ) (hOK : CmOK a b c d) (Λ : AddSubgroup (m → ℂ))
    (hθ : ∀ z ∈ Λ, cmTheta b d • z ∈ Λ) {l : ℕ} (hl : l.Prime) :
    ∃ τ : ℂ, ∃ r s : ℤ, τ + conj τ = 1 ∧ τ * conj τ = (r : ℂ) / s ∧ ¬ (l : ℤ) ∣ s ∧
      ∀ v : m → ℂ, SatMem l Λ v → SatMem l Λ (τ • v) := by
  obtain ⟨hac, -, hd8, -⟩ := hOK
  obtain ⟨k, hk⟩ : ∃ k : ℤ, b = 2 * k + 1 := by
    rcases Int.even_or_odd b with ⟨j, hj⟩ | ⟨j, hj⟩
    · exfalso
      have h4 : (d : ℤ) = 4 * ((a : ℤ) * c - j * j) := by
        rw [hj] at hac
        linear_combination -hac
      generalize (a : ℤ) * c - j * j = t at h4
      omega
    · exact ⟨j, hj⟩
  have hadd := rep_theta_add_conj b d
  have hmul := rep_theta_mul_conj a b c d hac
  refine ⟨cmTheta b d - (k : ℂ), a * c - k * b + k ^ 2, 1, ?_, ?_, ?_, ?_⟩
  · rw [map_sub, map_intCast]
    have hb : (b : ℂ) = 2 * k + 1 := by
      rw [hk]
      push_cast
      ring
    linear_combination hadd + hb
  · rw [map_sub, map_intCast]
    push_cast
    rw [div_one]
    linear_combination hmul - (k : ℂ) * hadd
  · intro h
    have h1 := Int.le_of_dvd one_pos h
    have h2 := hl.one_lt
    omega
  · intro v hv
    unfold SatMem at hv ⊢
    obtain ⟨n, hn, hnv⟩ := hv
    refine ⟨n, hn, ?_⟩
    rw [smul_comm, sub_smul, Int.cast_smul_eq_zsmul]
    exact Λ.sub_mem (hθ _ hnv) (Λ.zsmul_mem hnv k)
end PI.UnitaryGroupMassFormula.UnimodLocStd
