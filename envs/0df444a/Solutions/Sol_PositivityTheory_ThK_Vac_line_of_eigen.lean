-- Prove2me | solution 1 for PositivityTheory.ThK.Vac.line_of_eigen
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T05:22:23.873324+00:00
-- url     : https://prove2.me/submissions/96a39062-e38b-4e2e-934c-9c75eae9e1a8

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_MembershipCriteria_LaEqSqrtSmulLam
import Definitions.Def_Development_WeilBound_CoreStatements_CompactAveragingSplitting_EigenvectorLifting_VaceigenAlg
import Theorems.Thm_GlobalTheory_CompanionTheory_FinHeis_Sys_c_mul_c_swap


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PositivityTheory PositivityTheory.ThK PositivityTheory.ThK.Vac
open scoped nonZeroDivisors Matrix
open GlobalTheory.CompanionTheory.FinHeis
namespace PositivityTheory.ThK.Vac
theorem _root_.solution {X M : Type} [AddCommGroup X] [AddCommGroup M] [Module ℂ M] (S : Sys X M) (Γ : Set X) (χ : X → ℂ)
    (hΓ : ∀ x, (∀ γ ∈ Γ, S.c γ x ^ 2 = 1) → x ∈ Γ) {φ φ' : M} (h0 : φ ≠ 0) (hc : Cyclic S φ)
    (hφ : ∀ γ ∈ Γ, S.rho γ φ = χ γ • φ) (hφ' : ∀ γ ∈ Γ, S.rho γ φ' = χ γ • φ') : ∃ a : ℂ, φ' = a • φ := by
  have hne : S.B φ φ ≠ 0 := fun h => by simpa [h] using S.B_pos φ h0
  have hχ : ∀ γ ∈ Γ, (starRingEnd ℂ) (χ γ) * χ γ = 1 := fun γ hγ => by
    have h := S.B_rho γ φ φ
    rw [hφ γ hγ] at h
    simp only [map_smul, LinearMap.map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul] at h
    refine mul_right_cancel₀ hne ?_
    linear_combination h
  have key : ∀ η : M, (∀ γ ∈ Γ, S.rho γ η = χ γ • η) → S.B η φ = 0 → η = 0 := by
    intro η hη h1
    have hall : ∀ x, S.B η (S.rho x φ) = 0 := by
      intro x
      by_cases hx : x ∈ Γ
      · rw [hφ x hx, map_smul, h1, smul_zero]
      · by_contra hn
        refine hx (hΓ x fun γ hγ => mul_right_cancel₀ hn ?_)
        have h2 := S.B_rho γ η (S.rho x φ)
        have h3 : S.rho γ (S.rho x φ) = S.c γ x ^ 2 • S.rho x (S.rho γ φ) := by
          rw [S.rho_rho, S.rho_rho, smul_smul, add_comm x γ, pow_two, mul_assoc, S.c_mul_c_swap, mul_one]
        rw [h3, hφ γ hγ, hη γ hγ] at h2
        simp only [map_smul, LinearMap.map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul] at h2
        linear_combination h2 - S.c γ x ^ 2 * S.B η (S.rho x φ) * hχ γ hγ
    have hle : Submodule.span ℂ (Set.range fun x => S.rho x φ) ≤ LinearMap.ker (S.B η) := by
      rw [Submodule.span_le]
      rintro _ ⟨x, rfl⟩
      exact hall x
    rw [show Submodule.span ℂ (Set.range fun x => S.rho x φ) = ⊤ from hc] at hle
    have h4 : S.B η η = 0 := hle Submodule.mem_top
    by_contra hn
    simpa [h4] using S.B_pos η hn
  refine ⟨S.B φ φ' / S.B φ φ, sub_eq_zero.1 (key _ (fun γ hγ => ?_) ?_)⟩
  · rw [map_sub, map_smul, hφ γ hγ, hφ' γ hγ, smul_sub, smul_comm]
  · rw [← S.B_conj, map_sub, map_smul, smul_eq_mul, div_mul_cancel₀ _ hne, sub_self, map_zero]
end PositivityTheory.ThK.Vac
