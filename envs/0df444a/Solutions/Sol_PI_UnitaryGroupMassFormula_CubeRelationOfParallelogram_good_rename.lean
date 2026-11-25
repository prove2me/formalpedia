-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.CubeRelationOfParallelogram.good_rename
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:39:38.855578+00:00
-- url     : https://prove2.me/submissions/0fafea66-e06f-4ad4-99e5-1ed99abcb154

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_FglGram
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CubeFormalIdentities_CoeffPowMulPowEqZero
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CubeFormalIdentities_IsExpIntegralParallelogramOfNe
import Theorems.Thm_PI_UnitaryGroupMassFormula_CubeRelationOfParallelogram_coeff_expMv
import Theorems.Thm_PI_UnitaryGroupMassFormula_CubeRelationOfParallelogram_coeff_expMv_of_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open Classical
namespace PI.UnitaryGroupMassFormula.CubeRelationOfParallelogram
open PI.FglGram MvPowerSeries
variable {p : ℕ} [Fact p.Prime] {σ τ : Type*}
private theorem coeff_embDomain_rename' (e : σ ↪ τ) (F : MvPowerSeries σ ℂ_[p]) (α : σ →₀ ℕ) :
    coeff (α.embDomain e) (rename e F) = coeff α F :=
  coeff_embDomain_rename e F α
private theorem coeff_rename_eq_zero_of_not_mem_range_embDomain_cube_formal_identities (e : σ ↪ τ) (F : MvPowerSeries σ ℂ_[p]) {β : τ →₀ ℕ}
    (hβ : ¬ ∃ α : σ →₀ ℕ, α.embDomain e = β) : coeff β (rename e F) = 0 := by
  apply coeff_rename_eq_zero
  rintro ⟨α, rfl⟩
  exact hβ ⟨α, Finsupp.embDomain_eq_mapDomain _ _⟩
private theorem constantCoeff_rename_embedding (e : σ ↪ τ) (F : MvPowerSeries σ ℂ_[p]) :
    constantCoeff (rename e F) = constantCoeff F :=
  constantCoeff_rename e F
section
variable {l ex : PowerSeries ℂ_[p]} (ph : PowerSeries ℂ_[p])
  (hex : PowerSeries.constantCoeff ex = 0) (hl : PowerSeries.constantCoeff l = 0)
end
end PI.UnitaryGroupMassFormula.CubeRelationOfParallelogram
end
end

set_option autoImplicit false
noncomputable section
open Classical
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.CubeRelationOfParallelogram
open PI.FglGram MvPowerSeries
variable {p : ℕ} [Fact p.Prime] {σ τ : Type*}
namespace PI.UnitaryGroupMassFormula.CubeRelationOfParallelogram
theorem _root_.solution (e : σ ↪ τ) {D : MvPowerSeries σ ℂ_[p]} (hD : Good D) : Good (rename e D) := by
  obtain ⟨h0, hI⟩ := hD
  have h0' : constantCoeff (rename e D) = 0 := by rw [constantCoeff_rename_embedding]; exact h0
  show constantCoeff (rename e D) = 0 ∧ PI.FglGram.IntegralMv (PI.FglGram.expMv (rename e D))
  refine ⟨h0', ?_⟩
  intro β
  by_cases hβ : ∃ α : σ →₀ ℕ, α.embDomain e = β
  · obtain ⟨α, rfl⟩ := hβ
    have hα := hI α
    rw [coeff_expMv_of_le h0 (α.degree + (α.embDomain e).degree)
      (Nat.le_add_right _ _)] at hα
    rw [coeff_expMv_of_le h0' (α.degree + (α.embDomain e).degree)
      (Nat.le_add_left _ _)]
    have hc : ∀ n, coeff (α.embDomain e) (rename e D ^ n) = coeff α (D ^ n) := fun n => by
      rw [← map_pow, coeff_embDomain_rename']
    simp only [hc]
    exact hα
  · rw [coeff_expMv (rename e D) β]
    have hz : ∀ n, coeff β (rename e D ^ n) = 0 := fun n => by
      rw [← map_pow]; exact coeff_rename_eq_zero_of_not_mem_range_embDomain_cube_formal_identities e _ hβ
    simp only [hz, zero_div, Finset.sum_const_zero]
    simp [PI.FglGram.IsIntP]
end PI.UnitaryGroupMassFormula.CubeRelationOfParallelogram
