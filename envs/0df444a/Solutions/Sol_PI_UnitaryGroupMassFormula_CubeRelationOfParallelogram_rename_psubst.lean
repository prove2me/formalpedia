-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.CubeRelationOfParallelogram.rename_psubst
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:42:29.57686+00:00
-- url     : https://prove2.me/submissions/a0e5b629-ea22-4eb7-b5e0-79b849ec2265

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_FglGram
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CubeFormalIdentities_CoeffPowMulPowEqZero
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CubeFormalIdentities_IsExpIntegralParallelogramOfNe
import Theorems.Thm_PI_UnitaryGroupMassFormula_CubeRelationOfParallelogram_coeff_mul_pow_eq_zero

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
private theorem coeff_subst_eq_sum_range_of_degree_le {a : MvPowerSeries τ ℂ_[p]} (ha : constantCoeff a = 0)
    (g : PowerSeries ℂ_[p]) (β : τ →₀ ℕ) (N : ℕ) (hN : β.degree ≤ N) :
    coeff β (PowerSeries.subst a g) =
      ∑ n ∈ Finset.range (N + 1), PowerSeries.coeff n g * coeff β (a ^ n) := by
  have hs : PowerSeries.HasSubst a := PowerSeries.HasSubst.of_constantCoeff_zero ha
  rw [PowerSeries.coeff_subst hs]
  rw [finsum_eq_sum_of_support_subset _ (s := Finset.range (N + 1)) ?_]
  · simp only [smul_eq_mul]
  · intro n hn
    rw [Function.mem_support] at hn
    rw [Finset.coe_range, Set.mem_Iio]
    by_contra h
    apply hn
    have h0 : coeff β (a ^ n) = 0 := by
      have := coeff_mul_pow_eq_zero ha (1 : MvPowerSeries τ ℂ_[p]) (n := n) (α := β)
        (by omega)
      simpa using this
    rw [h0, smul_zero]
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
theorem _root_.solution (e : σ ↪ τ) {a : MvPowerSeries σ ℂ_[p]} (ha : constantCoeff a = 0)
    (g : PowerSeries ℂ_[p]) :
    rename e (PowerSeries.subst a g) = PowerSeries.subst (rename e a) g := by
  have ha' : constantCoeff (rename e a) = 0 := by rw [constantCoeff_rename_embedding]; exact ha
  ext β
  by_cases hβ : ∃ α : σ →₀ ℕ, α.embDomain e = β
  · obtain ⟨α, rfl⟩ := hβ
    rw [coeff_embDomain_rename', coeff_subst_eq_sum_range_of_degree_le ha g α (α.degree + (α.embDomain e).degree)
      (Nat.le_add_right _ _), coeff_subst_eq_sum_range_of_degree_le ha' g _ (α.degree + (α.embDomain e).degree)
      (Nat.le_add_left _ _)]
    have hc : ∀ n, coeff (α.embDomain e) (rename e a ^ n) = coeff α (a ^ n) := fun n => by
      rw [← map_pow, coeff_embDomain_rename']
    simp only [hc]
  · rw [coeff_rename_eq_zero_of_not_mem_range_embDomain_cube_formal_identities e _ hβ, coeff_subst_eq_sum_range_of_degree_le ha' g β β.degree le_rfl]
    have hz : ∀ n, coeff β (rename e a ^ n) = 0 := fun n => by
      rw [← map_pow]; exact coeff_rename_eq_zero_of_not_mem_range_embDomain_cube_formal_identities e _ hβ
    simp only [hz, mul_zero, Finset.sum_const_zero]
end PI.UnitaryGroupMassFormula.CubeRelationOfParallelogram
