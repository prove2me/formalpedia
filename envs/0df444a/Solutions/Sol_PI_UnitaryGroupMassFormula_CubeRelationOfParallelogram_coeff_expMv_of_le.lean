-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.CubeRelationOfParallelogram.coeff_expMv_of_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:42:19.223965+00:00
-- url     : https://prove2.me/submissions/8a3f3b0c-1f9d-4527-95ca-db42f20411ae

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_FglGram
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CubeFormalIdentities_CoeffPowMulPowEqZero
import Theorems.Thm_PI_UnitaryGroupMassFormula_CubeRelationOfParallelogram_coeff_expMv
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
variable {p : ℕ} [Fact p.Prime] {σ : Type*}
private lemma low_mul_lemma {X Y : MvPowerSeries σ ℂ_[p]} {a b : ℕ}
    (hX : ∀ β : σ →₀ ℕ, β.degree < a → coeff β X = 0) (hY : ∀ β : σ →₀ ℕ, β.degree < b → coeff β Y = 0) :
    ∀ β : σ →₀ ℕ, β.degree < a + b → coeff β (X * Y) = 0 := by
  intro β hβ
  rw [MvPowerSeries.coeff_mul]
  refine Finset.sum_eq_zero fun x hx => ?_
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx
  have hd : x.1.degree + x.2.degree = β.degree := by rw [← hx, map_add]
  by_cases h1 : x.1.degree < a
  · rw [hX _ h1, zero_mul]
  · rw [hY _ (by omega), mul_zero]
private lemma low_pow_lemma_2 {u : MvPowerSeries σ ℂ_[p]} (hu : constantCoeff u = 0) (n : ℕ) :
    ∀ β : σ →₀ ℕ, β.degree < n → coeff β (u ^ n) = 0 := by
  induction n with
  | zero => intro β h; exact absurd h (Nat.not_lt_zero _)
  | succ n ih =>
    rw [pow_succ]
    refine low_mul_lemma ih fun β hβ => ?_
    have h0 : β = 0 := (Finsupp.degree_eq_zero_iff β).mp (by omega)
    rw [h0, MvPowerSeries.coeff_zero_eq_constantCoeff_apply, hu]
end PI.UnitaryGroupMassFormula.CubeRelationOfParallelogram
end
end

set_option autoImplicit false
noncomputable section
open Classical
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.CubeRelationOfParallelogram
open PI.FglGram MvPowerSeries
variable {p : ℕ} [Fact p.Prime] {σ : Type*}
namespace PI.UnitaryGroupMassFormula.CubeRelationOfParallelogram
theorem _root_.solution {F : MvPowerSeries σ ℂ_[p]} (hF : constantCoeff F = 0) {α : σ →₀ ℕ}
    (N : ℕ) (hN : α.degree ≤ N) :
    coeff α (expMv F) = ∑ n ∈ Finset.range (N + 1), coeff α (F ^ n) / (n.factorial : ℂ_[p]) := by
  rw [coeff_expMv]
  apply Finset.sum_subset
  · intro x hx
    simp only [Finset.mem_range] at hx ⊢
    omega
  · intro n _ hn
    simp only [Finset.mem_range, not_lt] at hn
    rw [low_pow_lemma_2 hF n α (by omega), zero_div]
end PI.UnitaryGroupMassFormula.CubeRelationOfParallelogram
