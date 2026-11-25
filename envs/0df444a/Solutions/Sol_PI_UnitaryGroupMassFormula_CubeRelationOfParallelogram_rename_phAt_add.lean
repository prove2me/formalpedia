-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.CubeRelationOfParallelogram.rename_phAt_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:44:45.711182+00:00
-- url     : https://prove2.me/submissions/47724e23-add3-446e-8843-cca4f306cdba

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_FglGram
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CubeFormalIdentities_CoeffPowMulPowEqZero
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CubeFormalIdentities_IsExpIntegralParallelogramOfNe
import Theorems.Thm_PI_UnitaryGroupMassFormula_CubeRelationOfParallelogram_rename_psubst
import Theorems.Thm_PI_UnitaryGroupMassFormula_CubeRelationOfParallelogram_cc_lg_add
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
private theorem constantCoeff_subst_of_zero_lemma_2 {a : MvPowerSeries τ ℂ_[p]} (ha : constantCoeff a = 0)
    (g : PowerSeries ℂ_[p]) :
    constantCoeff (PowerSeries.subst a g) = PowerSeries.constantCoeff g := by
  have h := coeff_subst_eq_sum_range_of_degree_le ha g 0 0 (by simp)
  rw [← coeff_zero_eq_constantCoeff_apply, h]
  simp
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
variable {l ex : PowerSeries ℂ_[p]} (ph : PowerSeries ℂ_[p])
  (hex : PowerSeries.constantCoeff ex = 0) (hl : PowerSeries.constantCoeff l = 0)
include hex hl
namespace PI.UnitaryGroupMassFormula.CubeRelationOfParallelogram
theorem _root_.solution (e : σ ↪ τ) (a b : MvPowerSeries σ ℂ_[p]) (ha : constantCoeff a = 0)
    (hb : constantCoeff b = 0) :
    rename e (phAt ph (add l ex a b)) = phAt ph (add l ex (rename e a) (rename e b)) := by
  have hsum := cc_lg_add hl a b ha hb
  have hF : constantCoeff (PI.FglGram.add l ex a b) = 0 := by
    simp only [PI.FglGram.add, PI.FglGram.pt]
    rw [constantCoeff_subst_of_zero_lemma_2 hsum]
    exact hex
  simp only [PI.FglGram.phAt]
  rw [rename_psubst e hF]
  congr 1
  simp only [PI.FglGram.add, PI.FglGram.pt]
  rw [rename_psubst e hsum, map_add]
  simp only [PI.FglGram.lg]
  rw [rename_psubst e ha, rename_psubst e hb]
end PI.UnitaryGroupMassFormula.CubeRelationOfParallelogram
