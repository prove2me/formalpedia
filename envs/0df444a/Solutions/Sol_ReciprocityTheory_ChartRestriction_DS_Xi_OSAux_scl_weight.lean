-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Xi.OSAux.scl_weight
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:18:45.447752+00:00
-- url     : https://prove2.me/submissions/26267663-018e-44b9-8521-348c5c50b9ca

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_Imports
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_RhoSqNonneg
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace ReciprocityTheory.ChartRestriction.DS.Xi
namespace OSAux
private lemma linF_scl {p m : ℕ} (τ : ℝ) (hτ : τ ≠ 0) (η η' : Fin (p + 1) → ℂ) (ζ : Fin m → ℂ)
    (x : Xp (p + 1) m) :
    (τ : ℂ) * linF η η' ζ (scl τ x) = x.2.1 0 * η' 0 +
      ((∑ j : Fin p, (x.1 j.succ * η j.succ + x.2.1 j.succ * η' j.succ)) + ∑ i, x.2.2.1 i * ζ i) * τ +
      x.1 0 * η 0 * τ ^ 2 := by
  have hτ' : (τ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hτ
  have e1 : (scl τ x).1 0 = (τ : ℂ) * x.1 0 := by simp [scl]
  have e2 : (scl τ x).2.1 0 = x.2.1 0 / (τ : ℂ) := by simp [scl]
  have e3 : ∀ j : Fin p, (scl τ x).1 j.succ = x.1 j.succ := fun j => by
    simp [scl, Fin.succ_ne_zero]
  have e4 : ∀ j : Fin p, (scl τ x).2.1 j.succ = x.2.1 j.succ := fun j => by
    simp [scl, Fin.succ_ne_zero]
  have e5 : (scl τ x).2.2.1 = x.2.2.1 := rfl
  have hk : (τ : ℂ) * (x.2.1 0 / (τ : ℂ) * η' 0) = x.2.1 0 * η' 0 := by
    field_simp
  unfold linF
  rw [Fin.sum_univ_succ]
  simp only [e1, e2, e3, e4, e5]
  linear_combination hk
private lemma enn_norm (z : ℂ) : ENNReal.ofReal ‖z‖ = (‖z‖₊ : ℝ≥0∞) := by
  rw [← coe_nnnorm, ENNReal.ofReal_coe_nnreal]
end OSAux
end ReciprocityTheory.ChartRestriction.DS.Xi
end
end

set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open scoped ENNReal
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Xi
open ReciprocityTheory.ChartRestriction.DS.Xi.OSAux
namespace ReciprocityTheory.ChartRestriction.DS.Xi.OSAux
theorem _root_.solution (hS : SUB) {δ γ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1 / 2) (hγ0 : 0 < γ) (hγ : γ ≤ δ / 8) :
    ∃ C : ℝ, 0 < C ∧ ∀ {p m : ℕ} (η η' : Fin (p + 1) → ℂ) (ζ : Fin m → ℂ) (x : Xp (p + 1) m),
      ∫⁻ τ in Icc (1 : ℝ) 2, ENNReal.ofReal ((1 + ‖linF η η' ζ (scl τ x)‖) ^ (-δ / 4)) ≤
        ENNReal.ofReal C * (‖η' 0‖₊ : ℝ≥0∞) ^ (-γ) * (‖x.2.1 0‖₊ : ℝ≥0∞) ^ (-γ) := by
  obtain ⟨CS, hCS⟩ := hS (δ / 4) (by positivity) (by linarith)
  have hC : 0 < 2 ^ (δ / 4) * (|CS| + 1) := by positivity
  refine ⟨2 ^ (δ / 4) * (|CS| + 1), hC, ?_⟩
  intro p m η η' ζ x
  have hCn : ENNReal.ofReal (2 ^ (δ / 4) * (|CS| + 1)) ≠ 0 := by
    rw [Ne, ENNReal.ofReal_eq_zero, not_le]; exact hC
  have hng : -γ < 0 := by linarith
  by_cases hη : η' 0 = 0
  · refine le_top.trans (le_of_eq ?_)
    rw [hη, nnnorm_zero, ENNReal.coe_zero, ENNReal.zero_rpow_of_neg hng, ENNReal.mul_top hCn,
      ENNReal.top_mul]
    rw [Ne, ENNReal.rpow_eq_zero_iff]
    simp [hγ0.le]
  by_cases ha : x.2.1 0 = 0
  · refine le_top.trans (le_of_eq ?_)
    rw [ha, nnnorm_zero, ENNReal.coe_zero, ENNReal.zero_rpow_of_neg hng, ENNReal.mul_top]
    refine mul_ne_zero hCn ?_
    rw [Ne, ENNReal.rpow_eq_zero_iff]
    simp [hγ0.le]
  set R : ℂ := (∑ j : Fin p, (x.1 j.succ * η j.succ + x.2.1 j.succ * η' j.succ)) + ∑ i, x.2.2.1 i * ζ i
  set c : Fin 3 → ℂ := ![x.2.1 0 * η' 0, R, x.1 0 * η 0] with hc
  have hc0 : c 0 = x.2.1 0 * η' 0 := rfl
  have hc1 : c 1 = R := rfl
  have hc2 : c 2 = x.1 0 * η 0 := rfl
  have hpt : ∀ τ ∈ Icc (1 : ℝ) 2, ENNReal.ofReal ((1 + ‖linF η η' ζ (scl τ x)‖) ^ (-δ / 4)) ≤
      ENNReal.ofReal (2 ^ (δ / 4)) *
        ENNReal.ofReal ((1 + ‖c 0 + c 1 * τ + c 2 * (τ : ℂ) ^ 2‖) ^ (-(δ / 4))) := by
    intro τ hτ
    have hτ0 : 0 < τ := by linarith [hτ.1]
    rw [← ENNReal.ofReal_mul (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    have hP : ‖c 0 + c 1 * τ + c 2 * (τ : ℂ) ^ 2‖ ≤ 2 * ‖linF η η' ζ (scl τ x)‖ := by
      rw [hc0, hc1, hc2, ← linF_scl τ hτ0.ne' η η' ζ x, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos hτ0]
      gcongr
      exact hτ.2
    have hF := norm_nonneg (linF η η' ζ (scl τ x))
    have hP0 := norm_nonneg (c 0 + c 1 * τ + c 2 * (τ : ℂ) ^ 2)
    have h1 : (1 + ‖c 0 + c 1 * τ + c 2 * (τ : ℂ) ^ 2‖) / 2 ≤ 1 + ‖linF η η' ζ (scl τ x)‖ := by linarith
    calc (1 + ‖linF η η' ζ (scl τ x)‖) ^ (-δ / 4)
        ≤ ((1 + ‖c 0 + c 1 * τ + c 2 * (τ : ℂ) ^ 2‖) / 2) ^ (-δ / 4) :=
          Real.rpow_le_rpow_of_nonpos (by positivity) h1 (by linarith)
      _ = 2 ^ (δ / 4) * (1 + ‖c 0 + c 1 * τ + c 2 * (τ : ℂ) ^ 2‖) ^ (-(δ / 4)) := by
          rw [Real.div_rpow (by positivity) (by norm_num), neg_div,
            Real.rpow_neg (x := 2) (by norm_num), div_inv_eq_mul, mul_comm]
  have ht : 0 < ‖x.2.1 0‖ * ‖η' 0‖ := mul_pos (norm_pos_iff.2 ha) (norm_pos_iff.2 hη)
  have hct : ‖x.2.1 0‖ * ‖η' 0‖ ≤ ‖c‖ := by
    rw [← norm_mul, ← hc0]; exact norm_le_pi_norm c 0
  have e1 : (1 + ‖c‖) ^ (-(δ / 4) / 2) ≤ (1 + ‖x.2.1 0‖ * ‖η' 0‖) ^ (-(δ / 4) / 2) :=
    Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith) (by linarith)
  have e2 : (1 + ‖x.2.1 0‖ * ‖η' 0‖) ^ (-(δ / 4) / 2) ≤ (1 + ‖x.2.1 0‖ * ‖η' 0‖) ^ (-γ) :=
    Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
  have e3 : (1 + ‖x.2.1 0‖ * ‖η' 0‖) ^ (-γ) ≤ (‖x.2.1 0‖ * ‖η' 0‖) ^ (-γ) :=
    Real.rpow_le_rpow_of_nonpos ht (by linarith) (by linarith)
  have e4 : (‖x.2.1 0‖ * ‖η' 0‖) ^ (-γ) = ‖η' 0‖ ^ (-γ) * ‖x.2.1 0‖ ^ (-γ) := by
    rw [Real.mul_rpow (norm_nonneg _) (norm_nonneg _), mul_comm]
  have e5 : CS * (1 + ‖c‖) ^ (-(δ / 4) / 2) ≤ (|CS| + 1) * (‖x.2.1 0‖ * ‖η' 0‖) ^ (-γ) :=
    calc CS * (1 + ‖c‖) ^ (-(δ / 4) / 2) ≤ (|CS| + 1) * (1 + ‖c‖) ^ (-(δ / 4) / 2) :=
          mul_le_mul_of_nonneg_right (by linarith [le_abs_self CS]) (by positivity)
      _ ≤ (|CS| + 1) * (‖x.2.1 0‖ * ‖η' 0‖) ^ (-γ) :=
          mul_le_mul_of_nonneg_left (e1.trans (e2.trans e3)) (by positivity)
  calc ∫⁻ τ in Icc (1 : ℝ) 2, ENNReal.ofReal ((1 + ‖linF η η' ζ (scl τ x)‖) ^ (-δ / 4))
      ≤ ∫⁻ τ in Icc (1 : ℝ) 2, ENNReal.ofReal (2 ^ (δ / 4)) *
          ENNReal.ofReal ((1 + ‖c 0 + c 1 * τ + c 2 * (τ : ℂ) ^ 2‖) ^ (-(δ / 4))) :=
        setLIntegral_mono' measurableSet_Icc hpt
    _ = ENNReal.ofReal (2 ^ (δ / 4)) * ∫⁻ τ in Icc (1 : ℝ) 2,
          ENNReal.ofReal ((1 + ‖c 0 + c 1 * τ + c 2 * (τ : ℂ) ^ 2‖) ^ (-(δ / 4))) :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal (2 ^ (δ / 4)) * ENNReal.ofReal (CS * (1 + ‖c‖) ^ (-(δ / 4) / 2)) := by
        gcongr; exact hCS c
    _ = ENNReal.ofReal (2 ^ (δ / 4) * (CS * (1 + ‖c‖) ^ (-(δ / 4) / 2))) :=
        (ENNReal.ofReal_mul (by positivity)).symm
    _ ≤ ENNReal.ofReal (2 ^ (δ / 4) * (|CS| + 1) * ‖η' 0‖ ^ (-γ) * ‖x.2.1 0‖ ^ (-γ)) := by
        apply ENNReal.ofReal_le_ofReal
        calc 2 ^ (δ / 4) * (CS * (1 + ‖c‖) ^ (-(δ / 4) / 2))
            ≤ 2 ^ (δ / 4) * ((|CS| + 1) * (‖x.2.1 0‖ * ‖η' 0‖) ^ (-γ)) :=
              mul_le_mul_of_nonneg_left e5 (by positivity)
          _ = 2 ^ (δ / 4) * (|CS| + 1) * ‖η' 0‖ ^ (-γ) * ‖x.2.1 0‖ ^ (-γ) := by rw [e4]; ring
    _ = ENNReal.ofReal (2 ^ (δ / 4) * (|CS| + 1)) * (‖η' 0‖₊ : ℝ≥0∞) ^ (-γ) *
          (‖x.2.1 0‖₊ : ℝ≥0∞) ^ (-γ) := by
        rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
          ← ENNReal.ofReal_rpow_of_pos (norm_pos_iff.2 hη),
          ← ENNReal.ofReal_rpow_of_pos (norm_pos_iff.2 ha), enn_norm, enn_norm]
end ReciprocityTheory.ChartRestriction.DS.Xi.OSAux
