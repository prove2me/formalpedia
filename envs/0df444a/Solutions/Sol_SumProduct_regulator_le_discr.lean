-- Prove2me | solution 1 for SumProduct.regulator_le_discr
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T02:25:09.23483+00:00
-- url     : https://prove2.me/submissions/3f2113b3-a2ab-4889-bae1-9744aaf3a8bf

import Definitions.Def_SumProduct_PartialZetaMellin
import Definitions.Def_SumProduct_MultiplicativeCount
import Definitions.Def_SumProduct_EulerBound
import Definitions.Def_SumProduct_RegulatorBound
import Theorems.Thm_SumProduct_dedekind_residue_le
import Theorems.Thm_SumProduct_torsionOrder_eq_two_of_totallyReal

section
open scoped NumberField
open Pointwise
namespace SumProduct
private lemma four_le_pi_pow {d : ℕ} (hd : 2 ≤ d) : (4 : ℝ) ≤ Real.pi ^ d :=
  calc (4 : ℝ) ≤ Real.pi ^ 2 := by nlinarith [Real.pi_gt_three]
    _ ≤ Real.pi ^ d := pow_le_pow_right₀ (by linarith [Real.pi_gt_three]) hd
end SumProduct
end

set_option autoImplicit true
open scoped NumberField
open Pointwise
open SumProduct
open scoped Classical
open NumberField NumberField.Units NumberField.InfinitePlace
namespace SumProduct
theorem _root_.solution (K : Type*) [Field K] [NumberField K] [NumberField.IsTotallyReal K]
    (hd : 2 ≤ Module.finrank ℚ K) :
    NumberField.Units.regulator K ≤ |(NumberField.discr K : ℝ)| := by
  set d := Module.finrank ℚ K with hddef
  set Δ : ℝ := |(NumberField.discr K : ℝ)| with hΔdef
  have hd1 : 1 < d := hd
  set m : ℕ := d - 1 with hmdef
  have hΔ2 : (2 : ℝ) < Δ := by rw [hΔdef]; exact_mod_cast abs_discr_gt_two hd1
  have hΔ0 : (0 : ℝ) < Δ := by linarith
  have hRpos : 0 < regulator K := regulator_pos K
  have hsqΔ : 0 < Real.sqrt Δ := Real.sqrt_pos.mpr hΔ0
  have h2pos : (0 : ℝ) < 2 ^ m := by positivity
  have hh1 : (1 : ℝ) ≤ (classNumber K : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (classNumber_ne_zero K)
  -- Analytic class number formula specialised to totally real K: κ = 2^{d-1} R h / √Δ.
  have hnrc : nrComplexPlaces K = 0 := IsTotallyReal.nrComplexPlaces_eq_zero (K := K)
  have hnrr : nrRealPlaces K = d := by
    have h := card_add_two_mul_card_eq_rank K
    rw [hnrc] at h; omega
  have htor : torsionOrder K = 2 := torsionOrder_eq_two_of_totallyReal
  have h2d : (2 : ℝ) ^ d = 2 ^ m * 2 := by rw [show d = m + 1 by omega, pow_succ]
  have hACNF : dedekindZeta_residue K
      = 2 ^ m * regulator K * (classNumber K : ℝ) / Real.sqrt Δ := by
    rw [dedekindZeta_residue_def, hnrc, hnrr, htor, pow_zero, mul_one, ← hΔdef, h2d]
    field_simp
    ring
  -- The functional-equation residue bound at s = 2.
  have hres := dedekind_residue_le K hd
  rw [← hddef, ← hΔdef, hACNF] at hres
  -- 2^m R h / √Δ ≤ 2 (2/π)^d √Δ ⟹ 2^m R h ≤ 2 (2/π)^d Δ
  have hstep : 2 ^ m * regulator K * (classNumber K : ℝ) ≤ 2 * (2 / Real.pi) ^ d * Δ := by
    have h2 := (div_le_iff₀ hsqΔ).mp hres
    calc 2 ^ m * regulator K * (classNumber K : ℝ)
        ≤ 2 * (2 / Real.pi) ^ d * Real.sqrt Δ * Real.sqrt Δ := h2
      _ = 2 * (2 / Real.pi) ^ d * Δ := by rw [mul_assoc, Real.mul_self_sqrt hΔ0.le]
  -- 2 (2/π)^d ≤ 2^{d-1}  (⟺ 4 ≤ π^d).
  have hnum : 2 * (2 / Real.pi) ^ d ≤ (2 : ℝ) ^ m := by
    have hpd : (0 : ℝ) < Real.pi ^ d := by positivity
    rw [div_pow, ← mul_div_assoc, div_le_iff₀ hpd]
    have hpow : (2 : ℝ) * 2 ^ d = 2 ^ m * 4 := by rw [show d = m + 1 by omega, pow_succ]; ring
    rw [hpow]
    exact mul_le_mul_of_nonneg_left (four_le_pi_pow hd) h2pos.le
  -- Combine and cancel.
  have hfin : 2 ^ m * regulator K * (classNumber K : ℝ) ≤ 2 ^ m * Δ :=
    hstep.trans (mul_le_mul_of_nonneg_right hnum hΔ0.le)
  have hRh : regulator K * (classNumber K : ℝ) ≤ Δ :=
    le_of_mul_le_mul_left (by rw [← mul_assoc]; exact hfin) h2pos
  calc regulator K = regulator K * 1 := (mul_one _).symm
    _ ≤ regulator K * (classNumber K : ℝ) := mul_le_mul_of_nonneg_left hh1 hRpos.le
    _ ≤ Δ := hRh
end SumProduct
