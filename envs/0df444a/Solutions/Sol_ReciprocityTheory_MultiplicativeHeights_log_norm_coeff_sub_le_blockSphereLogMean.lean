-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.log_norm_coeff_sub_le_blockSphereLogMean
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T16:02:06.855135+00:00
-- url     : https://prove2.me/submissions/758cf6f7-0a34-460f-b203-67ae2c857b86

import Definitions.Def_ReciprocityTheory_SemistableReduction_RestBlockSubstIsMultiHomogeneous
import Definitions.Def_ReciprocityTheory_SemistableReduction_LogNormCoeffSubLeBlockSphereLogMean
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_harmonic_pred_le_one_add_log
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_blockSphere_logMean_bound
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_eval_mul_of_isMultiHomogeneous
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_exists_torus_coeff_le


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights
open MeasureTheory MvPolynomial NumberField
namespace ReciprocityTheory.MultiplicativeHeights
theorem _root_.solution (hSJ : SJStatement) (hInt : SphereLogIntegrableStatement) {B n : ℕ}
    (hn : 0 < n) {a : Fin B → ℕ} {g : MvPolynomial (Fin B × Fin n) ℂ}
    (hg : IsMultiHomogeneous a g) (s : Fin B × Fin n →₀ ℕ) (hs : g.coeff s ≠ 0) :
    Real.log ‖g.coeff s‖ - ∑ b, (a b : ℝ) * (Real.log n + 1 / 2) ≤ blockSphereMean B n g := by
  obtain ⟨z, hz1, hzc⟩ := exists_torus_coeff_le g s
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  set r : ℝ := Real.sqrt n with hrdef
  have hr : 0 < r := Real.sqrt_pos.mpr hnpos
  have hr2 : r ^ 2 = n := Real.sq_sqrt hnpos.le

  have hmem : ∀ b : Fin B, (WithLp.toLp 2 (fun j => z (b, j) / (r : ℂ)) : EuclideanSpace ℂ (Fin n)) ∈
      Metric.sphere (0 : EuclideanSpace ℂ (Fin n)) 1 := by
    intro b
    have hj : ∀ j, ‖z (b, j) / (r : ℂ)‖ = 1 / r := by
      intro j
      rw [norm_div, hz1, Complex.norm_of_nonneg hr.le]
    rw [mem_sphere_zero_iff_norm, EuclideanSpace.norm_eq]
    simp only [PiLp.toLp_apply, hj, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [div_pow, one_pow, hr2, mul_one_div_cancel hnpos.ne', Real.sqrt_one]
  let u : BlockSphere B n := fun b => ⟨WithLp.toLp 2 (fun j => z (b, j) / (r : ℂ)), hmem b⟩
  have hrC : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  have hz' : (fun p => (r : ℂ) * blockPoint u p) = z := by
    funext p
    simp only [blockPoint, spherePoint, u, PiLp.toLp_apply]
    field_simp
  have hev := eval_mul_of_isMultiHomogeneous hg (r : ℂ) (blockPoint u)
  rw [hz'] at hev
  have hcpos : 0 < ‖g.coeff s‖ := norm_pos_iff.mpr hs
  have hgz : 0 < ‖eval z g‖ := lt_of_lt_of_le hcpos hzc
  have hnorm : ‖eval z g‖ = r ^ (∑ b, a b) * ‖eval (blockPoint u) g‖ := by
    rw [hev, norm_mul, norm_pow, Complex.norm_of_nonneg hr.le]
  have hgu : eval (blockPoint u) g ≠ 0 := by
    intro h0
    rw [hnorm, h0, norm_zero, mul_zero] at hgz
    exact lt_irrefl _ hgz
  have hbb := blockSphere_logMean_bound hSJ hInt hn B a g u hg hgu
  have hH := harmonic_pred_le_one_add_log hn
  have hlogr : Real.log r = Real.log n / 2 := Real.log_sqrt hnpos.le
  have hlz : Real.log ‖eval z g‖ =
      ((∑ b, a b : ℕ) : ℝ) * Real.log r + Real.log ‖eval (blockPoint u) g‖ := by
    rw [hnorm, Real.log_mul (by positivity) (norm_ne_zero_iff.mpr hgu), Real.log_pow]
  have hlc : Real.log ‖g.coeff s‖ ≤ Real.log ‖eval z g‖ := Real.log_le_log hcpos hzc
  set A : ℝ := ∑ b, (a b : ℝ) with hAdef
  have hsum : ((∑ b, a b : ℕ) : ℝ) = A := by rw [hAdef]; push_cast; rfl
  have hA0 : 0 ≤ A := Finset.sum_nonneg (fun b _ => Nat.cast_nonneg _)
  have hmul : A / 2 * (harmonic (n - 1) : ℝ) ≤ A / 2 * (1 + Real.log n) :=
    mul_le_mul_of_nonneg_left hH (by positivity)
  have hgoal : ∑ b, (a b : ℝ) * (Real.log n + 1 / 2) = A * (Real.log n + 1 / 2) := by
    rw [hAdef, Finset.sum_mul]
  rw [hgoal]
  rw [hsum, hlogr] at hlz
  nlinarith
end ReciprocityTheory.MultiplicativeHeights
