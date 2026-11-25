-- Prove2me | solution 1 for PI.ET.kyFan_diag
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T09:49:19.253285+00:00
-- url     : https://prove2.me/submissions/cd9372c0-9ec0-4dd7-ace8-0a184f590156

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExponentialTriangular_SortedSpec
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExponentialTriangular_ProdLeOfInjective
import Theorems.Thm_PI_ET_factorial_mul_det
import Theorems.Thm_PI_ET_prod_le_of_injective

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
noncomputable section
open PI PI.ET
namespace PI.ET
theorem _root_.solution {n k : ℕ} (hk : k ≤ n) (p : Fin n → ℝ) (hp : Antitone p)
    (hpos : ∀ i, 0 < p i) (V : Matrix (Fin n) (Fin k) ℂ) (hV : Vᴴ * V = 1) :
    ‖(Vᴴ * diagonal (fun i => (p i : ℂ)) * V).det‖ ≤ ∏ i : Fin k, p (Fin.castLE hk i) := by
  have hT := factorial_mul_det k n (fun i => (p i : ℂ)) V
  have hU := factorial_mul_det k n (fun _ => (1 : ℂ)) V
  rw [diagonal_one, Matrix.mul_one, hV, det_one, mul_one] at hU
  simp only [Finset.prod_const_one, one_mul] at hU
  have hsq : ∀ f : Fin k → Fin n, (V.submatrix f id).det * star (V.submatrix f id).det =
      ((‖(V.submatrix f id).det‖ ^ 2 : ℝ) : ℂ) := by
    intro f
    rw [Complex.star_def, Complex.mul_conj']
    push_cast
    rfl
  simp_rw [hsq] at hU
  have hU' : (k.factorial : ℝ) = ∑ f : Fin k → Fin n, ‖(V.submatrix f id).det‖ ^ 2 := by
    exact_mod_cast hU
  set P := ∏ i : Fin k, p (Fin.castLE hk i)
  have hterm : ∀ f : Fin k → Fin n,
      ‖(∏ i, ((p (f i) : ℝ) : ℂ)) * ((V.submatrix f id).det * star (V.submatrix f id).det)‖ ≤
        P * ‖(V.submatrix f id).det‖ ^ 2 := by
    intro f
    rw [hsq, norm_mul, Complex.norm_real, Real.norm_of_nonneg (sq_nonneg _), norm_prod]
    simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (hpos _)]
    by_cases hf : Function.Injective f
    · exact mul_le_mul_of_nonneg_right (prod_le_of_injective hk p hp (fun i => (hpos i).le) f hf)
        (sq_nonneg _)
    · obtain ⟨i, j, hij, hne⟩ : ∃ i j, f i = f j ∧ i ≠ j := by
        by_contra hc
        exact hf fun i j h => by_contra fun hne => hc ⟨i, j, h, hne⟩
      have h0 : (V.submatrix f id).det = 0 := det_zero_of_row_eq hne (by ext c; simp [hij])
      simp [h0]
  have hfact : (0 : ℝ) < k.factorial := by exact_mod_cast Nat.factorial_pos k
  have hmain : (k.factorial : ℝ) * ‖(Vᴴ * diagonal (fun i => (p i : ℂ)) * V).det‖ ≤ P * k.factorial := by
    calc (k.factorial : ℝ) * ‖(Vᴴ * diagonal (fun i => (p i : ℂ)) * V).det‖
        = ‖(k.factorial : ℂ) * (Vᴴ * diagonal (fun i => (p i : ℂ)) * V).det‖ := by
          rw [norm_mul, Complex.norm_natCast]
      _ = ‖∑ f : Fin k → Fin n, (∏ i, ((p (f i) : ℝ) : ℂ)) *
          ((V.submatrix f id).det * star (V.submatrix f id).det)‖ := by rw [hT]
      _ ≤ ∑ f : Fin k → Fin n, ‖(∏ i, ((p (f i) : ℝ) : ℂ)) *
          ((V.submatrix f id).det * star (V.submatrix f id).det)‖ := norm_sum_le _ _
      _ ≤ ∑ f : Fin k → Fin n, P * ‖(V.submatrix f id).det‖ ^ 2 := Finset.sum_le_sum fun f _ => hterm f
      _ = P * k.factorial := by rw [← Finset.mul_sum, hU']
  nlinarith [norm_nonneg (Vᴴ * diagonal (fun i => (p i : ℂ)) * V).det]
end PI.ET
