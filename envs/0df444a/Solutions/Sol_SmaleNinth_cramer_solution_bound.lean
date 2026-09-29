-- Prove2me | solution 1 for SmaleNinth.cramer_solution_bound
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-06T20:47:43.403746+00:00
-- url     : https://prove2.me/submissions/60d376c6-d47e-4baa-a43b-f59e31355934

import Mathlib

open Matrix Finset

namespace CramerAux

theorem det_bound {r : ℕ} (U : ℕ)
    (M : Matrix (Fin r) (Fin r) ℤ) (hM : ∀ i j, |M i j| ≤ (U : ℤ)) :
    |M.det| ≤ (r.factorial : ℤ) * (U : ℤ) ^ r := by
  classical
  rw [Matrix.det_apply]
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  have hterm : ∀ σ : Equiv.Perm (Fin r),
      |(Equiv.Perm.sign σ : ℤ) • ∏ i, M (σ i) i| ≤ (U : ℤ) ^ r := by
    intro σ
    have h1 : |(Equiv.Perm.sign σ : ℤ) • ∏ i, M (σ i) i| = |∏ i, M (σ i) i| := by
      rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;>
        simp [h, abs_neg]
    rw [h1, Finset.abs_prod]
    calc ∏ i, |M (σ i) i| ≤ ∏ _i : Fin r, (U : ℤ) :=
          Finset.prod_le_prod (fun i _ => abs_nonneg _) (fun i _ => hM _ _)
      _ = (U : ℤ) ^ r := by simp
  refine le_trans (Finset.sum_le_sum (fun σ _ => hterm σ)) ?_
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin, nsmul_eq_mul]

end CramerAux

open CramerAux

theorem solution {r : ℕ} (U : ℕ)
    (M : Matrix (Fin r) (Fin r) ℤ) (v : Fin r → ℤ)
    (hM : ∀ i j, |M i j| ≤ (U : ℤ)) (hv : ∀ i, |v i| ≤ (U : ℤ))
    (hdet : M.det ≠ 0)
    (z : Fin r → ℝ)
    (hz : (M.map (Int.cast : ℤ → ℝ)).mulVec z = fun i => ((v i : ℤ) : ℝ)) :
    ∀ j, |z j| ≤ (r.factorial : ℝ) * (U : ℝ) ^ r := by
  classical
  set Mr : Matrix (Fin r) (Fin r) ℝ := M.map (Int.cast : ℤ → ℝ) with hMr
  set vr : Fin r → ℝ := fun i => ((v i : ℤ) : ℝ) with hvr
  have hdetMr : Mr.det = ((M.det : ℤ) : ℝ) := (Int.cast_det M).symm
  have hdetne : Mr.det ≠ 0 := by
    rw [hdetMr]
    exact_mod_cast hdet
  -- Cramer: `Mr.det • z = Mr.cramer vr`
  have hkey : Mr.det • z = Mr.cramer vr := by
    have h1 : Mr.mulVec (Mr.cramer vr) = Mr.det • vr := Matrix.mulVec_cramer Mr vr
    have h2 : Mr.mulVec (Mr.det • z) = Mr.det • vr := by
      rw [Matrix.mulVec_smul, hz]
    have hunit : IsUnit Mr := (Matrix.isUnit_iff_isUnit_det Mr).2 (isUnit_iff_ne_zero.2 hdetne)
    have hinj : Function.Injective Mr.mulVec := Matrix.mulVec_injective_of_isUnit hunit
    exact hinj (h2.trans h1.symm)
  intro j
  have hcol : Mr.cramer vr j = (((M.updateCol j v).det : ℤ) : ℝ) := by
    rw [Matrix.cramer_apply]
    have : Mr.updateCol j vr = (M.updateCol j v).map (Int.cast : ℤ → ℝ) := by
      ext a c
      by_cases hc : c = j <;> simp [Matrix.updateCol_apply, hc, hMr, hvr]
    rw [this]
    exact (Int.cast_det _).symm
  have hzj : ((M.det : ℤ) : ℝ) * z j = (((M.updateCol j v).det : ℤ) : ℝ) := by
    have := congrFun hkey j
    simpa [hdetMr, hcol] using this
  have hnum : |(M.updateCol j v).det| ≤ (r.factorial : ℤ) * (U : ℤ) ^ r := by
    refine det_bound U _ fun a c => ?_
    by_cases hc : c = j <;> simp [Matrix.updateCol_apply, hc, hv a, hM a c]
  have hden : (1 : ℝ) ≤ |((M.det : ℤ) : ℝ)| := by
    have : (1 : ℤ) ≤ |M.det| := Int.one_le_abs (by exact_mod_cast hdet)
    exact_mod_cast this
  have habs : |((M.det : ℤ) : ℝ)| * |z j| ≤ (r.factorial : ℝ) * (U : ℝ) ^ r := by
    rw [← abs_mul, hzj]
    have hcast : |(((M.updateCol j v).det : ℤ) : ℝ)|
        ≤ (((r.factorial : ℤ) * (U : ℤ) ^ r : ℤ) : ℝ) := by
      rw [← Int.cast_abs]
      exact_mod_cast hnum
    simpa using hcast
  calc |z j| = 1 * |z j| := (one_mul _).symm
    _ ≤ |((M.det : ℤ) : ℝ)| * |z j| := mul_le_mul_of_nonneg_right hden (abs_nonneg _)
    _ ≤ (r.factorial : ℝ) * (U : ℝ) ^ r := habs
