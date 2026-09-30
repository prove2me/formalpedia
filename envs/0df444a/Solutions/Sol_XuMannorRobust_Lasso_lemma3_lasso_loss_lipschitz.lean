-- Prove2me | solution 1 for XuMannorRobust.Lasso.lemma3_lasso_loss_lipschitz
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T06:40:17.353772+00:00
-- url     : https://prove2.me/submissions/3315f467-8412-4a94-817c-ace169a79186

import Mathlib
import Definitions.Def_XuMannorRobust_Lasso_LassoLoss
import Definitions.Def_XuMannorRobust_Lasso_LassoFormulation
open XuMannorRobust.Lasso

private theorem lasso_bound {m n : ℕ} (c : ℝ) (hc : 0 < c)
    (s : Fin n → ℝ × (Fin m → ℝ)) (w : Fin m → ℝ) (hw : IsLassoSolution c s w) :
    lassoObjective c s w ≤ lassoObjective c s 0 ∧
    lassoObjective c s 0 = (1 / (n : ℝ)) * ∑ i, (s i).1 ^ 2 ∧
    l1norm w ≤ (1 / ((n : ℝ) * c)) * ∑ i, (s i).1 ^ 2 := by
  have hzero : lassoObjective c s 0 = (1 / (n : ℝ)) * ∑ i, (s i).1 ^ 2 := by
    simp [lassoObjective, l1norm]
  refine ⟨hw 0, hzero, ?_⟩
  have hnonneg : 0 ≤ (1 / (n : ℝ)) * ∑ i, ((s i).1 - dotProduct w (s i).2) ^ 2 := by
    positivity
  have hbound : c * l1norm w ≤ (1 / (n : ℝ)) * ∑ i, (s i).1 ^ 2 := by
    have := hw 0
    rw [hzero] at this
    unfold lassoObjective at this
    linarith
  calc
    l1norm w ≤ ((1 / (n : ℝ)) * ∑ i, (s i).1 ^ 2) / c :=
      (le_div_iff₀ hc).mpr (by simpa [mul_comm] using hbound)
    _ = (1 / ((n : ℝ) * c)) * ∑ i, (s i).1 ^ 2 := by simp [div_eq_mul_inv]; ring

theorem solution {m n : ℕ} (c : ℝ) (hc : 0 < c)
    (s : Fin n → ℝ × (Fin m → ℝ)) (w : Fin m → ℝ) (hw : IsLassoSolution c s w)
    (za zb : ℝ × (Fin m → ℝ)) :
    |lassoLoss w za - lassoLoss w zb| ≤
      ((1 / ((n : ℝ) * c)) * ∑ i, (s i).1 ^ 2 + 1) * ‖za - zb‖ := by
  have hcoord (i : Fin m) : |za.2 i - zb.2 i| ≤ ‖za - zb‖ := by
    simpa only [Real.norm_eq_abs, Pi.sub_apply, Prod.snd_sub] using
      (norm_le_pi_norm ((za - zb).2) i).trans (norm_snd_le (za - zb))
  have hresp : |za.1 - zb.1| ≤ ‖za - zb‖ := by
    simpa only [Real.norm_eq_abs, Prod.fst_sub] using norm_fst_le (za - zb)
  have hdot : |dotProduct w (za.2 - zb.2)| ≤ l1norm w * ‖za - zb‖ := by
    calc
      |dotProduct w (za.2 - zb.2)| ≤ ∑ i, |w i * (za.2 i - zb.2 i)| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i, |w i| * ‖za - zb‖ := by
        apply Finset.sum_le_sum
        intro i _
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left (hcoord i) (abs_nonneg _)
      _ = l1norm w * ‖za - zb‖ := by rw [← Finset.sum_mul]; rfl
  have hb := (lasso_bound c hc s w hw).2.2
  calc
    |lassoLoss w za - lassoLoss w zb| ≤
        |(za.1 - dotProduct w za.2) - (zb.1 - dotProduct w zb.2)| :=
      abs_abs_sub_abs_le_abs_sub _ _
    _ = |(za.1 - zb.1) - dotProduct w (za.2 - zb.2)| := by
      rw [dotProduct_sub]
      congr 1
      ring
    _ ≤ |za.1 - zb.1| + |dotProduct w (za.2 - zb.2)| := abs_sub _ _
    _ ≤ ‖za - zb‖ + l1norm w * ‖za - zb‖ := add_le_add hresp hdot
    _ ≤ ‖za - zb‖ + ((1 / ((n : ℝ) * c)) * ∑ i, (s i).1 ^ 2) * ‖za - zb‖ :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_right hb (norm_nonneg _))
    _ = _ := by ring
