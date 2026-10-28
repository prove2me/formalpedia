-- Prove2me | solution 2 for XuMannorRobust.Lasso.example6_lasso_robust
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-27T14:24:22.09483+00:00
-- url     : https://prove2.me/submissions/c405eca8-5402-4faf-9253-6e0955cefd6a

import Mathlib
import Definitions.Def_XuMannorRobust_Lasso_IsRobustOn
import Definitions.Def_XuMannorRobust_Lasso_LassoLoss
import Definitions.Def_XuMannorRobust_Lasso_LassoFormulation
import Theorems.Thm_XuMannorRobust_Lasso_theorem6_covering_robust
import Theorems.Thm_XuMannorRobust_Lasso_lemma3_lasso_loss_lipschitz

-- carved verbatim out of submission 59271778-4e98-431c-8703-11cbfcf2d645, lines 108-128

section
open XuMannorRobust.Lasso

theorem solution {m n : ℕ} (Z : Set (ℝ × (Fin m → ℝ))) (hZ : IsCompact Z)
    (c : ℝ) (hc : 0 < c) (A : (Fin n → ℝ × (Fin m → ℝ)) → (Fin m → ℝ))
    (hA : ∀ s, IsLassoSolution c s (A s)) (γ : ℝ) (hγ : 0 < γ) :
    IsRobustOn Z lassoLoss A (Metric.coveringNumber (Real.toNNReal (γ / 2)) Z).toNat
      (fun s => (meanSqResponse s / c + 1) * γ) := by
  apply XuMannorRobust.Lasso.theorem6_covering_robust Z lassoLoss A _ γ hγ
  · intro s hs j z hz hd
    have hloss := XuMannorRobust.Lasso.lemma3_lasso_loss_lipschitz c hc s (A s) (hA s) (s j) z
    have he : (1 / ((n : ℝ) * c)) * ∑ i, (s i).1 ^ 2 + 1 = meanSqResponse s / c + 1 := by
      unfold meanSqResponse
      simp [div_eq_mul_inv]
      <;> ring
    rw [he] at hloss
    have hcoef : 0 ≤ meanSqResponse s / c + 1 := by
      unfold meanSqResponse
      positivity
    exact hloss.trans (mul_le_mul_of_nonneg_left (by simpa [dist_eq_norm] using hd) hcoef)
  · have hrad : Real.toNNReal (γ / 2) ≠ 0 := ne_of_gt (Real.toNNReal_pos.mpr (by linarith))
    obtain ⟨N, hNZ, hNfin, hcov⟩ := Metric.exists_finite_isCover_of_isCompact hrad hZ
    exact lt_of_le_of_lt (Metric.IsCover.coveringNumber_le_encard hNZ hcov) hNfin.encard_lt_top

end
