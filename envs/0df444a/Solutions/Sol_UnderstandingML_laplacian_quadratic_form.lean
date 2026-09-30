-- Prove2me | solution 1 for UnderstandingML.laplacian_quadratic_form
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-26T10:56:31.032773+00:00
-- url     : https://prove2.me/submissions/915bcc0f-cea3-4864-b8ee-6df599ddeb35

import Mathlib
import Definitions.Def_UnderstandingML_Clustering

set_option autoImplicit false

open MeasureTheory

open MeasureTheory UnderstandingML in
theorem solution {m : ℕ} (W : Matrix (Fin m) (Fin m) ℝ) (hW : W.IsSymm)
    (v : Fin m → ℝ) :
    dotProduct v ((laplacian W).mulVec v) = 1 / 2 * ∑ r, ∑ s, W r s * (v r - v s) ^ 2 := by
  have hsym : ∀ r s, W s r = W r s := fun r s => hW.apply r s
  have h1 : ∑ r, ∑ s, W r s * v s ^ 2 = ∑ r, ∑ s, W r s * v r ^ 2 := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun r _ => Finset.sum_congr rfl (fun s _ => ?_))
    rw [hsym]
  have h2 : ∑ r, ∑ s, W r s * (v r - v s) ^ 2 =
      ∑ r, ∑ s, W r s * v r ^ 2 + ∑ r, ∑ s, W r s * v s ^ 2
        - 2 * ∑ r, ∑ s, W r s * v r * v s := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun r _ => ?_)
    rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun s _ => ?_)
    ring
  have e : ∀ r, (laplacian W).mulVec v r = (∑ s, W r s) * v r - ∑ s, W r s * v s := by
    intro r
    simp only [laplacian, degreeMatrix, Matrix.sub_mulVec, Pi.sub_apply, Matrix.mulVec_diagonal]
    rfl
  have h3 : dotProduct v ((laplacian W).mulVec v) =
      ∑ r, ∑ s, W r s * v r ^ 2 - ∑ r, ∑ s, W r s * v r * v s := by
    simp only [dotProduct, e]
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun r _ => ?_)
    rw [Finset.sum_mul, mul_sub, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib,
      ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun s _ => ?_)
    ring
  rw [h3, h2, h1]
  ring
