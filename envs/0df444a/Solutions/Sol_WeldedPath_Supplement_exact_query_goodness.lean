-- Prove2me | solution 1 for WeldedPath.Supplement.exact_query_goodness
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dmilosch
-- created : 2026-11-22T16:10:04.953021+00:00
-- url     : https://prove2.me/submissions/bd361a7c-715b-4f3d-a0f8-33233dda9ebb
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_WeldedPath_Supplement_theorem_4_9
import Theorems.Thm_WeldedPath_Supplement_localized_oracle_comparison

open WeldedPath WeldedPath.Supplement

/-- Ordinary goodness and the boundary-localized correction imply exact goodness.
The two imported analytic theorems are explicit proof-sketch dependencies. -/
theorem solution :
    ∃ C₀ : ℝ, 0 < C₀ ∧ ∃ C : ℝ, 0 < C ∧
      ∀ n l : ℕ, Even n → 16 ≤ n → 2 ≤ l → l ≤ n - 4 →
      ∀ G : WeldedInstance n, G.IsValid →
      ∀ q t : ℕ, t ≤ 6 * q →
      C₀ * ((q : ℝ) + 1) ≤ (2 : ℝ) ^ (n - l) →
      C₀ * (((q : ℝ) + 1) / (2 : ℝ) ^ l +
        ((n : ℝ) + 1) * ((q : ℝ) + 1) ^ 3 / (2 : ℝ) ^ n) ≤ 1 / 2 →
      ‖(1 - projGood l G (t + 6)).comp
        ((exactCpWT l G).comp (projGood l G t))‖ ≤ C * etaStep n l t := by
  obtain ⟨A,hA,C,hC,hordinary⟩ := theorem_4_9
  obtain ⟨B,hB,D,hD,hcomparison⟩ := localized_oracle_comparison
  refine ⟨max A B,lt_of_lt_of_le hA (le_max_left _ _),C+D,add_pos hC hD,?_⟩
  intro n l hn hn16 hl hln G hG q t ht hsize hbudget
  have hq : 0 ≤ (q : ℝ)+1 := by positivity
  have hnonneg : 0 ≤ ((q : ℝ)+1)/(2:ℝ)^l+
      ((n:ℝ)+1)*((q:ℝ)+1)^3/(2:ℝ)^n := by positivity
  have ho := hordinary n l hn hl hln G hG q t ht
    ((mul_le_mul_of_nonneg_right (le_max_left A B) hq).trans hsize)
    ((mul_le_mul_of_nonneg_right (le_max_left A B) hnonneg).trans hbudget)
  have hd := hcomparison n l hn hn16 hl hln G hG q t ht
    ((mul_le_mul_of_nonneg_right (le_max_right A B) hq).trans hsize)
    ((mul_le_mul_of_nonneg_right (le_max_right A B) hnonneg).trans hbudget)
  have hsqrt : Real.sqrt ((n:ℝ)*((t:ℝ)+1)/(2:ℝ)^n) ≤ etaStep n l t := by
    apply Real.sqrt_le_sqrt
    change _ ≤ 1/(2:ℝ)^l+(n:ℝ)*((t:ℝ)+1)/(2:ℝ)^n
    exact le_add_of_nonneg_left (by positivity)
  have he : (1-projGood l G (t+6)).comp ((exactCpWT l G).comp (projGood l G t)) =
      (1-projGood l G (t+6)).comp ((cpWT l G).comp (projGood l G t)) +
      (1-projGood l G (t+6)).comp ((exactCpWT l G-cpWT l G).comp (projGood l G t)) := by
    ext ψ
    simp only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.add_apply,
      ContinuousLinearMap.sub_apply,map_sub]
    abel
  rw [he]
  calc
    _ ≤ ‖(1-projGood l G (t+6)).comp ((cpWT l G).comp (projGood l G t))‖+
        ‖(1-projGood l G (t+6)).comp ((exactCpWT l G-cpWT l G).comp (projGood l G t))‖ := norm_add_le _ _
    _ ≤ C*etaStep n l t+D*Real.sqrt ((n:ℝ)*((t:ℝ)+1)/(2:ℝ)^n) := add_le_add ho hd
    _ ≤ C*etaStep n l t+D*etaStep n l t :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_left hsqrt (le_of_lt hD))
    _ = _ := (add_mul _ _ _).symm


