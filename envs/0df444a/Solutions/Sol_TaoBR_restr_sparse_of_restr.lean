-- Prove2me | solution 1 for TaoBR.restr_sparse_of_restr
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-29T23:11:54.152566+00:00
-- url     : https://prove2.me/submissions/c146c861-871f-4f46-9923-dbb00d8f812d
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_TaoBR
import Theorems.Thm_TaoBR_restr_sparse_of_restr_uniform

open MeasureTheory Metric
open scoped ENNReal NNReal SchwartzMap

open TaoBR in
theorem solution (n : ℕ) (hn : 2 ≤ n) (p : ℝ≥0∞) (hp : 1 < p) (hp2 : p < 2)
    (α : ℝ) (hα : 0 < α) (h : Restr n p α) :
    ∃ C₀ : ℝ, ∃ C : ℝ≥0, ∀ R : ℝ, 1 ≤ R → ∀ (N : ℕ) (x : Fin N → E n), IsSparse C₀ R x →
      ∀ f : 𝓢(E n, ℂ), tsupport f ⊆ ⋃ i, closedBall (x i) R →
        eLpNorm (restriction f) p (sphereMeasure n) ≤
          C * ENNReal.ofReal (R ^ α) * eLpNorm f p volume := by
  obtain ⟨C₀, hC₀⟩ := TaoBR.restr_sparse_of_restr_uniform n hn p hp hp2
  obtain ⟨C, hC⟩ := hC₀ α hα h
  exact ⟨C₀, C, hC⟩
