-- Prove2me | solution 1 for SongZhangKLS.theorem_6_1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-24T08:35:54.850295+00:00
-- url     : https://prove2.me/submissions/d4919663-d6e7-490e-a6c1-41cf7c1f32da
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_KLSModular_FunctionalInequalities_Probability_LogConcave
import Definitions.Def_KLSModular_FunctionalInequalities_KLS_Isotropic
import Definitions.Def_SongZhangKLS_poincareConst
import Definitions.Def_SongZhangKLS_cheegerPsi
import Theorems.Thm_SongZhangKLS_poincare_L2_universal
import Theorems.Thm_SongZhangKLS_cheeger_universal

open MeasureTheory ProbabilityTheory
open scoped ENNReal

theorem solution :
    ∃ C C' : ℝ, 0 < C ∧ 0 < C' ∧ ∀ n : ℕ, 1 ≤ n →
      (∀ μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin n)),
        FunctionalInequalities.KLS.LogConcave μ → FunctionalInequalities.KLS.Isotropic μ →
          SongZhangKLS.poincareConst (μ : Measure (EuclideanSpace ℝ (Fin n))) ≤ ENNReal.ofReal C ∧
          ∀ f : EuclideanSpace ℝ (Fin n) → ℝ, LocallyLipschitz f →
            SongZhangKLS.dirichletEnergy (μ : Measure (EuclideanSpace ℝ (Fin n))) f < ⊤ →
              MemLp f 2 (μ : Measure (EuclideanSpace ℝ (Fin n))) ∧
              evariance f (μ : Measure (EuclideanSpace ℝ (Fin n))) ≤
                ENNReal.ofReal C * SongZhangKLS.dirichletEnergy (μ : Measure (EuclideanSpace ℝ (Fin n))) f) ∧
      SongZhangKLS.psiN n ≤ ENNReal.ofReal C' := by
  obtain ⟨C, hC, hA⟩ := SongZhangKLS.poincare_L2_universal
  obtain ⟨C', hC', hB⟩ := SongZhangKLS.cheeger_universal
  refine ⟨C, C', hC, hC', fun n _ => ⟨fun μ hlc hiso => ⟨?_, hA n μ hlc hiso⟩, ?_⟩⟩
  · unfold SongZhangKLS.poincareConst
    refine iInf₂_le_of_le (Real.toNNReal C) ?_ ?_
    · intro f hf hE
      have := hA n μ hlc hiso f hf hE
      refine ⟨this.1, ?_⟩
      simpa [ENNReal.ofReal] using this.2
    · simp [ENNReal.ofReal]
  · unfold SongZhangKLS.psiN
    exact iSup₂_le fun μ hμ => hB n μ hμ.1 hμ.2
