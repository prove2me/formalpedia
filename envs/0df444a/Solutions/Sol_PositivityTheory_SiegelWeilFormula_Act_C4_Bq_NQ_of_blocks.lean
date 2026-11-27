-- Prove2me | solution 1 for PositivityTheory.SiegelWeilFormula.Act.C4.Bq.NQ.of_blocks
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T05:21:04.634811+00:00
-- url     : https://prove2.me/submissions/d6690ee4-1d33-4a2f-9ccd-992256d08946

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_SiegelWeilFormula_ParabolicBlockForms_UpperBlockRankOneUpdate

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PositivityTheory PositivityTheory.SiegelWeilFormula PositivityTheory.SiegelWeilFormula.Act PositivityTheory.SiegelWeilFormula.Act.C4 PositivityTheory.SiegelWeilFormula.Act.C4.Bq
open Matrix
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
variable {ι R : Type} [Fintype ι] [DecidableEq ι] [CommRing R]
variable {n : ℕ}
namespace PositivityTheory.SiegelWeilFormula.Act.C4.Bq
namespace NQ
theorem _root_.solution {i₀ : Fin n} {A B D : Matrix (Fin n) (Fin n) R}
    (hA0 : ∀ a, (A - 1) a i₀ = 0) (hA : ∀ a k, a ≠ i₀ → (A - 1) a k = 0)
    (hB : ∀ a k, a ≠ i₀ → k ≠ i₀ → B a k = 0) (hD : ∀ a k, k ≠ i₀ → (D - 1) a k = 0) :
    NQ (Sum.inl i₀) (Sum.inr i₀) (Matrix.fromBlocks A B 0 D) := by
  refine ⟨fun k => ?_, fun k l hlx hly hkx => ?_⟩
  · rcases k with a | a
    · have := hA0 a
      simpa [Matrix.sub_apply, Matrix.one_apply] using this
    · simp [Matrix.sub_apply, Matrix.one_apply]
  · rcases l with l | l <;> rcases k with k | k
    · have hk : k ≠ i₀ := fun h => hkx (by rw [h])
      have := hA k l hk
      simpa [Matrix.sub_apply, Matrix.one_apply] using this
    · simp [Matrix.sub_apply, Matrix.one_apply]
    · have hk : k ≠ i₀ := fun h => hkx (by rw [h])
      have hl : l ≠ i₀ := fun h => hly (by rw [h])
      simp [Matrix.sub_apply, Matrix.one_apply, hB k l hk hl]
    · have hl : l ≠ i₀ := fun h => hly (by rw [h])
      have := hD k l hl
      simpa [Matrix.sub_apply, Matrix.one_apply] using this
end NQ
end PositivityTheory.SiegelWeilFormula.Act.C4.Bq
