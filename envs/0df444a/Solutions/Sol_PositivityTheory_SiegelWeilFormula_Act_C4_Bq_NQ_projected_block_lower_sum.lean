-- Prove2me | solution 1 for PositivityTheory.SiegelWeilFormula.Act.C4.Bq.NQ.projected_block_lower_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T05:21:10.154888+00:00
-- url     : https://prove2.me/submissions/2e246479-d46e-4805-9d7e-c2c3af44b04e

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_SiegelWeilFormula_ParabolicBlockForms_UpperBlockRankOneUpdate
import Theorems.Thm_PositivityTheory_SiegelWeilFormula_Act_C4_Bq_NQ_apply

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
theorem _root_.solution {i₀ : Fin n} {M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) R} (hM : NQ (Sum.inl i₀) (Sum.inr i₀) M) :
    M.toBlocks₂₁ = 0 := by
  ext i k
  simp only [Matrix.toBlocks₂₁, Matrix.of_apply, Matrix.zero_apply]
  by_cases hk : k = i₀
  · subst hk; rw [hM.apply (Or.inl rfl)]; simp [Matrix.one_apply]
  · rw [hM.apply (Or.inr ⟨by simp, by simp⟩)]
    simp [Matrix.one_apply]
end NQ
end PositivityTheory.SiegelWeilFormula.Act.C4.Bq
